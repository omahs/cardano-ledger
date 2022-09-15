{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Data.Coders provides tools for writing 'ToCBOR' and 'FromVCBOR' instances (see module 'Cardano.Binary')
--   in an intuitive way that mirrors the way one constructs values of a particular type. Advantages include:
--
-- 1. Book-keeping details neccesary to write correct instances are hidden from the user.
-- 2. Inverse 'ToCBOR' and 'FromVCBOR' instances have visually similar definitions.
-- 3. Advanced instances involving sparse-encoding, compact-representation, and 'Annotator' instances are also supported.
--
-- A Guide to Visual inspection of Duality in Encode and Decode
--
-- 1. @(Sum c)@     and @(SumD c)@    are duals
-- 2. @(Rec c)@     and @(RecD c)@    are duals
-- 3. @(Keyed c)@   and @(KeyedD c)@  are duals
-- 4. @(OmitC x)@   and @(Emit x)@    are duals
-- 5. @(Omit p ..)@ and @(Emit x)@    are duals if (p x) is True
-- 6. @(To x)@      and @(From)@      are duals if (x::T) and (forall (y::T). isRight (roundTrip y))
-- 7. @(E enc x)@   and @(D dec)@     are duals if (forall x . isRight (roundTrip' enc dec x))
-- 6. @(ED d x)@    and @(DD f)@      are duals as long as d=(Dual enc dec) and (forall x . isRight (roundTrip' enc dec x))
-- 7. @(f !> x)@    and @(g <! y)@    are duals if (f and g are duals) and (x and y are duals)
--
-- Duality properties of @(Summands name decodeT)@ and @(SparseKeyed name (init::T) pick required)@ also exist
-- but are harder to describe succinctly.
module Data.Coders
  ( -- * Creating decoders.

    --
    -- $Decoders
    Decode (..),
    (<!),
    (<*!),
    (<?),
    decode,
    decodeSparse,

    -- * Index types for well-formed Coders.

    --
    -- $Indexes
    Density (..),
    Wrapped (..),
    Annotator (..),
    Field (..),
    ofield,
    invalidField,
    field,
    fieldA,
    fieldAA,

    -- * Using Duals .
    decodeDual,

    -- * Containers, Combinators, Annotators

    --
    -- $Combinators
    mapDecode,
    mapDecodeA,
    vMapDecode,
    setDecode,
    setDecodeA,
    listDecode,
    listDecodeA,
    pairDecodeA,
    decodeList,
    decodePair,
    decodeSeq,
    decodeStrictSeq,
    decodeSet,
    decodeAnnSet,

    -- * Low level (Encoding/Decoder) utility functions
    decodeRecordNamed,
    decodeRecordNamedT,
    decodeRecordSum,
    invalidKey,
    unusedRequiredKeys,
    duplicateKey,
    decodeNullMaybe,
    decodeCollectionWithLen,
    decodeCollection,
    decodeMap,
    decodeVMap,
    decodeMapNoDuplicates,
    decodeMapContents,
    decodeMapTraverse,
    decodeMapContentsTraverse,
    cborError,
  )
where

import qualified Cardano.Binary as C
import Cardano.Ledger.Binary.Decoding.Annotated (Annotator (..))
import Cardano.Ledger.Binary.Decoding.FromVCBOR (FromVCBOR (fromVCBOR))
import Cardano.Ledger.Binary.Decoding.VDecoder
import Codec.CBOR.Encoding (Encoding, encodeTag)
import Control.Applicative (liftA2)
import Control.Monad (replicateM, unless, when)
import Control.Monad.Trans (MonadTrans (..))
import Control.Monad.Trans.Identity (IdentityT (runIdentityT))
import Data.Foldable (foldl')
import Data.Functor.Compose (Compose (..))
import qualified Data.Map.Strict as Map
import Data.Maybe.Strict (StrictMaybe (SJust, SNothing))
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set, insert, member)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Typeable (Typeable, typeOf)
import qualified Data.VMap as VMap
import Data.Void (Void)
import Formatting (build, formatToString)
import Formatting.Buildable (Buildable)
import qualified GHC.Exts as Exts
import GHC.TypeLits
import Numeric.Natural (Natural)

-- ====================================================================

-- ===============================================================================
-- Encode and Decode are typed data structures which specify encoders and decoders
-- for Algebraic data structures written in Haskell. They exploit types and count
-- the correct number fields in an encoding and decoding, which are automatically computed.
-- They are somewhat dual, and are designed so that visual inspection of a Encode and
-- its dual Decode can help the user conclude that the two are self-consistent.
-- They are also reusable abstractions that can be defined once, and then used many places.
--
-- (Encode t) is a data structure from which 3 things can be recovered
-- Given:    x :: Encode t
-- 1. get a value of type t
-- 2. get an Encoding for that value, which correctly encodes the number of "fields"
--    written to the ByteString. Care must still be taken that the Keys are correct.
-- 3. get a (MemoBytes t)
--
-- The advantage of using Encode with a MemoBytes, is we don't have to make a ToCBOR
-- instance. Instead the "instance" is spread amongst the pattern constuctors by using
-- (memoBytes encoding) in the where clause of the pattern contructor.
-- See some examples of this see the file Timelocks.hs
--

-- ========================================================
-- Subsidary classes and datatype used in the Coders scheme
-- =========================================================

-- $Indexes
--  Some CBOR instances wrap encoding sequences with prefixes and suffixes. I.e.
--  prefix , encode, encode, encode , ... , suffix.
--  There are two kinds of wrapping coders: Nary sums, and Sparsely encoded products.
--  Coders in these classes can only be decoded when they are wrapped by their
--  closing forms 'Summands' and 'SparseKeyed'. Another dimension, where we use indexes
--  to maintain type safety, are records which can be
--  encoded densely (all their fields serialised) or sparsely (only some of their
--  fields). We use indexes to types to try and mark (and enforce) these distinctions.

-- | Index for record density. Distinguishing (all the fields) from (some of the fields).
data Density = Dense | Sparse

-- | Index for a wrapped Coder. Wrapping is necessary for 'Summands' and 'SparseKeyed'.
data Wrapped where
  Open :: Wrapped -- Needs some type-wide wrapping
  Closed :: Density -> Wrapped -- Does not need type-wide wrapping,
  -- But may need field-wide wrapping, when Density is 'Sparse

-- | A Field pairs an update function and a decoder for one field of a Sparse record.
data Field v t where
  Field :: (x -> t -> t) -> (forall s. VDecoder v s x) -> Field v t

{-# INLINE field #-}
field :: KnownNat v => (x -> t -> t) -> Decode ('Closed d) x -> Field v t
field update dec = Field update (decode dec)

{-# INLINE ofield #-}
ofield :: KnownNat v => (StrictMaybe x -> t -> t) -> Decode ('Closed d) x -> Field v t
ofield update dec = Field update (SJust <$> decode dec)

{-# INLINE invalidField #-}
invalidField :: forall v t. KnownNat v => Word -> Field v t
invalidField n = field (flip $ const @t @Void) (Invalid n)

-- | Sparse decode something with a (FromVCBOR (Annotator t)) instance
-- A special case of 'field'
fieldA :: (KnownNat v, Applicative ann) => (x -> t -> t) -> Decode ('Closed d) x -> Field v (ann t)
fieldA update dec = Field (liftA2 update) (pure <$> decode dec)

-- | Sparse decode something with a (FromVCBOR (Annotator t)) instance
fieldAA ::
  (KnownNat v, Applicative ann) =>
  (x -> t -> t) ->
  Decode ('Closed d) (ann x) ->
  Field v (ann t)
fieldAA update dec = Field (liftA2 update) (decode dec)

-- ==================================================================
-- Decode
-- ===================================================================

-- | The type @('Decode' t)@ is designed to be dual to @('Encode' t)@. It was designed so that
-- in many cases a decoder can be extracted from an encoder by visual inspection. We now give some
-- example of @(Decode t)@  and  @(Encode t)@ pairs.
--
--
-- An example with 1 constructor (a record) uses 'Rec' and 'RecD'
--
-- In this example, let @Int@ and @C@ have 'ToCBOR' instances, and @dualB :: Dual B@.
--
-- @
-- data C = C Text.Text
-- instance ToCBOR C where toCBOR (C t) = toCBOR t
-- instance FromVCBOR C where fromVCBOR = C <$> fromVCBOR
--
-- data B = B Text.Text
-- dualB = Dual (\ (B t) ->toCBOR t) (B <$> fromVCBOR)
--
-- data A = ACon Int B C
--
-- encodeA :: A -> Encode ('Closed 'Dense) A
-- encodeA (ACon i b c) = Rec ACon !> To i !> ED dualB b !> To c
--
-- decodeA :: Decode ('Closed 'Dense) A
-- decodeA = RecD ACon <! From <! DD dualB <! From
--
-- instance ToCBOR A   where toCBOR x = encode(encodeA x)
-- instance FromVCBOR A where fromVCBOR = decode decodeA
-- @
--
-- An example with multiple constructors uses 'Sum', 'SumD', and 'Summands'.
--
-- @
-- data N = N1 Int | N2 B Bool | N3 A
--
-- encodeN :: N -> Encode 'Open N
-- encodeN (N1 i)    = Sum N1 0 !> To i
-- encodeN (N2 b tf) = Sum N2 1 !> ED dualB b  !> To tf
-- encodeN (N3 a)    = Sum N3 2 !> To a
--
-- decodeN :: Decode ('Closed 'Dense) N    -- Note each clause has an 'Open decoder,
-- decodeN = Summands "N" decodeNx           -- But Summands returns a ('Closed 'Dense) decoder
--   where decodeNx 0 = SumD N1 <! From
--         decodeNx 1 = SumD N2 <! DD dualB <! From
--         decodeNx 3 = SumD N3 <! From
--         decodeNx k = Invalid k
--
-- instance ToCBOR N   where toCBOR x = encode(encodeN x)
-- instance FromVCBOR N where fromVCBOR = decode decodeN
-- @
--
-- Two examples using variants of sparse encoding for records, i.e. those datatypes with only one constructor.
-- The Virtual constructor approach using 'Summands', 'OmitC', 'Emit'.
-- The Sparse field approach using 'Keyed', 'Key' and 'Omit'. The approaches work
-- because encoders and decoders don't put
-- fields with default values in the Encoding, and reconstruct the default values on the decoding side.
-- We will illustrate the two approaches using the datatype M
--
-- @
-- data M = M Int [Bool] Text.Text
--   deriving (Show, Typeable)
--
-- a0, a1, a2, a3 :: M  -- Some illustrative examples, using things that might be given default values.
-- a0 = M 0 [] "ABC"
-- a1 = M 0 [True] "ABC"
-- a2 = M 9 [] "ABC"
-- a3 = M 9 [False] "ABC"
-- @
--
-- The virtual constructor strategy pretends there are mutiple constructors
-- Even though there is only one. We use invariants about the data to avoid
-- encoding some of the values. Note the use of 'Sum' with virtual constructor tags 0,1,2,3
--
-- @
-- encM :: M -> Encode 'Open M
-- encM (M 0 [] t) = Sum M 0 !> OmitC 0 !> OmitC [] !> To t
-- encM (M 0 bs t) = Sum M 1 !> OmitC 0 !> To bs !> To t
-- encM (M n [] t) = Sum M 2 !> To n !> OmitC [] !> To t
-- encM (M n bs t) = Sum M 3 !> To n !> To bs !> To t
--
-- decM :: Word -> Decode 'Open M
-- decM 0 = SumD M <! Emit 0 <! Emit [] <! From  -- The virtual constructors tell which fields have been Omited
-- decM 1 = SumD M <! Emit 0 <! From <! From     -- So those fields are reconstructed using 'Emit'.
-- decM 2 = SumD M <! From <! Emit [] <! From
-- decM 3 = SumD M <! From <! From <! From
-- decM n = Invalid n
--
-- instance ToCBOR M where
--   toCBOR m = encode (encM m)
--
-- instance FromVCBOR M where
--   fromVCBOR = decode (Summands "M" decM)
-- @
--
-- The Sparse field approach uses N keys, one for each field that is not defaulted. For example
-- @(M 9 [True] (pack "hi")))@. Here zero fields are defaulted, so there should be 3 keys.
-- Encoding this example would look something like this.
--
-- @
-- [TkMapLen 3,TkInt 0,TkInt 9,TkInt 1,TkListBegin,TkBool True,TkBreak,TkInt 2,TkString "hi"]
--                   ^key            ^key                                    ^key
-- @
--
-- So the user supplies a function, that encodes every field, each field must use a unique
-- key, and fields with default values have Omit wrapped around the Key encoding.
-- The user must ensure that there is NOT an Omit on a required field. 'encM2' is an example.
--
-- @
-- encM2:: M -> Encode ('Closed 'Sparse) M
-- encM2 (M n xs t) =
--     Keyed M
--        !> Omit (== 0) (Key 0 (To n))    -- Omit if n is zero
--        !> Omit null (Key 1 (To xs))     -- Omit if xs is null
--        !> Key 2 (To t)                  -- Always encode t
-- @
--
-- To write an Decoder we must pair a decoder for each field, with a function that updates only
-- that field. We use the 'Field' GADT to construct these pairs, and we must write a function, that
-- for each field tag, picks out the correct pair. If the Encode and Decode don't agree on how the
-- tags correspond to a particular field, things will fail.
--
-- @
-- boxM :: Word -> Field M
-- boxM 0 = field update0 From
--   where
--     update0 n (M _ xs t) = M n xs t
-- boxM 1 = field update1 From
--   where
--     update1 xs (M n _ t) = M n xs t
-- boxM 2 = field update2 From
--   where
--     update2 t (M n xs _) = M n xs t
-- boxM n = invalidField n
-- @
--
-- Finally there is a new constructor for 'Decode', called 'SparseKeyed', that decodes field
-- keyed sparse objects. The user supplies an initial value and field function, and a list
-- of tags of the required fields. The initial value should have default values and
-- any well type value in required fields. If the encode function (baz above) is
-- encoded properly the required fields in the initial value should always be over
-- overwritten. If it is not written properly, or a bad encoding comes from somewhere
-- else, the intial values in the required fields might survive decoding. The list
-- of required fields is checked.
--
-- @
-- instance FromVCBOR M where
--   fromVCBOR = decode (SparseKeyed
--                       "TT"                        -- ^ Name of the type being decoded
--                       (M 0 [] (Text.pack "a"))  -- ^ The default value
--                       boxM                      -- ^ The Field function
--                       [(2, "Stringpart")]         -- ^ The required Fields
--                     )
--
-- instance ToCBOR M where
--   toCBOR m = encode(encM2 m)
-- @
data Decode (w :: Wrapped) t where
  -- | Label the constructor of a Record-like datatype (one with exactly 1 constructor) as a Decode.
  RecD :: t -> Decode ('Closed 'Dense) t
  -- | Label the constructor of a Record-like datatype (one with multiple constructors) as an Decode.
  SumD :: t -> Decode 'Open t
  -- | Lift a Word to Decode function into a DeCode for a type with multiple constructors.
  Summands :: String -> (Word -> Decode 'Open t) -> Decode ('Closed 'Dense) t
  -- | Lift a Word to Field function into a DeCode for a type with 1 constructor stored sparsely
  SparseKeyed ::
    Typeable t =>
    -- | Name of the Type (for error messages)
    String ->
    -- | The type with default values in all fields
    t ->
    -- | What to do with key in the @Word@
    (forall v. KnownNat v => Word -> Field v t) ->
    -- | Pairs of keys and Strings which must be there (default values not allowed)
    [(Word, String)] ->
    Decode ('Closed 'Dense) t
  -- | Label a (component, field, argument) as sparsely stored, which will be populated
  -- with the default value.
  KeyedD :: t -> Decode ('Closed 'Sparse) t
  -- | Label a (component, field, argument). It will be decoded using the existing
  -- FromVCBOR instance at @t@
  From :: FromVCBOR t => Decode w t
  -- | Label a (component, field, argument). It will be decoded using the given decoder.
  D :: (forall s v. KnownNat v => VDecoder v s t) -> Decode ('Closed 'Dense) t
  -- | Apply a functional decoding (arising from 'RecD' or 'SumD') to get (type wise)
  -- smaller decoding.
  ApplyD :: Decode w1 (a -> t) -> Decode ('Closed d) a -> Decode w1 t
  -- | Mark a Word as a Decoding which is not a valid Decoding. Used when decoding sums
  -- that are tagged out of range.
  Invalid :: Word -> Decode w t
  -- | Used to make (Decode w) an instance of Functor.
  Map :: (a -> b) -> Decode w a -> Decode w b
  -- | Assert that the next thing decoded must be tagged with the given word.
  TagD :: Word -> Decode ('Closed x) t -> Decode ('Closed x) t
  -- | Decode the next thing, not by inspecting the bytes, but pulled out of thin air,
  -- returning @t@. Used in sparse decoding.
  Emit :: t -> Decode w t
  -- The next two could be generalized to any (Applicative f) rather than Annotator

  -- | Lift a @(Decode w t)@ to a @(Decode w (Annotator t))@. Used on a (component, field,
  -- argument) that was not Annotator encoded, but contained in Record or Sum which is
  -- Annotator encoded.
  Ann :: Decode w t -> Decode w (Annotator t)
  -- | Apply a functional decoding (arising from 'RecD' or 'SumD' that needs to be
  -- Annotator decoded) to get (type wise) smaller decoding.
  ApplyAnn ::
    -- | A functional Decode
    Decode w1 (Annotator (a -> t)) ->
    -- | An Decoder for an Annotator
    Decode ('Closed d) (Annotator a) ->
    Decode w1 (Annotator t)
  -- | the function to Either can raise an error when applied by returning (Left errorMessage)
  ApplyErr :: Decode w1 (a -> Either String t) -> Decode ('Closed d) a -> Decode w1 t

infixl 4 <!

infixl 4 <*!

infixl 4 <?

-- | Infix form of @ApplyD@ with the same infixity and precedence as @($)@.
(<!) :: Decode w1 (a -> t) -> Decode ('Closed w) a -> Decode w1 t
x <! y = ApplyD x y

-- | Infix form of @ApplyAnn@ with the same infixity and precedence as @($)@.
(<*!) :: Decode w1 (Annotator (a -> t)) -> Decode ('Closed d) (Annotator a) -> Decode w1 (Annotator t)
x <*! y = ApplyAnn x y

-- | Infix form of @ApplyErr@ with the same infixity and precedence as @($)@.
(<?) :: Decode w1 (a -> Either String t) -> Decode ('Closed d) a -> Decode w1 t
f <? y = ApplyErr f y

hsize :: Decode w t -> Int
hsize (Summands _ _) = 1
hsize (SumD _) = 0
hsize (RecD _) = 0
hsize (KeyedD _) = 0
hsize From = 1
hsize (D _) = 1
hsize (ApplyD f x) = hsize f + hsize x
hsize (Invalid _) = 0
hsize (Map _ x) = hsize x
hsize (Emit _) = 0
hsize SparseKeyed {} = 1
hsize (TagD _ _) = 1
hsize (Ann x) = hsize x
hsize (ApplyAnn f x) = hsize f + hsize x
hsize (ApplyErr f x) = hsize f + hsize x

decode :: KnownNat v => Decode w t -> VDecoder v s t
decode x = fmap snd (decodE x)

decodE :: KnownNat v => Decode w t -> VDecoder v s (Int, t)
decodE x = decodeCount x 0

decodeCount :: forall (w :: Wrapped) v s t. KnownNat v => Decode w t -> Int -> VDecoder v s (Int, t)
decodeCount (Summands nm f) n = (n + 1,) <$> decodeRecordSum nm (decodE . f)
decodeCount (SumD cn) n = pure (n + 1, cn)
decodeCount (KeyedD cn) n = pure (n + 1, cn)
decodeCount (RecD cn) n = decodeRecordNamed "RecD" (const n) (pure (n, cn))
decodeCount From n = (n,) <$> fromVCBOR
decodeCount (D dec) n = (n,) <$> dec
decodeCount (Invalid k) _ = invalidKey k
decodeCount (Map f x) n = do (m, y) <- decodeCount x n; pure (m, f y)
decodeCount (Emit x) n = pure (n, x)
decodeCount (TagD expectedTag decoder) n = do
  assertTag expectedTag
  decodeCount decoder n
decodeCount (SparseKeyed name initial pick required) n =
  (n + 1,) <$> decodeSparse name initial pick required
decodeCount (Ann x) n = do (m, y) <- decodeCount x n; pure (m, pure y)
decodeCount (ApplyAnn g x) n = do
  (i, f) <- decodeCount g (n + hsize x)
  y <- decodeClosed x
  pure (i, f <*> y)
decodeCount (ApplyD cn g) n = do
  (i, f) <- decodeCount cn (n + hsize g)
  y <- decodeClosed g
  pure (i, f y)
decodeCount (ApplyErr cn g) n = do
  (i, f) <- decodeCount cn (n + hsize g)
  y <- decodeClosed g
  case f y of
    Right z -> pure (i, z)
    Left message -> cborError $ DecoderErrorCustom "decoding error:" (Text.pack message)

-- The type of DecodeClosed precludes pattern match against (SumD c) as the types are different.

decodeClosed :: KnownNat v => Decode ('Closed d) t -> VDecoder v s t
decodeClosed (Summands nm f) = decodeRecordSum nm (decodE . f)
decodeClosed (KeyedD cn) = pure cn
decodeClosed (RecD cn) = pure cn
decodeClosed From = fromVCBOR
decodeClosed (D dec) = dec
decodeClosed (ApplyD cn g) = do
  f <- decodeClosed cn
  y <- decodeClosed g
  pure (f y)
decodeClosed (Invalid k) = invalidKey k
decodeClosed (Map f x) = f <$> decodeClosed x
decodeClosed (Emit n) = pure n
decodeClosed (TagD expectedTag decoder) = do
  assertTag expectedTag
  decodeClosed decoder
decodeClosed (SparseKeyed name initial pick required) =
  decodeSparse name initial pick required
decodeClosed (Ann x) = fmap pure (decodeClosed x)
decodeClosed (ApplyAnn g x) = do
  f <- decodeClosed g
  y <- decodeClosed x
  pure (f <*> y)
decodeClosed (ApplyErr cn g) = do
  f <- decodeClosed cn
  y <- decodeClosed g
  case f y of
    Right z -> pure z
    Left message -> cborError $ DecoderErrorCustom "decoding error:" (Text.pack message)

decodeSparse ::
  Typeable a =>
  String ->
  a ->
  (Word -> Field v a) ->
  [(Word, String)] ->
  VDecoder v s a
decodeSparse name initial pick required = do
  lenOrIndef <- decodeMapLenOrIndef
  (!v, used) <- case lenOrIndef of
    Just len -> getSparseBlock len initial pick Set.empty name
    Nothing -> getSparseBlockIndef initial pick Set.empty name
  if all (\(key, _name) -> member key used) required
    then pure v
    else unusedRequiredKeys used required (show (typeOf initial))

-- | Given a function that picks a Field from a key, decodes that field
--   and returns a (t -> t) transformer, which when applied, will
--   update the record with the value decoded.
applyField :: (Word -> Field v t) -> Set Word -> String -> VDecoder v s (t -> t, Set Word)
applyField f seen name = do
  tag <- decodeWord
  if Set.member tag seen
    then duplicateKey name tag
    else case f tag of
      Field update d -> d >>= \v -> pure (update v, insert tag seen)

-- | Decode a Map Block of key encoded data for type t
--   given a function that picks the right box for a given key, and an
--   initial value for the record (usually starts filled with default values).
--   The Block can be either len-encoded or block-encoded.
getSparseBlock :: Int -> t -> (Word -> Field v t) -> Set Word -> String -> VDecoder v s (t, Set Word)
getSparseBlock 0 initial _pick seen _name = pure (initial, seen)
getSparseBlock n initial pick seen name = do
  (transform, seen2) <- applyField pick seen name
  getSparseBlock (n - 1) (transform initial) pick seen2 name

getSparseBlockIndef :: t -> (Word -> Field v t) -> Set Word -> String -> VDecoder v s (t, Set Word)
getSparseBlockIndef initial pick seen name =
  decodeBreakOr >>= \case
    True -> pure (initial, seen)
    False -> do
      (transform, seen2) <- applyField pick seen name
      getSparseBlockIndef (transform initial) pick seen2 name

-- ======================================================
-- (Decode ('Closed 'Dense)) and (Decode ('Closed 'Sparse)) are applicative
-- (Decode 'Open) is not applicative since there is no
-- (Applys 'Open 'Open) instance. And there should never be one.

instance Functor (Decode w) where
  fmap f (Map g x) = Map (f . g) x
  fmap f x = Map f x

instance Applicative (Decode ('Closed d)) where
  pure x = Emit x
  f <*> x = ApplyD f x

-- | Use to and from, when you want to guarantee that a type has both
-- ToCBOR and FromCBR instances.
decodeDual :: forall t. (C.ToCBOR t, FromVCBOR t) => Decode ('Closed 'Dense) t
decodeDual = D fromVCBOR
  where
    -- Enforce ToCBOR constraint on t
    _toCBOR = C.toCBOR (undefined :: t)

-- Combinators

-- | Combinators for building @(Encode ('Closed 'Dense) x)@ and @(Decode ('Closed 'Dense) x)@ objects.
--
-- The use of the low level function 'encodeFoldable' is not self-documenting at all (and
-- not even correct for Maps, even though Map is an instance of Foldable). So instead of
-- writing: @(E encodeFoldable x)@, we want people to write:
--
-- 1. @(mapEncode x)@   if x is a Map
-- 2. @(setEncode x)@   if x is a Set
-- 3. @(listEncode x)@  if x is a List
--
-- To decode one of these foldable instances, we should use one of the aptly named Duals
--
-- 1. @mapDecode@   if x is a Map
-- 2. @setDecode@   if x is a Set
-- 3. @listDecode@  if x is a List
--
-- If one needs an 'Annotated' decoder, one can use (explained further below)
--
-- 1. @mapDecodeA@   if x is a Map
-- 2. @setDecodeA@   if x is a Set
-- 3. @listDecodeA@  if x is a List
-- 4. @pairDecodeA@  if x is a Pair like (Int,Bool)

-- | @(mapDecode)@ is the Dual for @(mapEncode x)@
mapDecode :: (Ord k, FromVCBOR k, FromVCBOR v) => Decode ('Closed 'Dense) (Map.Map k v)
mapDecode = D (decodeMap fromVCBOR fromVCBOR)

-- | @(vMapDecode)@ is the Dual for @(vMapEncode x)@
vMapDecode ::
  (VMap.Vector kv k, VMap.Vector vv v, Ord k, FromVCBOR k, FromVCBOR v) =>
  Decode ('Closed 'Dense) (VMap.VMap kv vv k v)
vMapDecode = D (decodeVMap fromVCBOR fromVCBOR)

-- | @(setDecode)@ is the Dual for @(setEncode x)@
setDecode :: (Ord v, FromVCBOR v) => Decode ('Closed 'Dense) (Set.Set v)
setDecode = D (decodeSet fromVCBOR)

-- | @(listDecode)@ is the Dual for @(listEncode x)@
listDecode :: (FromVCBOR v) => Decode ('Closed 'Dense) [v]
listDecode = D (decodeList fromVCBOR)

-- =============================================================================

-- | Combinators for building (Decode ('Closed 'Dense) (Annotator x)) objects. Unlike
-- the combinators above (setDecode, mapDecode, ListDecode) for Non-Annotator types,
-- these combinators take explicit (Decode  ('Closed 'Dense) i) objects as parameters
-- rather than relying on FromVCBOR instances as implicit parameters. To get the
-- annotator version, just add 'A' to the end of the non-annotator version decode function.
-- E.g.  setDecodeA, listDecodeA, mapDecodeA. Suppose I want to decode x:: Map [A] (B,C)
-- and I only have Annotator instances of A and C, then the following decodes x.
-- mapDecodeA (listDecodeA From) (pairDecodeA (Ann From) From).
--                                             ^^^^^^^^
-- One can always lift x::(Decode w T) by using Ann. so (Ann x)::(Decode w (Annotator T)).
pairDecodeA ::
  Decode ('Closed 'Dense) (Annotator x) ->
  Decode ('Closed 'Dense) (Annotator y) ->
  Decode ('Closed 'Dense) (Annotator (x, y))
pairDecodeA x y = D $ do
  (xA, yA) <- decodePair (decode x) (decode y)
  pure ((,) <$> xA <*> yA)

listDecodeA :: Decode ('Closed 'Dense) (Annotator x) -> Decode ('Closed 'Dense) (Annotator [x])
listDecodeA dx = D (sequence <$> decodeList (decode dx))

setDecodeA ::
  Ord x =>
  Decode ('Closed 'Dense) (Annotator x) ->
  Decode ('Closed 'Dense) (Annotator (Set x))
setDecodeA dx = D (decodeAnnSet (decode dx))

mapDecodeA ::
  Ord k =>
  Decode ('Closed 'Dense) (Annotator k) ->
  Decode ('Closed 'Dense) (Annotator v) ->
  Decode ('Closed 'Dense) (Annotator (Map.Map k v))
mapDecodeA k v = D (decodeMapTraverse (decode k) (decode v))

--------------------------------------------------------------------------------
-- Utility functions for working with CBOR
--------------------------------------------------------------------------------

assertTag :: Word -> VDecoder v s ()
assertTag tag = do
  t <-
    peekTokenType >>= \case
      TypeTag -> fromIntegral <$> decodeTag
      TypeTag64 -> fromIntegral <$> decodeTag64
      _ -> fail "expected tag"
  when (t /= (fromIntegral tag :: Natural)) $
    fail $ "expecteg tag " <> show tag <> " but got tag " <> show t

decodeRecordNamed :: Text.Text -> (a -> Int) -> VDecoder v s a -> VDecoder v s a
decodeRecordNamed name getRecordSize decoder = do
  runIdentityT $ decodeRecordNamedT name getRecordSize (lift decoder)

decodeRecordNamedT ::
  (MonadTrans m, Monad (m (VDecoder v s))) =>
  Text.Text ->
  (a -> Int) ->
  m (VDecoder v s) a ->
  m (VDecoder v s) a
decodeRecordNamedT name getRecordSize decoder = do
  lenOrIndef <- lift decodeListLenOrIndef
  x <- decoder
  lift $ case lenOrIndef of
    Just n -> matchSize (Text.pack "\nRecord " <> name) n (getRecordSize x)
    Nothing -> do
      isBreak <- decodeBreakOr
      unless isBreak $ cborError $ DecoderErrorCustom name "Excess terms in array"
  pure x

decodeRecordSum :: String -> (Word -> VDecoder v s (Int, a)) -> VDecoder v s a
decodeRecordSum name decoder = do
  lenOrIndef <- decodeListLenOrIndef
  tag <- decodeWord
  (size, x) <- decoder tag -- we decode all the stuff we want
  case lenOrIndef of
    Just n ->
      let errMsg =
            "\nSum " ++ name ++ "\nreturned="
              ++ show size
              ++ " actually read= "
              ++ show n
       in matchSize (Text.pack errMsg) size n
    Nothing -> do
      isBreak <- decodeBreakOr -- if there is stuff left, it is unnecessary extra stuff
      unless isBreak $ cborError $ DecoderErrorCustom (Text.pack name) "Excess terms in array"
  pure x


decodePair :: VDecoder v s a -> VDecoder v s b -> VDecoder v s (a, b)
decodePair first second = decodeRecordNamed "pair" (const 2) ((,) <$> first <*> second)

invalidKey :: Word -> VDecoder v s a
invalidKey k = cborError $ DecoderErrorCustom "not a valid key:" (Text.pack $ show k)

duplicateKey :: String -> Word -> VDecoder v s a
duplicateKey name k =
  cborError $
    DecoderErrorCustom
      "Duplicate key:"
      (Text.pack $ show k ++ " while decoding type " ++ name)

unusedRequiredKeys :: Set Word -> [(Word, String)] -> String -> VDecoder v s a
unusedRequiredKeys used required name =
  cborError $
    DecoderErrorCustom
      (Text.pack ("value of type " ++ name))
      (Text.pack (message (filter bad required)))
  where
    bad (k, _) = not (member k used)
    message [] = ", not decoded."
    message [pair] = report pair ++ message []
    message (pair : more) = report pair ++ ", and " ++ message more
    report (k, f) = "field " ++ f ++ " with key " ++ show k

decodeSeq :: KnownNat v => VDecoder v s a -> VDecoder v s (Seq a)
decodeSeq decoder = Seq.fromList <$> decodeList decoder

decodeStrictSeq :: KnownNat v => VDecoder v s a -> VDecoder v s (StrictSeq a)
decodeStrictSeq decoder = StrictSeq.fromList <$> decodeList decoder

decodeAnnSet :: (KnownNat v, Ord t) => VDecoder v s (Annotator t) -> VDecoder v s (Annotator (Set t))
decodeAnnSet dec = do
  xs <- decodeList dec
  pure (Set.fromList <$> sequence xs)

-- Utilities

decodeCollection :: VDecoder v s (Maybe Int) -> VDecoder v s a -> VDecoder v s [a]
decodeCollection lenOrIndef el = snd <$> decodeCollectionWithLen lenOrIndef el

decodeCollectionWithLen ::
  VDecoder v s (Maybe Int) ->
  VDecoder v s a ->
  VDecoder v s (Int, [a])
decodeCollectionWithLen lenOrIndef el = do
  lenOrIndef >>= \case
    Just len -> (,) len <$> replicateM len el
    Nothing -> loop (0, []) (not <$> decodeBreakOr) el
  where
    loop (n, acc) condition action =
      condition >>= \case
        False -> pure (n, reverse acc)
        True -> action >>= \v -> loop (n + 1, v : acc) condition action

decodeAccWithLen ::
  VDecoder v s (Maybe Int) ->
  (a -> b -> b) ->
  b ->
  VDecoder v s a ->
  VDecoder v s (Int, b)
decodeAccWithLen lenOrIndef combine acc0 action = do
  mLen <- lenOrIndef
  let condition = case mLen of
        Nothing -> const <$> decodeBreakOr
        Just len -> pure (>= len)
      loop !i !acc = do
        shouldStop <- condition
        if shouldStop i
          then pure (i, acc)
          else do
            v <- action
            loop (i + 1) (v `combine` acc)
  loop 0 acc0

-- | Just like `decodeMap`, but assumes there are no duplicate keys
decodeMapNoDuplicates :: Ord a => VDecoder v s a -> VDecoder v s b -> VDecoder v s (Map.Map a b)
decodeMapNoDuplicates decodeKey decodeValue =
  snd
    <$> decodeAccWithLen
      decodeMapLenOrIndef
      (uncurry Map.insert)
      Map.empty
      decodeInlinedPair
  where
    decodeInlinedPair = do
      !key <- decodeKey
      !value <- decodeValue
      pure (key, value)

decodeMapContents :: VDecoder v s a -> VDecoder v s [a]
decodeMapContents = decodeCollection decodeMapLenOrIndef

decodeMapTraverse ::
  (Ord a, Applicative t) =>
  VDecoder v s (t a) ->
  VDecoder v s (t b) ->
  VDecoder v s (t (Map.Map a b))
decodeMapTraverse decodeKey decodeValue =
  fmap Map.fromList <$> decodeMapContentsTraverse decodeKey decodeValue

decodeMapContentsTraverse ::
  (Applicative t) =>
  VDecoder v s (t a) ->
  VDecoder v s (t b) ->
  VDecoder v s (t [(a, b)])
decodeMapContentsTraverse decodeKey decodeValue =
  sequenceA <$> decodeMapContents decodeInlinedPair
  where
    decodeInlinedPair = getCompose $ (,) <$> Compose decodeKey <*> Compose decodeValue