{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.BaseTypesSpec (spec) where

import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Binary
import Data.Aeson
import Data.ByteString.Lazy (ByteString)
import Data.Either
import Data.GenValidity (GenValid (genValid))
import Data.GenValidity.Scientific ()
import Data.Scientific
import Data.Typeable
import Test.Cardano.Ledger.Binary.RoundTrip (roundTripCborExpectation)
import Test.Cardano.Ledger.Common
import Test.Cardano.Ledger.Core.Arbitrary ()
import Test.Cardano.Ledger.Core.Utils (epsilonMaybeEq)

boundedRationalTests ::
  forall a.
  ( BoundedRational a
  , ToJSON a
  , FromJSON a
  , ToCBOR a
  , FromCBOR a
  , Arbitrary a
  , GenValid a
  , Show a
  , Ord a
  ) =>
  [(String, ByteString)] ->
  Spec
boundedRationalTests badJSONValues = do
  describe (showsTypeRep (typeRep (Proxy :: Proxy a)) "") $ do
    describe "Rational roundtrip" $ do
      prop "(boundRational . unboundRational)" $ \(bi :: a) ->
        Just bi === boundRational (unboundRational bi)
      prop "(unboundRational . boundRational)" $
        forAll genValid $ \r ->
          maybe
            (property True)
            ((r ===) . unboundRational)
            (boundRational r :: Maybe a)
      prop "bounding produces valid values within bounds" $
        forAll genValid $ \r ->
          case boundRational r of
            Nothing -> property True
            Just (br :: a) ->
              conjoin
                [ minBound <= br
                , br <= maxBound
                , unboundRational (minBound :: a) <= r
                , r <= unboundRational (maxBound :: a)
                ]
    describe "JSON" $ do
      prop "ToJSON/FromJSON roundtrip up to an epsilon" $
        forAll genValid $ \(br :: a) ->
          within 500000 $
            case eitherDecode (encode br) of
              Left err -> error err
              Right (br' :: a) ->
                epsilonMaybeEq 1e-18 (unboundRational br) (unboundRational br')
      prop "Roundtrip to Scientific and back up to an epsilon" $
        forAll genValid $ \ui ->
          within 500000 $
            case fromRationalRepetendLimited 20 (unboundRational ui) of
              Left (s, r) -> Just ui === boundRational (toRational s + r)
              Right (s, Nothing) ->
                classify
                  True
                  "no-repeat digits"
                  (Right ui === boundedFromJSON (encode s))
              Right (s, Just r) ->
                Just ui === boundRational (toRationalRepetend s r)
      prop "Roundtrip from valid Scientific and back exactly" $
        within 500000 $
          forAll genValid $ \(s :: Scientific) ->
            case eitherDecode (encode s) of
              Right (ui :: a) -> s === fromRational (unboundRational ui)
              Left _ -> property True
      describe "Bad Values" $ do
        prop "Check divergence" $
          within 500000 $
            boundedFromJSON "10e1234567893456" `shouldSatisfy` isLeft
        forM_ badJSONValues $ \(testName, invalidInput) ->
          it testName $
            boundedFromJSON invalidInput `shouldSatisfy` isLeft
    prop "CBOR roundtrip" $
      forAll genValid $
        \(br :: a) -> roundTripCborExpectation br
  where
    boundedFromJSON = eitherDecode :: ByteString -> Either String a

spec :: Spec
spec = do
  let badJSONValues =
        [("Word64 denominator overflow", "3.14159265358979323e-7"), ("Negative value", "-1e-3")]
  describe "BoundedRational" $ do
    boundedRationalTests @UnitInterval $ badJSONValues ++ [("Too big", "1.01")]
    boundedRationalTests @PositiveUnitInterval $
      badJSONValues ++ [("Zero", "0"), ("Too big", "1.01")]
    boundedRationalTests @PositiveInterval $ badJSONValues ++ [("Zero", "0")]
    boundedRationalTests @NonNegativeInterval badJSONValues
