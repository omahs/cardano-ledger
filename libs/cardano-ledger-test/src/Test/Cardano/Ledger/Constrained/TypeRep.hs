{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.Constrained.TypeRep
  ( Rep (..),
    (:~:) (Refl),
    Shape (..),
    Singleton (..),
    Eql,
    synopsis,
    compareRep,
    genSizedRep,
    genRep,
  )
where

-- import Cardano.Ledger.Shelley.LedgerState
import Cardano.Ledger.BaseTypes (EpochNo)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core (EraTxOut, TxOut)
import Cardano.Ledger.Credential (Credential)
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Keys (KeyHash, KeyRole (StakePool, Staking))
import Cardano.Ledger.PoolParams (PoolParams (ppId))
import Cardano.Ledger.TxIn (TxIn)
import Cardano.Ledger.UTxO (UTxO (..))
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Universe (Eql, Shape (..), Shaped (..), Singleton (..), cmpIndex, (:~:) (Refl))
import Data.Word (Word64)
import Test.Cardano.Ledger.Constrained.Combinators
import Test.Cardano.Ledger.Core.Arbitrary ()
import Test.Cardano.Ledger.Generic.PrettyCore (credSummary, keyHashSummary, txInSummary)
import Test.Cardano.Ledger.Generic.Proof (Proof)
import Test.Cardano.Ledger.Shelley.Serialisation.EraIndepGenerators ()
import Test.QuickCheck hiding (Fixed, total)

-- ==============================================

infixr 0 :->

data Rep era t where
  RationalR :: Rep era Rational
  CoinR :: Rep era Coin
  EpochR :: Rep era EpochNo
  (:->) :: Rep era a -> Rep era b -> Rep era (a -> b)
  MapR :: Ord a => Rep era a -> Rep era b -> Rep era (Map a b)
  SetR :: Ord a => Rep era a -> Rep era (Set a)
  ListR :: Rep era a -> Rep era [a]
  CredR :: Rep era (Credential 'Staking (EraCrypto era))
  PoolR :: Rep era (KeyHash 'StakePool (EraCrypto era))
  PoolParamsR :: Rep era (PoolParams (EraCrypto era))
  IntR :: Rep era Int
  Word64R :: Rep era Word64
  UTxOR :: (EraTxOut era, Arbitrary (TxOut era)) => Proof era -> Rep era (UTxO era)
  TxOutR :: Arbitrary (TxOut era) => Proof era -> Rep era (TxOut era)
  TxInR :: Rep era (TxIn (EraCrypto era))
  StringR :: Rep era String

-- ===========================================================
-- Proof of Rep equality

instance Singleton (Rep e) where
  testEql CoinR CoinR = Just Refl
  testEql (a :-> b) (x :-> y) = do
    Refl <- testEql a x
    Refl <- testEql b y
    Just Refl
  testEql (MapR a b) (MapR x y) = do
    Refl <- testEql a x
    Refl <- testEql b y
    Just Refl
  testEql (SetR a) (SetR b) = do
    Refl <- testEql a b
    Just Refl
  testEql (ListR a) (ListR b) = do
    Refl <- testEql a b
    Just Refl
  testEql CredR CredR = Just Refl
  testEql EpochR EpochR = Just Refl
  testEql RationalR RationalR = Just Refl
  testEql PoolR PoolR = Just Refl
  testEql PoolParamsR PoolParamsR = Just Refl
  testEql Word64R Word64R = Just Refl
  testEql IntR IntR = Just Refl
  testEql (UTxOR p1) (UTxOR p2) = do
    Refl <- testEql p1 p2
    pure Refl
  testEql (TxOutR p1) (TxOutR p2) = do
    Refl <- testEql p1 p2
    pure Refl
  testEql TxInR TxInR = Just Refl
  testEql StringR StringR = Just Refl
  testEql _ _ = Nothing
  cmpIndex x y = compare (shape x) (shape y)

-- ============================================================
-- Show instances

instance Show (Rep era t) where
  show CoinR = "Coin"
  show (a :-> b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (MapR a b) = "(Map " ++ show a ++ " " ++ show b ++ ")"
  show (SetR a) = "(Set " ++ show a ++ " " ++ ")"
  show (ListR a) = "[" ++ show a ++ "]"
  show CredR = "Cred" -- "(Credential 'Staking c)"
  show PoolR = "Pool" -- "(KeyHash 'StakePool c)"
  show PoolParamsR = "(PoolParams c)"
  show EpochR = "EpochNo"
  show RationalR = "Rational"
  show Word64R = "Word64"
  show IntR = "Int"
  show (UTxOR x) = "(UTxO " ++ show x ++ ")"
  show (TxOutR x) = "(TxOut " ++ show x ++ ")"
  show TxInR = "TxIn"
  show StringR = "String"

synopsis :: forall e t. Rep e t -> t -> String
synopsis RationalR r = show r
synopsis CoinR c = show c
synopsis EpochR e = show e
synopsis (a :-> b) _ = "(Arrow " ++ show a ++ " " ++ show b ++ ")"
synopsis Word64R w = show w
synopsis rep@(MapR a b) mp = case Map.toList mp of
  [] -> "(empty::Map " ++ show a ++ " " ++ show b ++ ")"
  ((d, r) : _) -> "Map{" ++ synopsis a d ++ " -> " ++ synopsis b r ++ " | " ++ show (Map.size mp) ++ synSum rep mp ++ "}"
synopsis rep@(SetR a) t
  | Set.null t = "(empty::Set " ++ show a ++ ")"
  | otherwise = "Set{" ++ synopsis a (head (Set.elems t)) ++ " | " ++ show (Set.size t) ++ synSum rep t ++ "}"
synopsis rep@(ListR a) ll = case ll of
  [] -> "(empty::" ++ show (ListR a) ++ "]"
  (d : _) -> "[" ++ synopsis a d ++ " | " ++ show (length ll) ++ synSum rep ll ++ "]"
synopsis CredR c = show (credSummary c)
synopsis PoolR k = "(KeyHash 'PoolStake " ++ show (keyHashSummary k) ++ ")"
synopsis PoolParamsR pp = "(PoolParams " ++ synopsis @e PoolR (ppId pp) ++ ")"
synopsis IntR n = show n
synopsis (UTxOR p) (UTxO mp) = "UTxO( " ++ synopsis (MapR TxInR (TxOutR p)) mp ++ " )"
synopsis (TxOutR _) _ = "(type family TxOut)" -- eventually use pcTxOut
synopsis TxInR txin = show (txInSummary txin)
synopsis StringR s = show s

synSum :: Rep era a -> a -> String
synSum (MapR _ CoinR) m = " | " ++ show (Map.foldl' (<>) mempty m)
synSum (MapR _ RationalR) m = " | " ++ show (Map.foldl' (+) 0 m)
synSum (SetR CoinR) m = " | " ++ show (Set.foldl' (<>) mempty m)
synSum (SetR RationalR) m = " | " ++ show (Set.foldl' (+) 0 m)
synSum (ListR CoinR) m = " | " ++ show (List.foldl' (<>) mempty m)
synSum (ListR RationalR) m = " | " ++ show (List.foldl' (+) 0 m)
synSum _ _ = ""

-- ==================================================

instance Shaped (Rep era) any where
  shape CoinR = Nullary 0
  shape (a :-> b) = Nary 1 [shape a, shape b]
  shape (MapR a b) = Nary 2 [shape a, shape b]
  shape (SetR a) = Nary 3 [shape a]
  shape (ListR a) = Nary 4 [shape a]
  shape CredR = Nullary 5
  shape PoolR = Nullary 6
  shape PoolParamsR = Nullary 7
  shape EpochR = Nullary 8
  shape RationalR = Nullary 9
  shape Word64R = Nullary 10
  shape IntR = Nullary 11
  shape (UTxOR p) = Nary 12 [shape p]
  shape (TxOutR p) = Nary 13 [shape p]
  shape TxInR = Nullary 14
  shape StringR = Nullary 15

compareRep :: forall era t s. Rep era t -> Rep era s -> Ordering
compareRep x y = cmpIndex @(Rep era) x y

-- ================================================

genSizedRep :: Crypto (EraCrypto era) => Int -> Rep era t -> Gen t
genSizedRep _ CoinR = arbitrary
genSizedRep n (_a :-> b) = const <$> genSizedRep n b
genSizedRep n (MapR a b) = do
  mapSized n (genSizedRep n a) (genSizedRep n b)
genSizedRep n (SetR a) = do
  setSized n (genSizedRep n a)
genSizedRep n (ListR a) = vectorOf n (genSizedRep n a)
genSizedRep _ CredR = arbitrary
genSizedRep _ PoolR = arbitrary
genSizedRep _ PoolParamsR = arbitrary
genSizedRep _ EpochR = arbitrary
genSizedRep _ RationalR = arbitrary
genSizedRep _ Word64R = arbitrary
genSizedRep _ IntR = arbitrary
genSizedRep _n (UTxOR _) = arbitrary
genSizedRep _ (TxOutR _) = arbitrary
genSizedRep _ TxInR = arbitrary
genSizedRep n StringR = vectorOf n arbitrary

genRep :: Crypto (EraCrypto era) => Rep era b -> Gen b
genRep x = do (NonZero n) <- arbitrary; genSizedRep n x

-- ======================================
