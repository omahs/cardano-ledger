{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.Shelley.Orphans () where

-- import qualified Cardano.Crypto.DSIGN as DSIGN
-- import Cardano.Ledger.Coin (Coin (..))
-- import Cardano.Ledger.Crypto (DSIGN)
-- import Cardano.Ledger.Keys
-- import Data.Functor.Identity (Identity)
-- import Data.Maybe.Strict (StrictMaybe)
-- import Data.TreeDiff.Class (ToExpr (..))
-- import Generic.Random (genericArbitraryU)
-- import Test.Cardano.Ledger.Shelley.Utils (Split (..))
-- import Test.QuickCheck (Arbitrary (..))

-- We need this here for the tests, but should not be in the actual library because
-- a Num instance for this type does not make sense in the general case.
--deriving instance Num (DSIGN.VerKeyDSIGN (DSIGN c)) => Num (VKey kd c)


-- ============================================================
