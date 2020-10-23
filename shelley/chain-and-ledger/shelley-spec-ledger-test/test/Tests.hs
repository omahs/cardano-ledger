{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

import Cardano.Crypto.Libsodium (sodiumInit)
import qualified Cardano.Ledger.Core as Core
import Data.Proxy
import Shelley.Spec.Ledger.Coin (Coin)
import Test.Control.Iterate.SetAlgebra (setAlgTest)
import Test.QuickCheck (Arbitrary (..), Gen)
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C)
import Test.Shelley.Spec.Ledger.MemoBytes (memoBytesTest)
import Test.Shelley.Spec.Ledger.PropertyTests (minimalPropertyTests, propertyTests)
import Test.Shelley.Spec.Ledger.Rewards (rewardTests)
import Test.Shelley.Spec.Ledger.STSTests (chainExamples)
import qualified Test.Shelley.Spec.Ledger.Serialisation as Serialisation
import Test.Shelley.Spec.Ledger.UnitTests (unitTests)
import Test.Shelley.Spec.Ledger.ValProp (valTests)
import Test.Tasty
import Test.TestScenario (TestScenario (..), mainWithTestScenario)

tests :: Gen (Core.Value C) -> TestTree
tests gv = askOption $ \case
  Nightly -> (nightlyTests gv)
  Fast -> fastTests
  _ -> (mainTests gv)

mainTests :: Gen (Core.Value C) -> TestTree
mainTests gv =
  testGroup
    "Ledger with Delegation"
    [ minimalPropertyTests gv,
      rewardTests (Proxy :: Proxy C),
      Serialisation.tests 5,
      chainExamples,
      --multisigExamples, - TODO re-enable after the script embargo has been lifted
      unitTests,
      setAlgTest,
      memoBytesTest,
      valTests
    ]

nightlyTests :: Gen (Core.Value C) -> TestTree
nightlyTests gv =
  testGroup
    "Ledger with Delegation nightly"
    [ propertyTests gv,
      Serialisation.tests 50
    ]

fastTests :: TestTree
fastTests =
  testGroup
    "Ledger with Delegation fast"
    [ Serialisation.tests 1,
      chainExamples,
      --multisigExamples, - TODO re-enable after the script embargo has been lifted
      unitTests,
      setAlgTest,
      memoBytesTest,
      valTests
    ]

-- Generator for coin. This is required, but its ouput is completely discarded.
-- What is going on here?
--
-- In order to support running tests in multiple eras (which may have different
-- values) we allow providing a value generator from the top level. However,
-- this value generator is currently only used to generate the non-coin part of
-- the value, since we pass additional arguments to the coin generator.
--
-- However, in the Shelley era, the value _is_ Coin, so anything generated by
-- this is immediately overridden by the specialised `Coin` generator.
--
-- The correct solution here will be to allow passing a generator which can have
-- the correct arguments plumbed in. At that point we can remove the specialised
-- Coin generator with its overrides, and simply establish the correct generator
-- from the top for the correct era.
--
-- TODO CAD-2119 covers the task of fixing this generator infrastructure.
--
-- Note that the fact that the output of this generator is completely discarded
-- is the _only_ reason that it's OK to use the naked @Arbitrary@ instance here!
genVl :: Gen Coin
genVl = arbitrary

-- main entry point
main :: IO ()
main = sodiumInit >> mainWithTestScenario (tests genVl)
