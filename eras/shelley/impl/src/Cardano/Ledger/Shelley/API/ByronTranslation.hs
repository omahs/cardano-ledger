{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Cardano.Ledger.Shelley.API.ByronTranslation (
  translateToShelleyLedgerState,

  -- * Exported for testing purposes
  translateCompactTxOutByronToShelley,
  translateTxIdByronToShelley,
)
where

import qualified Cardano.Chain.Block as Byron
import qualified Cardano.Chain.Common as Byron
import qualified Cardano.Chain.UTxO as Byron
import qualified Cardano.Crypto.Hash as Crypto
import qualified Cardano.Crypto.Hashing as Hashing
import Cardano.Ledger.Address (fromBoostrapCompactAddress, isBootstrapRedeemer)
import Cardano.Ledger.BaseTypes (BlocksMade (..), TxIx (..))
import Cardano.Ledger.Coin (CompactForm (CompactCoin))
import Cardano.Ledger.Core
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.EpochBoundary
import Cardano.Ledger.SafeHash (unsafeMakeSafeHash)
import Cardano.Ledger.Shelley (ShelleyEra)
import Cardano.Ledger.Shelley.API.Types
import Cardano.Ledger.Shelley.Rules ()
import Cardano.Ledger.Slot
import Cardano.Ledger.UTxO (coinBalance)
import Cardano.Ledger.Val ((<->))
import qualified Data.ByteString.Short as SBS
import Data.Default.Class (def)
import qualified Data.Map.Strict as Map
import Data.Word
import GHC.Stack (HasCallStack)
import Lens.Micro.Extras (view)

-- | We use the same hashing algorithm so we can unwrap and rewrap the bytes.
-- We don't care about the type that is hashed, which will differ going from
-- Byron to Shelley, we just use the hashes as IDs.
translateTxIdByronToShelley ::
  (CC.Crypto c, CC.ADDRHASH c ~ Crypto.Blake2b_224) =>
  Byron.TxId ->
  TxId c
translateTxIdByronToShelley =
  TxId . unsafeMakeSafeHash . hashFromShortBytesE . Hashing.abstractHashToShort

hashFromShortBytesE ::
  forall h a.
  (Crypto.HashAlgorithm h, HasCallStack) =>
  SBS.ShortByteString ->
  Crypto.Hash h a
hashFromShortBytesE sbs =
  case Crypto.hashFromBytesShort sbs of
    Just !h -> h
    Nothing ->
      error $ "hashFromBytesShort called with ShortByteString of the wrong length: " <> show sbs

translateCompactTxOutByronToShelley :: Byron.CompactTxOut -> ShelleyTxOut (ShelleyEra c)
translateCompactTxOutByronToShelley (Byron.CompactTxOut compactAddr amount) =
  TxOutCompact
    (fromBoostrapCompactAddress compactAddr)
    (CompactCoin (Byron.unsafeGetLovelace amount))

translateCompactTxInByronToShelley ::
  (CC.Crypto c, CC.ADDRHASH c ~ Crypto.Blake2b_224) =>
  Byron.CompactTxIn ->
  TxIn c
translateCompactTxInByronToShelley (Byron.CompactTxInUtxo compactTxId idx) =
  TxIn
    (translateTxIdByronToShelley (Byron.fromCompactTxId compactTxId))
    (TxIx ((fromIntegral :: Word16 -> Word64) idx))

translateUTxOByronToShelley ::
  forall c.
  (CC.Crypto c, CC.ADDRHASH c ~ Crypto.Blake2b_224) =>
  Byron.UTxO ->
  UTxO (ShelleyEra c)
translateUTxOByronToShelley (Byron.UTxO utxoByron) =
  UTxO $
    Map.fromList
      [ (txInShelley, txOutShelley)
      | (txInByron, txOutByron) <- Map.toList utxoByron
      , let txInShelley = translateCompactTxInByronToShelley txInByron
            txOutShelley = translateCompactTxOutByronToShelley txOutByron
      ]

translateToShelleyLedgerState ::
  forall c.
  (CC.Crypto c, CC.ADDRHASH c ~ Crypto.Blake2b_224) =>
  ShelleyGenesis (ShelleyEra c) ->
  EpochNo ->
  Byron.ChainValidationState ->
  NewEpochState (ShelleyEra c)
translateToShelleyLedgerState genesisShelley epochNo cvs =
  NewEpochState
    { nesEL = epochNo
    , nesBprev = BlocksMade Map.empty
    , nesBcur = BlocksMade Map.empty
    , nesEs = epochState
    , nesRu = SNothing
    , nesPd = PoolDistr Map.empty
    , -- At this point, we compute the stashed AVVM addresses, while we are able
      -- to do a linear scan of the UTxO, and stash them away for use at the
      -- Shelley/Allegra boundary.
      stashedAVVMAddresses =
        let UTxO utxo = sutxosUtxo . lsUTxOState . esLState $ epochState
            redeemers =
              Map.filter (maybe False isBootstrapRedeemer . view bootAddrTxOutF) utxo
         in UTxO redeemers
    }
  where
    pparams :: ShelleyPParams (ShelleyEra c)
    pparams = sgProtocolParams genesisShelley

    -- NOTE: we ignore the Byron delegation map because the genesis and
    -- delegation verification keys are hashed using a different hashing
    -- scheme. This means we can't simply convert them, as Byron nowhere stores
    -- the original verification keys.
    --
    -- Fortunately, no Byron genesis delegations have happened yet, and if
    -- they did, we would be aware of them before the hard fork, as we
    -- instigate the hard fork. We just have to make sure that the hard-coded
    -- Shelley genesis contains the same genesis and delegation verification
    -- keys, but hashed with the right algorithm.
    genDelegs :: GenDelegs c
    genDelegs = GenDelegs $ sgGenDelegs genesisShelley

    reserves :: Coin
    reserves =
      word64ToCoin (sgMaxLovelaceSupply genesisShelley) <-> coinBalance utxoShelley

    epochState :: EpochState (ShelleyEra c)
    epochState =
      EpochState
        { esAccountState = AccountState (Coin 0) reserves
        , esSnapshots = emptySnapShots
        , esLState = ledgerState
        , esPrevPp = pparams
        , esPp = pparams
        , esNonMyopic = def
        }

    utxoByron :: Byron.UTxO
    utxoByron = Byron.cvsUtxo cvs

    utxoShelley :: UTxO (ShelleyEra c)
    utxoShelley = translateUTxOByronToShelley utxoByron

    ledgerState :: LedgerState (ShelleyEra c)
    ledgerState =
      LedgerState
        { lsUTxOState =
            UTxOState
              { sutxosUtxo = utxoShelley
              , sutxosDeposited = Coin 0
              , sutxosFees = Coin 0
              , sutxosPpups = def
              , sutxosStakeDistr = IStake mempty Map.empty
              }
        , lsDPState =
            DPState
              { dpsDState = def {dsGenDelegs = genDelegs}
              , dpsPState = def
              }
        }
