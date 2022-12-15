{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-deprecations #-}

module Cardano.Ledger.Shelley.LedgerState.Types where

import Cardano.Ledger.BaseTypes (
  BlocksMade (..),
  StrictMaybe (..),
 )
import Cardano.Ledger.Binary (
  FromCBOR (fromCBOR),
  FromSharedCBOR (Share, fromSharedCBOR, fromSharedPlusCBOR),
  Interns,
  ToCBOR (toCBOR),
  decodeRecordNamed,
  decodeRecordNamedT,
  encodeListLen,
  fromSharedLensCBOR,
 )
import Cardano.Ledger.Binary.Coders (Decode (From, RecD), decode, (<!))
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core
import Cardano.Ledger.Credential (Credential (..), Ptr (..))
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.DPState (DPState)
import Cardano.Ledger.EpochBoundary (
  SnapShots (..),
 )
import Cardano.Ledger.Keys (
  KeyHash (..),
  KeyPair, -- deprecated
  KeyRole (..),
 )
import Cardano.Ledger.PoolDistr (PoolDistr (..))
import Cardano.Ledger.SafeHash (HashAnnotated)
import Cardano.Ledger.Shelley.Era (ShelleyEra)
import Cardano.Ledger.Shelley.PParams (PPUPState (..))
import Cardano.Ledger.Shelley.PoolRank (
  NonMyopic (..),
 )
import Cardano.Ledger.Shelley.RewardUpdate (
  PulsingRewUpdate (..),
 )
import Cardano.Ledger.Shelley.Rules.Ppup (ShelleyPpupPredFailure)
import Cardano.Ledger.Slot (EpochNo (..))
import Cardano.Ledger.TreeDiff (ToExpr)
import Cardano.Ledger.UTxO (UTxO (..))
import Control.DeepSeq (NFData)
import Control.Monad.State.Strict (evalStateT)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Default.Class (Default, def)
import Data.Group (Group, invert)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import GHC.Generics (Generic)
import Lens.Micro (_1, _2)
import NoThunks.Class (NoThunks (..))

-- ==================================

type KeyPairs c = [(KeyPair 'Payment c, KeyPair 'Staking c)]

{-# DEPRECATED KeyPairs "Use `Test.Cardano.Ledger.Core.KeyPair (KeyPairs)` instead" #-}

type RewardAccounts c =
  Map (Credential 'Staking c) Coin

data AccountState = AccountState
  { asTreasury :: !Coin
  , asReserves :: !Coin
  }
  deriving (Show, Eq, Generic)

instance ToCBOR AccountState where
  toCBOR (AccountState t r) =
    encodeListLen 2 <> toCBOR t <> toCBOR r

instance FromCBOR AccountState where
  fromCBOR =
    decodeRecordNamed "AccountState" (const 2) $ AccountState <$> fromCBOR <*> fromCBOR

instance NoThunks AccountState

instance NFData AccountState

data EpochState era = EpochState
  { esAccountState :: !AccountState
  , esSnapshots :: !(SnapShots (EraCrypto era))
  , esLState :: !(LedgerState era)
  , esPrevPp :: !(PParams era)
  , esPp :: !(PParams era)
  , esNonMyopic :: !(NonMyopic (EraCrypto era))
  -- ^ This field, esNonMyopic, does not appear in the formal spec
  -- and is not a part of the protocol. It is only used for providing
  -- data to the stake pool ranking calculation @getNonMyopicMemberRewards@.
  -- See https://hydra.iohk.io/job/Cardano/cardano-ledger/specs.pool-ranking/latest/download-by-type/doc-pdf/pool-ranking
  }
  deriving (Generic)

deriving stock instance
  ( CC.Crypto (EraCrypto era)
  , Show (TxOut era)
  , Show (PParams era)
  , Show (PParamsUpdate era)
  , Show (PPUPStateOrUnit era)
  ) =>
  Show (EpochState era)

deriving stock instance
  ( CC.Crypto (EraCrypto era)
  , Eq (TxOut era)
  , Eq (PParams era)
  , Eq (PParamsUpdate era)
  , Eq (PPUPStateOrUnit era)
  ) =>
  Eq (EpochState era)

instance
  ( Era era
  , NoThunks (TxOut era)
  , NoThunks (Value era)
  , NoThunks (PParams era)
  , NoThunks (PParamsUpdate era)
  , NoThunks (PPUPStateOrUnit era)
  , ToCBOR (TxBody era)
  , ToCBOR (TxOut era)
  , ToCBOR (Value era)
  ) =>
  NoThunks (EpochState era)

instance
  ( Era era
  , NFData (TxOut era)
  , NFData (PParams era)
  , NFData (PParamsUpdate era)
  , NFData (PPUPStateOrUnit era)
  ) =>
  NFData (EpochState era)

instance
  ( Era era
  , ToCBOR (TxOut era)
  , ToCBOR (PParams era)
  , ToCBOR (PParamsUpdate era)
  , ToCBOR (PPUPStateOrUnit era)
  ) =>
  ToCBOR (EpochState era)
  where
  toCBOR EpochState {esAccountState, esLState, esSnapshots, esPrevPp, esPp, esNonMyopic} =
    encodeListLen 6
      <> toCBOR esAccountState
      <> toCBOR esLState -- We get better sharing when encoding ledger state before snaphots
      <> toCBOR esSnapshots
      <> toCBOR esPrevPp
      <> toCBOR esPp
      <> toCBOR esNonMyopic

instance
  ( FromCBOR (Value era)
  , FromCBOR (PParams era)
  , FromCBOR (PParamsUpdate era)
  , FromCBOR (PPUPStateOrUnit era)
  , HashAnnotated (TxBody era) EraIndependentTxBody (EraCrypto era)
  , FromSharedCBOR (TxOut era)
  , Share (TxOut era) ~ Interns (Credential 'Staking (EraCrypto era))
  , Era era
  ) =>
  FromCBOR (EpochState era)
  where
  fromCBOR =
    decodeRecordNamed "EpochState" (const 6) $
      flip evalStateT mempty $ do
        esAccountState <- lift fromCBOR
        esLState <- fromSharedPlusCBOR
        esSnapshots <- fromSharedPlusCBOR
        esPrevPp <- lift fromCBOR
        esPp <- lift fromCBOR
        esNonMyopic <- fromSharedLensCBOR _2
        pure EpochState {esAccountState, esSnapshots, esLState, esPrevPp, esPp, esNonMyopic}

data UpecState era = UpecState
  { currentPp :: !(PParams era)
  -- ^ Current protocol parameters.
  , ppupState :: !(PPUPState era)
  -- ^ State of the protocol update transition system.
  }

deriving stock instance
  ( Show (PPUPState era)
  , Show (PParams era)
  ) =>
  Show (UpecState era)

-- =============================

-- | Incremental Stake, Stake along with possible missed coins from danging Ptrs.
--   Transactions can use Ptrs to refer to a stake credential in a TxOut. The Ptr
--   does not have to point to anything until the epoch boundary, when we compute
--   rewards and aggregate staking information for ranking. This is unusual but legal.
--   In a non incremental system, we use whatever 'legal' Ptrs exist at the epoch
--   boundary. Here we are computing things incrementally, so we need to remember Ptrs
--   that might point to something by the time the epoch boundary is reached. When
--   the epoch boundary is reached we 'resolve' these pointers, to see if any have
--   become non-dangling since the time they were first used in the incremental computation.
data IncrementalStake c = IStake
  { credMap :: !(Map (Credential 'Staking c) Coin)
  , ptrMap :: !(Map Ptr Coin)
  }
  deriving (Generic, Show, Eq, Ord, NoThunks, NFData)

instance CC.Crypto c => ToCBOR (IncrementalStake c) where
  toCBOR (IStake st dangle) =
    encodeListLen 2 <> toCBOR st <> toCBOR dangle

instance CC.Crypto c => FromSharedCBOR (IncrementalStake c) where
  type Share (IncrementalStake c) = Interns (Credential 'Staking c)
  fromSharedCBOR credInterns =
    decodeRecordNamed "Stake" (const 2) $ do
      stake <- fromSharedCBOR (credInterns, mempty)
      IStake stake <$> fromCBOR

instance Semigroup (IncrementalStake c) where
  (IStake a b) <> (IStake c d) = IStake (Map.unionWith (<>) a c) (Map.unionWith (<>) b d)

instance Monoid (IncrementalStake c) where
  mempty = IStake Map.empty Map.empty

instance Data.Group.Group (IncrementalStake c) where
  invert (IStake m1 m2) = IStake (Map.map invert m1) (Map.map invert m2)

instance Default (IncrementalStake c) where
  def = IStake Map.empty Map.empty

-- =============================

type PPUPPredFailure era = PPUPPredFailurePV (ProtVerLow era) era

type family PPUPPredFailurePV pv era where
  PPUPPredFailurePV 1 era = ShelleyPpupPredFailure era
  PPUPPredFailurePV 2 era = ShelleyPpupPredFailure era
  PPUPPredFailurePV 3 era = ShelleyPpupPredFailure era
  PPUPPredFailurePV 4 era = ShelleyPpupPredFailure era
  PPUPPredFailurePV 5 era = ShelleyPpupPredFailure era
  PPUPPredFailurePV 6 era = ShelleyPpupPredFailure era
  PPUPPredFailurePV 7 era = ShelleyPpupPredFailure era
  PPUPPredFailurePV 8 era = ShelleyPpupPredFailure era
  PPUPPredFailurePV _ _ = ()

type PPUPStateOrUnit era = PPUPStateOrUnitPV (ProtVerLow era) era

type family PPUPStateOrUnitPV pv era where
  PPUPStateOrUnitPV 1 era = PPUPState era
  PPUPStateOrUnitPV 2 era = PPUPState era
  PPUPStateOrUnitPV 3 era = PPUPState era
  PPUPStateOrUnitPV 4 era = PPUPState era
  PPUPStateOrUnitPV 5 era = PPUPState era
  PPUPStateOrUnitPV 6 era = PPUPState era
  PPUPStateOrUnitPV 7 era = PPUPState era
  PPUPStateOrUnitPV 8 era = PPUPState era
  PPUPStateOrUnitPV _ _ = ()

-- | There is a serious invariant that we must maintain in the UTxOState.
--   Given (UTxOState utxo _ _ _ istake) it must be the case that
--   istake == (updateStakeDistribution (UTxO Map.empty) (UTxO Map.empty) utxo)
--   Of course computing the RHS of the above equality can be very expensive, so we only
--   use this route in the testing function smartUTxO. But we are very careful, wherever
--   we update the UTxO, we carefully make INCREMENTAL changes to istake to maintain
--   this invariant. This happens in the UTxO rule.
data UTxOState era = UTxOState
  { sutxosUtxo :: !(UTxO era)
  , sutxosDeposited :: !Coin
  , sutxosFees :: !Coin
  , sutxosPpups :: !(PPUPStateOrUnit era)
  , sutxosStakeDistr :: !(IncrementalStake (EraCrypto era))
  }
  deriving (Generic)

instance
  ( Era era
  , NFData (TxOut era)
  , NFData (PParamsUpdate era)
  , NFData (PPUPStateOrUnit era)
  ) =>
  NFData (UTxOState era)

deriving stock instance
  ( CC.Crypto (EraCrypto era)
  , Show (TxOut era)
  , Show (PParamsUpdate era)
  , Show (PPUPStateOrUnit era)
  ) =>
  Show (UTxOState era)

deriving stock instance
  ( CC.Crypto (EraCrypto era)
  , Eq (TxOut era)
  , Eq (PParamsUpdate era)
  , Eq (PPUPStateOrUnit era)
  ) =>
  Eq (UTxOState era)

instance
  ( NoThunks (UTxO era)
  , NoThunks (Value era)
  , NoThunks (PParamsUpdate era)
  , NoThunks (PPUPStateOrUnit era)
  ) =>
  NoThunks (UTxOState era)

instance
  ( Era era
  , ToCBOR (TxOut era)
  , ToCBOR (PParamsUpdate era)
  , ToCBOR (PPUPStateOrUnit era)
  ) =>
  ToCBOR (UTxOState era)
  where
  toCBOR (UTxOState ut dp fs us sd) =
    encodeListLen 5 <> toCBOR ut <> toCBOR dp <> toCBOR fs <> toCBOR us <> toCBOR sd

instance
  ( CC.Crypto (EraCrypto era)
  , FromSharedCBOR (TxOut era)
  , Share (TxOut era) ~ Interns (Credential 'Staking (EraCrypto era))
  , HashAnnotated (TxBody era) EraIndependentTxBody (EraCrypto era)
  , Era era
  , FromCBOR (PParamsUpdate era)
  , FromCBOR (PPUPStateOrUnit era)
  ) =>
  FromSharedCBOR (UTxOState era)
  where
  type
    Share (UTxOState era) =
      Interns (Credential 'Staking (EraCrypto era))
  fromSharedCBOR credInterns =
    decodeRecordNamed "UTxOState" (const 5) $ do
      sutxosUtxo <- fromSharedCBOR credInterns
      sutxosDeposited <- fromCBOR
      sutxosFees <- fromCBOR
      sutxosPpups <- fromCBOR
      sutxosStakeDistr <- fromSharedCBOR credInterns
      pure UTxOState {..}

-- | New Epoch state and environment
data NewEpochState era = NewEpochState
  { nesEL :: !EpochNo
  -- ^ Last epoch
  , nesBprev :: !(BlocksMade (EraCrypto era))
  -- ^ Blocks made before current epoch
  , nesBcur :: !(BlocksMade (EraCrypto era))
  -- ^ Blocks made in current epoch
  , nesEs :: !(EpochState era)
  -- ^ Epoch state before current
  , nesRu :: !(StrictMaybe (PulsingRewUpdate (EraCrypto era)))
  -- ^ Possible reward update
  , nesPd :: !(PoolDistr (EraCrypto era))
  -- ^ Stake distribution within the stake pool
  , stashedAVVMAddresses :: !(StashedAVVMAddresses era)
  -- ^ AVVM addresses to be removed at the end of the Shelley era. Note that
  -- the existence of this field is a hack, related to the transition of UTxO
  -- to disk. We remove AVVM addresses from the UTxO on the Shelley/Allegra
  -- boundary. However, by this point the UTxO will be moved to disk, and
  -- hence doing a scan of the UTxO for AVVM addresses will be expensive. Our
  -- solution to this is to do a scan of the UTxO on the Byron/Shelley
  -- boundary (since Byron UTxO are still on disk), stash the results here,
  -- and then remove them at the Shelley/Allegra boundary.
  --
  -- This is very much an awkward implementation hack, and hence we hide it
  -- from as many places as possible.
  }
  deriving (Generic)

type family StashedAVVMAddresses era where
  StashedAVVMAddresses (ShelleyEra c) = UTxO (ShelleyEra c)
  StashedAVVMAddresses _ = ()

deriving stock instance
  ( CC.Crypto (EraCrypto era)
  , Show (TxOut era)
  , Show (PParams era)
  , Show (StashedAVVMAddresses era)
  , Show (PParamsUpdate era)
  , Show (PPUPStateOrUnit era)
  ) =>
  Show (NewEpochState era)

deriving stock instance
  ( CC.Crypto (EraCrypto era)
  , Eq (TxOut era)
  , Eq (PParams era)
  , Eq (StashedAVVMAddresses era)
  , Eq (PParamsUpdate era)
  , Eq (PPUPStateOrUnit era)
  ) =>
  Eq (NewEpochState era)

instance
  ( Era era
  , NFData (TxOut era)
  , NFData (PParams era)
  , NFData (StashedAVVMAddresses era)
  , NFData (PParamsUpdate era)
  , NFData (PPUPStateOrUnit era)
  ) =>
  NFData (NewEpochState era)

instance
  ( Era era
  , ToCBOR (TxOut era)
  , ToCBOR (PParams era)
  , ToCBOR (StashedAVVMAddresses era)
  , ToCBOR (PParamsUpdate era)
  , ToCBOR (PPUPStateOrUnit era)
  ) =>
  ToCBOR (NewEpochState era)
  where
  toCBOR (NewEpochState e bp bc es ru pd av) =
    encodeListLen 7
      <> toCBOR e
      <> toCBOR bp
      <> toCBOR bc
      <> toCBOR es
      <> toCBOR ru
      <> toCBOR pd
      <> toCBOR av

instance
  ( Era era
  , FromCBOR (PParams era)
  , FromSharedCBOR (TxOut era)
  , Share (TxOut era) ~ Interns (Credential 'Staking (EraCrypto era))
  , FromCBOR (Value era)
  , FromCBOR (StashedAVVMAddresses era)
  , FromCBOR (PParamsUpdate era)
  , FromCBOR (PPUPStateOrUnit era)
  , HashAnnotated (TxBody era) EraIndependentTxBody (EraCrypto era)
  ) =>
  FromCBOR (NewEpochState era)
  where
  fromCBOR = do
    decode $
      RecD NewEpochState
        <! From
        <! From
        <! From
        <! From
        <! From
        <! From
        <! From

instance
  ( Era era
  , NoThunks (BlocksMade (EraCrypto era))
  , NoThunks (EpochState era)
  , NoThunks (PulsingRewUpdate (EraCrypto era))
  , NoThunks (StashedAVVMAddresses era)
  ) =>
  NoThunks (NewEpochState era)

-- | The state associated with a 'Ledger'.
data LedgerState era = LedgerState
  { lsUTxOState :: !(UTxOState era)
  -- ^ The current unspent transaction outputs.
  , lsDPState :: !(DPState (EraCrypto era))
  -- ^ The current delegation state
  }
  deriving (Generic)

deriving stock instance
  ( CC.Crypto (EraCrypto era)
  , Show (TxOut era)
  , Show (PParamsUpdate era)
  , Show (PPUPStateOrUnit era)
  ) =>
  Show (LedgerState era)

deriving stock instance
  ( CC.Crypto (EraCrypto era)
  , Eq (TxOut era)
  , Eq (PParamsUpdate era)
  , Eq (PPUPStateOrUnit era)
  ) =>
  Eq (LedgerState era)

instance
  ( Era era
  , NoThunks (UTxO era)
  , NoThunks (Value era)
  , NoThunks (PParamsUpdate era)
  , NoThunks (PPUPStateOrUnit era)
  ) =>
  NoThunks (LedgerState era)

instance
  ( Era era
  , NFData (TxOut era)
  , NFData (PParamsUpdate era)
  , NFData (PPUPStateOrUnit era)
  ) =>
  NFData (LedgerState era)

instance
  ( Era era
  , ToCBOR (TxOut era)
  , ToCBOR (PParamsUpdate era)
  , ToCBOR (PPUPStateOrUnit era)
  ) =>
  ToCBOR (LedgerState era)
  where
  toCBOR LedgerState {lsUTxOState, lsDPState} =
    encodeListLen 2
      <> toCBOR lsDPState -- encode delegation state first to improve sharing
      <> toCBOR lsUTxOState

instance
  ( Era era
  , HashAnnotated (TxBody era) EraIndependentTxBody (EraCrypto era)
  , FromCBOR (Value era)
  , FromSharedCBOR (TxOut era)
  , Share (TxOut era) ~ Interns (Credential 'Staking (EraCrypto era))
  , FromCBOR (PParamsUpdate era)
  , FromCBOR (PPUPStateOrUnit era)
  ) =>
  FromSharedCBOR (LedgerState era)
  where
  type
    Share (LedgerState era) =
      (Interns (Credential 'Staking (EraCrypto era)), Interns (KeyHash 'StakePool (EraCrypto era)))
  fromSharedPlusCBOR =
    decodeRecordNamedT "LedgerState" (const 2) $ do
      lsDPState <- fromSharedPlusCBOR
      lsUTxOState <- fromSharedLensCBOR _1
      pure LedgerState {lsUTxOState, lsDPState}

-- ====================================================

--------------------------------------------------------------------------------
-- Default instances
--------------------------------------------------------------------------------

instance
  (CC.Crypto (EraCrypto era), Default (PPUPStateOrUnit era)) =>
  Default (UTxOState era)
  where
  def = UTxOState mempty mempty mempty def mempty

instance
  (Default (LedgerState era), Default (PParams era)) =>
  Default (EpochState era)
  where
  def = EpochState def def def def def def

instance Default (UTxOState era) => Default (LedgerState era) where
  def = LedgerState def def

instance Default AccountState where
  def = AccountState (Coin 0) (Coin 0)

-- =============================================================
-- TreeDiff ToExpr instances

instance ToExpr AccountState

instance
  ( ToExpr (TxOut era)
  , ToExpr (PParams era)
  , ToExpr (StashedAVVMAddresses era)
  , ToExpr (PParamsUpdate era)
  , ToExpr (PPUPStateOrUnit era)
  ) =>
  ToExpr (NewEpochState era)

instance
  ( ToExpr (TxOut era)
  , ToExpr (PParams era)
  , ToExpr (PParamsUpdate era)
  , ToExpr (PPUPStateOrUnit era)
  ) =>
  ToExpr (EpochState era)

instance
  ( ToExpr (TxOut era)
  , ToExpr (PParamsUpdate era)
  , ToExpr (PPUPStateOrUnit era)
  ) =>
  ToExpr (LedgerState era)

instance
  ( ToExpr (TxOut era)
  , ToExpr (PParamsUpdate era)
  , ToExpr (PPUPStateOrUnit era)
  ) =>
  ToExpr (UTxOState era)

instance ToExpr (IncrementalStake c)
