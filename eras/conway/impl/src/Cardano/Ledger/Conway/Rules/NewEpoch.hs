{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Conway.Rules.NewEpoch (
  ConwayNEWEPOCH,
  ConwayNewEpochPredFailure (..),
  ConwayNewEpochEvent (..),
)
where

import Cardano.Ledger.BaseTypes (
  BlocksMade (BlocksMade),
  ProtVer,
  ShelleyBase,
  StrictMaybe (SJust, SNothing),
 )
import Cardano.Ledger.Coin (toDeltaCoin)
import Cardano.Ledger.Conway.Era (ConwayENACTMENT, ConwayEPOCH, ConwayNEWEPOCH)
import Cardano.Ledger.Conway.Rules.Enactment ()
import Cardano.Ledger.Conway.Rules.Epoch (ConwayEpochEvent)
import Cardano.Ledger.Core
import Cardano.Ledger.Credential (Credential)
import Cardano.Ledger.EpochBoundary
import Cardano.Ledger.Keys (KeyRole (..))
import Cardano.Ledger.PoolDistr (PoolDistr (..))
import Cardano.Ledger.Rules.ValidationMode (Inject (..))
import Cardano.Ledger.Shelley.AdaPots (AdaPots (..), totalAdaPotsES)
import Cardano.Ledger.Shelley.LedgerState
import Cardano.Ledger.Shelley.Rewards (sumRewards)
import Cardano.Ledger.Shelley.Rules (
  RupdEvent (..),
  ShelleyEpochPredFailure,
  ShelleyNewEpochPredFailure,
  ShelleyTICK,
  ShelleyTickEvent (..),
  ShelleyTickPredFailure (..),
 )
import qualified Cardano.Ledger.Shelley.Rules as Shelley
import Cardano.Ledger.Slot (EpochNo (EpochNo))
import qualified Cardano.Ledger.Val as Val
import Control.State.Transition
import Data.Default (Default (..))
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import GHC.Records (HasField)

data ConwayNewEpochPredFailure era
  = EpochFailure (PredicateFailure (EraRule "EPOCH" era)) -- Subtransition Failures
  | CorruptRewardUpdate
      !(RewardUpdate (EraCrypto era)) -- The reward update which violates an invariant

deriving instance
  Eq (PredicateFailure (EraRule "EPOCH" era)) =>
  Eq (ConwayNewEpochPredFailure era)

deriving instance
  Show (PredicateFailure (EraRule "EPOCH" era)) =>
  Show (ConwayNewEpochPredFailure era)

data ConwayNewEpochEvent era
  = DeltaRewardEvent (Event (EraRule "RUPD" era))
  | RestrainedRewards
      EpochNo
      (Map.Map (Credential 'Staking (EraCrypto era)) (Set (Reward (EraCrypto era))))
      (Set (Credential 'Staking (EraCrypto era)))
  | TotalRewardEvent EpochNo (Map.Map (Credential 'Staking (EraCrypto era)) (Set (Reward (EraCrypto era))))
  | EpochEvent (Event (EraRule "EPOCH" era))
  | TotalAdaPotsEvent AdaPots

instance
  ( EraTxOut era
  , Embed (EraRule "EPOCH" era) (ConwayNEWEPOCH era)
  , Embed (EraRule "ENACTMENT" era) (ConwayNEWEPOCH era)
  , Event (EraRule "RUPD" era) ~ RupdEvent (EraCrypto era)
  , Environment (EraRule "EPOCH" era) ~ ()
  , State (EraRule "EPOCH" era) ~ EpochState era
  , Signal (EraRule "EPOCH" era) ~ EpochNo
  , Default (EpochState era)
  , Signal (EraRule "ENACTMENT" era) ~ EpochNo
  , Environment (EraRule "ENACTMENT" era) ~ ()
  , State (EraRule "ENACTMENT" era) ~ EpochState era
  , HasField "_protocolVersion" (PParams era) ProtVer
  , Default (PParams era)
  , Default (StashedAVVMAddresses era)
  , Default (PPUPStateOrUnit era)
  ) =>
  STS (ConwayNEWEPOCH era)
  where
  type State (ConwayNEWEPOCH era) = NewEpochState era
  type Signal (ConwayNEWEPOCH era) = EpochNo
  type Environment (ConwayNEWEPOCH era) = ()
  type BaseM (ConwayNEWEPOCH era) = ShelleyBase
  type PredicateFailure (ConwayNEWEPOCH era) = ConwayNewEpochPredFailure era
  type Event (ConwayNEWEPOCH era) = ConwayNewEpochEvent era

  initialRules =
    [ pure $
        NewEpochState
          (EpochNo 0)
          (BlocksMade Map.empty)
          (BlocksMade Map.empty)
          def
          SNothing
          (PoolDistr Map.empty)
          def
    ]

  transitionRules = [newEpochTransition]

instance
  ( Era era
  , Default (PPUPStateOrUnit era)
  , Default (PParams era)
  ) =>
  Embed (ConwayENACTMENT era) (ConwayNEWEPOCH era)
  where
  wrapEvent = undefined
  wrapFailed = undefined

newEpochTransition ::
  forall era.
  ( EraTxOut era
  , Embed (EraRule "EPOCH" era) (ConwayNEWEPOCH era)
  , Environment (EraRule "EPOCH" era) ~ ()
  , State (EraRule "EPOCH" era) ~ EpochState era
  , Signal (EraRule "EPOCH" era) ~ EpochNo
  , Default (PParams era)
  , Default (StashedAVVMAddresses era)
  , Event (EraRule "RUPD" era) ~ RupdEvent (EraCrypto era)
  , Embed (EraRule "ENACTMENT" era) (ConwayNEWEPOCH era)
  , State (EraRule "ENACTMENT" era) ~ EpochState era
  , Environment (EraRule "ENACTMENT" era) ~ ()
  , Signal (EraRule "ENACTMENT" era) ~ EpochNo
  , Default (PPUPStateOrUnit era)
  ) =>
  TransitionRule (ConwayNEWEPOCH era)
newEpochTransition = do
  TRC
    ( _
      , src@(NewEpochState (EpochNo eL) _ bcur es ru _pd _)
      , e@(EpochNo e_)
      ) <-
    judgmentContext
  if e_ /= eL + 1
    then pure src
    else do
      es' <- case ru of
        SNothing -> (pure es)
        SJust p@(Pulsing _ _) -> do
          (ans, event) <- liftSTS (completeRupd p)
          tellReward (DeltaRewardEvent (RupdEvent e event))
          (updateRewards es e ans)
        SJust (Complete ru') -> updateRewards es e ru'
      es'' <- trans @(EraRule "EPOCH" era) $ TRC ((), es', e)
      es''' <- trans @(EraRule "ENACTMENT" era) $ TRC ((), es'', e)
      let adaPots = totalAdaPotsES es'''
      tellEvent $ TotalAdaPotsEvent adaPots
      let ss = esSnapshots es'''
          pd' = calculatePoolDistr (ssStakeSet ss)
      pure $
        src
          { nesEL = e
          , nesBprev = bcur
          , nesBcur = BlocksMade mempty
          , nesEs = es'''
          , nesRu = SNothing
          , nesPd = pd'
          }

-- | tell a RupdEvent as a DeltaRewardEvent only if the map is non-empty
tellReward ::
  (Event (EraRule "RUPD" era) ~ RupdEvent (EraCrypto era)) =>
  ConwayNewEpochEvent era ->
  Rule (ConwayNEWEPOCH era) rtype ()
tellReward (DeltaRewardEvent (RupdEvent _ m)) | Map.null m = pure ()
tellReward x = tellEvent x

-- ===========================================

updateRewards ::
  (HasField "_protocolVersion" (PParams era) ProtVer) =>
  EpochState era ->
  EpochNo ->
  RewardUpdate (EraCrypto era) ->
  Rule (ConwayNEWEPOCH era) 'Transition (EpochState era)
updateRewards es e ru'@(RewardUpdate dt dr rs_ df _) = do
  let totRs = sumRewards (esPrevPp es) rs_
  Val.isZero (dt <> (dr <> toDeltaCoin totRs <> df)) ?! CorruptRewardUpdate ru'
  let (!es', filtered) = applyRUpdFiltered ru' es
  tellEvent $ RestrainedRewards e (frShelleyIgnored filtered) (frUnregistered filtered)
  -- This event (which is only generated once per epoch) must be generated even if the
  -- map is empty (db-sync depends on it).
  tellEvent $ TotalRewardEvent e (frRegistered filtered)
  pure es'

instance
  ( STS (ConwayNEWEPOCH era)
  , PredicateFailure (EraRule "NEWEPOCH" era) ~ ConwayNewEpochPredFailure era
  , Event (EraRule "NEWEPOCH" era) ~ ConwayNewEpochEvent era
  ) =>
  Embed (ConwayNEWEPOCH era) (ShelleyTICK era)
  where
  wrapFailed = NewEpochFailure
  wrapEvent = TickNewEpochEvent

instance
  ( STS (ConwayEPOCH era)
  , PredicateFailure (EraRule "EPOCH" era) ~ ShelleyEpochPredFailure era
  , Event (EraRule "EPOCH" era) ~ ConwayEpochEvent era
  ) =>
  Embed (ConwayEPOCH era) (ConwayNEWEPOCH era)
  where
  wrapFailed = EpochFailure
  wrapEvent = EpochEvent

instance Inject (ConwayNewEpochPredFailure era) (ShelleyNewEpochPredFailure era) where
  inject (EpochFailure x) = Shelley.EpochFailure x
  inject (CorruptRewardUpdate x) = Shelley.CorruptRewardUpdate x
