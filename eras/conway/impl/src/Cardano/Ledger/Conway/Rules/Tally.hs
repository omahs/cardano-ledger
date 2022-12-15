{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Conway.Rules.Tally () where

import Cardano.Ledger.BaseTypes (ShelleyBase)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Conway.Era (ConwayTALLY)
import Cardano.Ledger.Conway.Governance (GovernanceAction, GovernanceActionId (..), GovernanceActionInfo (..), Vote (..), VoterRole)
import Cardano.Ledger.Core (Era (..))
import Cardano.Ledger.Keys (KeyHash (..), KeyRole (..))
import Cardano.Ledger.Shelley.Tx (TxId (..))
import Control.State.Transition.Extended (STS (..), TRC (..), TransitionRule, judgmentContext)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq, ViewL (..), viewl)
import qualified Data.Sequence as Seq

data GovernanceActionState era = GovernanceActionState
  { gasVotes :: !(Map (VoterRole, KeyHash 'Voting (EraCrypto era)) (Vote era))
  , gasDeposit :: !Coin
  , gasReturnAddr :: !(KeyHash 'Staking (EraCrypto era))
  , gasAction :: !(GovernanceAction era)
  }

newtype TallyState era
  = TallyState
      (Map (GovernanceActionId (EraCrypto era)) (GovernanceActionState era))

newtype TallyEnv era = TallyEnv (TxId (EraCrypto era))

data GovernanceProcedure era
  = VotingProcedure (Vote era)
  | ProposalProcedure (GovernanceActionInfo era)

data TallyPredicateFailure era
  deriving (Eq, Show)

instance Era era => STS (ConwayTALLY era) where
  type State (ConwayTALLY era) = TallyState era
  type Signal (ConwayTALLY era) = Seq (GovernanceProcedure era)
  type Environment (ConwayTALLY era) = TallyEnv era
  type BaseM (ConwayTALLY era) = ShelleyBase
  type PredicateFailure (ConwayTALLY era) = TallyPredicateFailure era
  type Event (ConwayTALLY era) = ()

  initialRules = []

  transitionRules = [tallyTransition]

makeGovAction :: GovernanceActionInfo era -> GovernanceActionState era
makeGovAction GovernanceActionInfo {..} =
  GovernanceActionState
    { gasVotes = mempty
    , gasDeposit = gaiDepositAmount
    , gasReturnAddr = gaiRewardAddress
    , gasAction = gaiAction
    }

addVote ::
  GovernanceActionId (EraCrypto era) ->
  Vote era ->
  TallyState era ->
  TallyState era
addVote gaid vote@Vote {..} (TallyState st) =
  TallyState $
    Map.update (pure . updateVote) gaid st
  where
    updateVote GovernanceActionState {..} =
      GovernanceActionState
        { gasVotes = Map.insert (voteRole, voteRoleKeyHash) vote gasVotes
        , ..
        }

addAction ::
  GovernanceActionId (EraCrypto era) ->
  GovernanceActionInfo era ->
  TallyState era ->
  TallyState era
addAction gaid gai (TallyState st) =
  TallyState $
    Map.insert gaid (makeGovAction gai) st

tallyTransition :: TransitionRule (ConwayTALLY era)
tallyTransition = do
  TRC (TallyEnv txid, st, govProcedures) <- judgmentContext

  let updateState st' EmptyL = pure st'
      updateState st' ((x, idx) :< xs) = do
        let st'' =
              let gaid = GovernanceActionId txid idx
               in case x of
                    VotingProcedure vote -> addVote gaid vote st'
                    ProposalProcedure action -> addAction gaid action st'
        updateState st'' $ viewl xs

  updateState st . viewl $ Seq.zip govProcedures [0 ..]
