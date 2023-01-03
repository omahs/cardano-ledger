{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Conway.Rules.Ledger (
  ConwayLEDGER,
  ConwayLedgerPredFailure (..),
) where

import Cardano.Crypto.DSIGN (DSIGNAlgorithm (..))
import Cardano.Crypto.Hash.Class (Hash)
import Cardano.Ledger.Alonzo.Rules (AlonzoUtxowEvent)
import Cardano.Ledger.Alonzo.Scripts (AlonzoScript, CostModels (..))
import Cardano.Ledger.Alonzo.UTxO (AlonzoScriptsNeeded (..))
import Cardano.Ledger.Babbage.Core (BabbageEraTxBody)
import Cardano.Ledger.Babbage.Rules (BabbageUTXOW, BabbageUtxowPredFailure)
import Cardano.Ledger.Babbage.Tx (IsValid (..))
import Cardano.Ledger.Babbage.TxBody (BabbageTxOut (..))
import Cardano.Ledger.BaseTypes (ShelleyBase)
import Cardano.Ledger.Block (txid)
import Cardano.Ledger.Conway.Core (ConwayEraTxBody (..))
import Cardano.Ledger.Conway.Era (ConwayLEDGER)
import Cardano.Ledger.Conway.Rules.Tally (GovernanceProcedure (..), TallyEnv (..), TallyState (..))
import Cardano.Ledger.Conway.Tx (AlonzoEraTx (..))
import Cardano.Ledger.Core (Era (..), EraIndependentTxBody, EraPParams (..), EraRule, EraScript (..), EraTx (..), EraTxOut (..))
import Cardano.Ledger.Crypto (Crypto (..))
import Cardano.Ledger.Shelley.Core (ShelleyEraTxBody (..))
import Cardano.Ledger.Shelley.Delegation.Certificates (DCert)
import Cardano.Ledger.Shelley.LedgerState (DPState (..), DState (..), PPUPStateOrUnit, UTxOState (..), obligationDPState)
import Cardano.Ledger.Shelley.Rules (
  DelegsEnv (..),
  DelplEnv (..),
  LedgerEnv (..),
  ShelleyDELEGS,
  ShelleyLEDGERS,
  ShelleyLedgerEvent (..),
  UtxoEnv (..),
 )
import Cardano.Ledger.UTxO (EraUTxO (..))
import Control.State.Transition.Extended (
  Assertion (..),
  AssertionViolation (..),
  Embed (..),
  STS (..),
  TRC (..),
  TransitionRule,
  judgmentContext,
  trans,
 )
import Data.Kind (Type)
import Data.Sequence (Seq)
import qualified Data.Sequence.Strict as StrictSeq
import GHC.Generics (Generic (..))
import GHC.Records (HasField)
import Lens.Micro ((^.))

-- | The state associated with a 'Ledger'.
data ConwayLedgerState era = ConwayLedgerState
  { clsUTxOState :: !(UTxOState era)
  -- ^ The current unspent transaction outputs.
  , clsDPState :: !(DPState (EraCrypto era))
  -- ^ The current delegation state
  , clsTallyState :: !(TallyState era)
  }
  deriving (Generic)

deriving instance
  ( Era era
  , Show (PParamsUpdate era)
  , Show (PPUPStateOrUnit era)
  , Show (TxOut era)
  , Show (TallyState era)
  ) =>
  Show (ConwayLedgerState era)

data ConwayLedgerPredFailure era
  = UtxowFailure (PredicateFailure (EraRule "UTXOW" era)) -- Subtransition Failures
  | DelegsFailure (PredicateFailure (EraRule "DELEGS" era)) -- Subtransition Failures
  | TallyFailure (PredicateFailure (EraRule "TALLY" era)) -- Subtransition Failures
  deriving (Generic)

deriving instance
  ( Eq (PredicateFailure (EraRule "UTXOW" era))
  , Eq (PredicateFailure (EraRule "DELEGS" era))
  , Eq (PredicateFailure (EraRule "TALLY" era))
  ) =>
  Eq (ConwayLedgerPredFailure era)

deriving instance
  ( Show (PredicateFailure (EraRule "UTXOW" era))
  , Show (PredicateFailure (EraRule "DELEGS" era))
  , Show (PredicateFailure (EraRule "TALLY" era))
  ) =>
  Show (ConwayLedgerPredFailure era)

instance
  ( Era era
  , Embed (EraRule "UTXOW" era) (ConwayLEDGER era)
  , Embed (EraRule "TALLY" era) (ConwayLEDGER era)
  , Embed (EraRule "DELEGS" era) (ConwayLEDGER era)
  , AlonzoEraTx era
  , State (EraRule "UTXOW" era) ~ UTxOState era
  , Environment (EraRule "UTXOW" era) ~ UtxoEnv era
  , Environment (EraRule "DELEGS" era) ~ DelegsEnv era
  , State (EraRule "DELEGS" era) ~ DPState (EraCrypto era)
  , Signal (EraRule "UTXOW" era) ~ Tx era
  , Signal (EraRule "DELEGS" era) ~ Seq (DCert (EraCrypto era))
  , Signal (EraRule "TALLY" era) ~ Seq (GovernanceProcedure era)
  , Environment (EraRule "TALLY" era) ~ TallyEnv era
  , State (EraRule "TALLY" era) ~ TallyState era
  , Show (ConwayLedgerState era)
  , ConwayEraTxBody era
  ) =>
  STS (ConwayLEDGER era)
  where
  type State (ConwayLEDGER era) = ConwayLedgerState era
  type Signal (ConwayLEDGER era) = Tx era
  type Environment (ConwayLEDGER era) = LedgerEnv era
  type BaseM (ConwayLEDGER era) = ShelleyBase
  type PredicateFailure (ConwayLEDGER era) = ConwayLedgerPredFailure era
  type Event (ConwayLEDGER era) = ShelleyLedgerEvent era

  initialRules = []
  transitionRules = [ledgerTransition @ConwayLEDGER]

  renderAssertionViolation AssertionViolation {avSTS, avMsg, avCtx, avState} =
    "AssertionViolation ("
      <> avSTS
      <> "): "
      <> avMsg
      <> "\n"
      <> show avCtx
      <> "\n"
      <> show avState

  assertions =
    [ PostCondition
        "Deposit pot must equal obligation"
        ( \(TRC (_, _, _))
           (ConwayLedgerState utxoSt dpstate _tallySt) ->
              obligationDPState dpstate
                == sutxosDeposited utxoSt
        )
    ]

-- =======================================

ledgerTransition ::
  forall (someLEDGER :: Type -> Type) era.
  ( Signal (someLEDGER era) ~ Tx era
  , State (someLEDGER era) ~ ConwayLedgerState era
  , Environment (someLEDGER era) ~ LedgerEnv era
  , Embed (EraRule "UTXOW" era) (someLEDGER era)
  , Embed (EraRule "TALLY" era) (someLEDGER era)
  , Embed (EraRule "DELEGS" era) (someLEDGER era)
  , Environment (EraRule "DELEGS" era) ~ DelegsEnv era
  , State (EraRule "DELEGS" era) ~ DPState (EraCrypto era)
  , Signal (EraRule "DELEGS" era) ~ Seq (DCert (EraCrypto era))
  , Environment (EraRule "UTXOW" era) ~ UtxoEnv era
  , State (EraRule "UTXOW" era) ~ UTxOState era
  , Signal (EraRule "UTXOW" era) ~ Tx era
  , Signal (EraRule "TALLY" era) ~ Seq (GovernanceProcedure era)
  , AlonzoEraTx era
  , Environment (EraRule "TALLY" era) ~ TallyEnv era
  , State (EraRule "TALLY" era) ~ TallyState era
  , ConwayEraTxBody era
  ) =>
  TransitionRule (someLEDGER era)
ledgerTransition = do
  TRC (LedgerEnv slot txIx pp account, ConwayLedgerState utxoSt dpstate tallySt, tx) <- judgmentContext
  let txBody = tx ^. bodyTxL

  dpstate' <-
    if tx ^. isValidTxL == IsValid True
      then
        trans @(EraRule "DELEGS" era) $
          TRC
            ( DelegsEnv slot txIx pp tx account
            , dpstate
            , StrictSeq.fromStrict $ txBody ^. certsTxBodyG
            )
      else pure dpstate

  let DPState dstate _pstate = dpstate
      genDelegs = dsGenDelegs dstate

  let govProcedures =
        mconcat
          [ fmap ProposalProcedure $ txBody ^. govActionsTxBodyL
          , fmap VotingProcedure $ txBody ^. votesTxBodyL
          ]
  tallySt' <-
    trans @(EraRule "TALLY" era) $
      TRC
        ( TallyEnv $ txid txBody
        , tallySt
        , StrictSeq.fromStrict govProcedures
        )

  utxoSt' <-
    trans @(EraRule "UTXOW" era) $
      TRC
        ( UtxoEnv @era slot pp dpstate genDelegs
        , utxoSt
        , tx
        )
  pure $ ConwayLedgerState utxoSt' dpstate' tallySt'

instance
  ( Signable (DSIGN (EraCrypto era)) (Hash (HASH (EraCrypto era)) EraIndependentTxBody)
  , BaseM (BabbageUTXOW era) ~ ShelleyBase
  , AlonzoEraTx era
  , EraUTxO era
  , BabbageEraTxBody era
  , HasField "_costmdls" (PParams era) CostModels
  , Embed (EraRule "UTXO" era) (BabbageUTXOW era)
  , State (EraRule "UTXO" era) ~ UTxOState era
  , Environment (EraRule "UTXO" era) ~ UtxoEnv era
  , Script era ~ AlonzoScript era
  , TxOut era ~ BabbageTxOut era
  , ScriptsNeeded era ~ AlonzoScriptsNeeded era
  , Signal (EraRule "UTXO" era) ~ Tx era
  , PredicateFailure (EraRule "UTXOW" era) ~ BabbageUtxowPredFailure era
  , Event (EraRule "UTXOW" era) ~ AlonzoUtxowEvent era
  , STS (BabbageUTXOW era)
  , PredicateFailure (BabbageUTXOW era) ~ BabbageUtxowPredFailure era
  , Event (BabbageUTXOW era) ~ AlonzoUtxowEvent era
  ) =>
  Embed (BabbageUTXOW era) (ConwayLEDGER era)
  where
  wrapFailed = UtxowFailure @era
  wrapEvent = UtxowEvent

instance
  ( EraTx era
  , ShelleyEraTxBody era
  , Embed (EraRule "DELPL" era) (ShelleyDELEGS era)
  , State (EraRule "DELPL" era) ~ DPState (EraCrypto era)
  , Environment (EraRule "DELPL" era) ~ DelplEnv era
  , Signal (EraRule "DELPL" era) ~ DCert (EraCrypto era)
  ) =>
  Embed (ShelleyDELEGS era) (ConwayLEDGER era)
  where
  wrapFailed = undefined
  wrapEvent = undefined

instance
  ( Embed (EraRule "UTXOW" era) (ConwayLEDGER era)
  , Embed (EraRule "DELEGS" era) (ConwayLEDGER era)
  , Embed (EraRule "TALLY" era) (ConwayLEDGER era)
  , AlonzoEraTx era
  , Show (PPUPStateOrUnit era)
  , ConwayEraTxBody era
  , Environment (EraRule "UTXOW" era) ~ UtxoEnv era
  , Environment (EraRule "DELEGS" era) ~ DelegsEnv era
  , Environment (EraRule "TALLY" era) ~ TallyEnv era
  , Signal (EraRule "UTXOW" era) ~ Tx era
  , Signal (EraRule "DELEGS" era) ~ Seq (DCert (EraCrypto era))
  , Signal (EraRule "TALLY" era) ~ Seq (GovernanceProcedure era)
  , State (EraRule "UTXOW" era) ~ UTxOState era
  , State (EraRule "DELEGS" era) ~ DPState (EraCrypto era)
  , State (EraRule "TALLY" era) ~ TallyState era
  ) =>
  Embed (ConwayLEDGER era) (ShelleyLEDGERS era)
  where
  wrapFailed = undefined
  wrapEvent = undefined
