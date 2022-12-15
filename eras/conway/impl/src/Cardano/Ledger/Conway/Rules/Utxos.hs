{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Conway.Rules.Utxos (ConwayUTXOS) where

import Cardano.Ledger.Alonzo.Rules (AlonzoUtxoEvent (..), AlonzoUtxoPredFailure (..), AlonzoUtxosEvent, AlonzoUtxosPredFailure)
import Cardano.Ledger.Alonzo.Scripts (AlonzoScript)
import Cardano.Ledger.Alonzo.Tx (AlonzoTx (..))
import Cardano.Ledger.Babbage.Rules (BabbageUTXO, BabbageUtxoPredFailure (..))
import Cardano.Ledger.BaseTypes (ShelleyBase)
import Cardano.Ledger.Conway.Era (ConwayUTXOS)
import Cardano.Ledger.Conway.TxOut (BabbageTxOut (..))
import Cardano.Ledger.Core (Era (..), EraPParams (..), EraRule, EraScript (..), EraTxOut (..), Value)
import Cardano.Ledger.Mary.Value (MaryValue (..))
import Cardano.Ledger.Shelley.LedgerState (PPUPPredFailure, PPUPStateOrUnit, UTxOState)
import Cardano.Ledger.Shelley.Rules (UtxoEnv (..))
import Control.State.Transition.Extended (Embed (..), STS (..))
import Data.Default (Default)

instance
  ( EraScript era
  , TxOut era ~ BabbageTxOut era
  , Value era ~ MaryValue (EraCrypto era)
  , Script era ~ AlonzoScript era
  , Eq (PPUPPredFailure era)
  , Show (PPUPPredFailure era)
  , Eq (PParamsUpdate era)
  , Show (PParamsUpdate era)
  , Default (PPUPStateOrUnit era)
  , Eq (PPUPStateOrUnit era)
  , Show (PPUPStateOrUnit era)
  ) =>
  STS (ConwayUTXOS era)
  where
  type BaseM (ConwayUTXOS era) = ShelleyBase
  type Environment (ConwayUTXOS era) = UtxoEnv era
  type State (ConwayUTXOS era) = UTxOState era
  type Signal (ConwayUTXOS era) = AlonzoTx era
  type PredicateFailure (ConwayUTXOS era) = AlonzoUtxosPredFailure era
  type Event (ConwayUTXOS era) = AlonzoUtxosEvent era

  transitionRules = []

instance
  ( TxOut era ~ BabbageTxOut era
  , Value era ~ MaryValue (EraCrypto era)
  , Script era ~ AlonzoScript era
  , PredicateFailure (EraRule "UTXOS" era) ~ AlonzoUtxosPredFailure era
  , Event (EraRule "UTXOS" era) ~ AlonzoUtxosEvent era
  , EraScript era
  , Default (PPUPStateOrUnit era)
  , Eq (PPUPStateOrUnit era)
  , Show (PPUPStateOrUnit era)
  , Eq (PPUPPredFailure era)
  , Show (PPUPPredFailure era)
  , Eq (PParamsUpdate era)
  , Show (PParamsUpdate era)
  ) =>
  Embed (ConwayUTXOS era) (BabbageUTXO era)
  where
  wrapFailed = AlonzoInBabbageUtxoPredFailure . UtxosFailure
  wrapEvent = UtxosEvent
