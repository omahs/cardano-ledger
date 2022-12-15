{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Conway.Rules.Enactment (
  ConwayENACTMENT,
)
where

import Cardano.Ledger.BaseTypes (EpochNo (..), ShelleyBase)
import Cardano.Ledger.Conway.Era (ConwayENACTMENT)
import Cardano.Ledger.Core (EraPParams (..))
import Cardano.Ledger.Era (Era)
import Cardano.Ledger.Shelley.LedgerState (EpochState (..), PPUPStateOrUnit)
import Control.State.Transition.Extended (STS (..))
import Data.Default (Default)

instance
  ( Era era
  , Default (PPUPStateOrUnit era)
  , Default (PParams era)
  ) =>
  STS (ConwayENACTMENT era)
  where
  type Environment (ConwayENACTMENT era) = ()
  type PredicateFailure (ConwayENACTMENT era) = ()
  type Signal (ConwayENACTMENT era) = EpochNo
  type State (ConwayENACTMENT era) = EpochState era
  type BaseM (ConwayENACTMENT era) = ShelleyBase

  transitionRules = undefined -- TODO once the specification is done
