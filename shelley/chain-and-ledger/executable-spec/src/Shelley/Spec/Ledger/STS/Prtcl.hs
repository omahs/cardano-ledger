{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.STS.Prtcl
  ( PRTCL,
    State,
    PrtclEnv (..),
    PrtclState (..),
    PredicateFailure (..),
    PrtlSeqFailure (..),
    prtlSeqChecks,
  )
where

import Cardano.Binary
  ( FromCBOR (fromCBOR),
    ToCBOR (toCBOR),
    encodeListLen,
  )
import qualified Cardano.Crypto.VRF as VRF
import Cardano.Ledger.Crypto (Crypto, VRF)
import Cardano.Prelude (MonadError (..), NoUnexpectedThunks (..), unless)
import Cardano.Slotting.Slot (WithOrigin (..))
import Control.State.Transition
import Data.Map.Strict (Map)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Shelley.Spec.Ledger.BaseTypes
  ( Nonce,
    Seed,
    ShelleyBase,
  )
import Shelley.Spec.Ledger.BlockChain
  ( BHBody (..),
    BHeader (..),
    LastAppliedBlock (..),
    PrevHash,
    bhbody,
    bnonce,
    lastAppliedHash,
  )
import Shelley.Spec.Ledger.Delegation.Certificates (PoolDistr)
import Shelley.Spec.Ledger.Keys
  ( DSignable,
    GenDelegs (..),
    KESignable,
    KeyHash,
    KeyRole (..),
    VRFSignable,
  )
import Shelley.Spec.Ledger.OCert (OCertSignable)
import Shelley.Spec.Ledger.OverlaySchedule (OverlaySchedule)
import Shelley.Spec.Ledger.STS.Overlay (OVERLAY, OverlayEnv (..))
import Shelley.Spec.Ledger.STS.Updn (UPDN, UpdnEnv (..), UpdnState (..))
import Shelley.Spec.Ledger.Serialization (decodeRecordNamed)
import Shelley.Spec.Ledger.Slot (BlockNo, SlotNo)

data PRTCL crypto

data PrtclState crypto
  = PrtclState
      !(Map (KeyHash 'BlockIssuer crypto) Word64)
      -- ^ Operation Certificate counters
      !Nonce
      -- ^ Evolving nonce
      !Nonce
      -- ^ Candidate nonce
  deriving (Generic, Show, Eq)

instance Crypto crypto => ToCBOR (PrtclState crypto) where
  toCBOR (PrtclState m n1 n2) =
    mconcat
      [ encodeListLen 3,
        toCBOR m,
        toCBOR n1,
        toCBOR n2
      ]

instance Crypto crypto => FromCBOR (PrtclState crypto) where
  fromCBOR =
    decodeRecordNamed
      "PrtclState"
      (const 3)
      ( PrtclState
          <$> fromCBOR
          <*> fromCBOR
          <*> fromCBOR
      )

instance Crypto crypto => NoUnexpectedThunks (PrtclState crypto)

data PrtclEnv crypto
  = PrtclEnv
      (OverlaySchedule crypto)
      (PoolDistr crypto)
      (GenDelegs crypto)
      Nonce
  deriving (Generic)

instance NoUnexpectedThunks (PrtclEnv crypto)

instance
  ( Crypto crypto,
    DSignable crypto (OCertSignable crypto),
    KESignable crypto (BHBody crypto),
    VRFSignable crypto Seed
  ) =>
  STS (PRTCL crypto)
  where
  type
    State (PRTCL crypto) =
      PrtclState crypto

  type
    Signal (PRTCL crypto) =
      BHeader crypto

  type
    Environment (PRTCL crypto) =
      PrtclEnv crypto

  type BaseM (PRTCL crypto) = ShelleyBase

  data PredicateFailure (PRTCL crypto)
    = OverlayFailure (PredicateFailure (OVERLAY crypto)) -- Subtransition Failures
    | UpdnFailure (PredicateFailure (UPDN crypto)) -- Subtransition Failures
    deriving (Generic)

  initialRules = []

  transitionRules = [prtclTransition]

deriving instance (VRF.VRFAlgorithm (VRF crypto)) => Show (PredicateFailure (PRTCL crypto))

deriving instance (VRF.VRFAlgorithm (VRF crypto)) => Eq (PredicateFailure (PRTCL crypto))

prtclTransition ::
  forall crypto.
  ( Crypto crypto,
    DSignable crypto (OCertSignable crypto),
    KESignable crypto (BHBody crypto),
    VRFSignable crypto Seed
  ) =>
  TransitionRule (PRTCL crypto)
prtclTransition = do
  TRC
    ( PrtclEnv osched pd dms eta0,
      PrtclState cs etaV etaC,
      bh
      ) <-
    judgmentContext
  let bhb = bhbody bh
      slot = bheaderSlotNo bhb
      eta = bnonce bhb

  UpdnState etaV' etaC' <-
    trans @(UPDN crypto) $
      TRC
        ( UpdnEnv eta,
          UpdnState etaV etaC,
          slot
        )
  cs' <-
    trans @(OVERLAY crypto) $
      TRC (OverlayEnv osched pd dms eta0, cs, bh)

  pure $
    PrtclState
      cs'
      etaV'
      etaC'

instance (Crypto crypto) => NoUnexpectedThunks (PredicateFailure (PRTCL crypto))

instance
  ( Crypto crypto,
    DSignable crypto (OCertSignable crypto),
    KESignable crypto (BHBody crypto),
    VRFSignable crypto Seed
  ) =>
  Embed (OVERLAY crypto) (PRTCL crypto)
  where
  wrapFailed = OverlayFailure

instance
  ( Crypto crypto,
    DSignable crypto (OCertSignable crypto),
    KESignable crypto (BHBody crypto),
    VRFSignable crypto Seed
  ) =>
  Embed (UPDN crypto) (PRTCL crypto)
  where
  wrapFailed = UpdnFailure

data PrtlSeqFailure crypto
  = WrongSlotIntervalPrtclSeq
      SlotNo
      -- ^ Last slot number.
      SlotNo
      -- ^ Current slot number.
  | WrongBlockNoPrtclSeq
      (WithOrigin (LastAppliedBlock crypto))
      -- ^ Last applied block.
      BlockNo
      -- ^ Current block number.
  | WrongBlockSequencePrtclSeq
      (PrevHash crypto)
      -- ^ Last applied hash
      (PrevHash crypto)
      -- ^ Current block's previous hash
  deriving (Show, Eq, Generic)

instance Crypto crypto => NoUnexpectedThunks (PrtlSeqFailure crypto)

prtlSeqChecks ::
  (MonadError (PrtlSeqFailure crypto) m, Crypto crypto) =>
  WithOrigin (LastAppliedBlock crypto) ->
  BHeader crypto ->
  m ()
prtlSeqChecks lab bh =
  case lab of
    Origin -> pure ()
    At (LastAppliedBlock bL sL _) -> do
      unless (sL < slot) . throwError $ WrongSlotIntervalPrtclSeq sL slot
      unless (bL + 1 == bn) . throwError $ WrongBlockNoPrtclSeq lab bn
      unless (ph == bheaderPrev bhb) . throwError $ WrongBlockSequencePrtclSeq ph (bheaderPrev bhb)
  where
    bhb = bhbody bh
    bn = bheaderBlockNo bhb
    slot = bheaderSlotNo bhb
    ph = lastAppliedHash lab
