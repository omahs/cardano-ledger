{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Cardano.Chain.UTxO.UTxOConfiguration (
  UTxOConfiguration (..),
  defaultUTxOConfiguration,
  mkUTxOConfiguration,
)
where

import Cardano.Chain.Common.Address (Address)
import Cardano.Chain.Common.Compact (CompactAddress, toCompactAddress)
import Cardano.Ledger.Binary (
  FromCBOR (..),
  ToCBOR (..),
  encodeListLen,
  enforceSize,
 )
import Cardano.Prelude
import qualified Data.Set as Set
import NoThunks.Class (NoThunks (..))

-- | Additional configuration for ledger validation.
data UTxOConfiguration = UTxOConfiguration
  { tcAssetLockedSrcAddrs :: !(Set CompactAddress)
  -- ^ Set of source address which are asset-locked. Transactions which
  -- use these addresses as transaction inputs will be deemed invalid.
  }
  deriving (Eq, Show, Generic, NoThunks)

instance ToCBOR UTxOConfiguration where
  toCBOR (UTxOConfiguration tcAssetLockedSrcAddrs_) =
    encodeListLen 1
      <> toCBOR @(Set CompactAddress) tcAssetLockedSrcAddrs_

instance FromCBOR UTxOConfiguration where
  fromCBOR = do
    enforceSize "UTxOConfiguration" 1
    UTxOConfiguration <$> fromCBOR @(Set CompactAddress)

defaultUTxOConfiguration :: UTxOConfiguration
defaultUTxOConfiguration =
  UTxOConfiguration
    { tcAssetLockedSrcAddrs = Set.empty
    }

mkUTxOConfiguration :: [Address] -> UTxOConfiguration
mkUTxOConfiguration lockedSrcAddrs =
  UTxOConfiguration
    { tcAssetLockedSrcAddrs = Set.fromList (map toCompactAddress lockedSrcAddrs)
    }
