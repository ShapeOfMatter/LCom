module LCom
  ( Address
  , address
  , Addresses
  , addresses
  , Communicate
  , downcast
  , Local
  , Located()
  , localInput
  , locally
  , localOutput
  , noEffectSingleThread
  , Party(Party)
  , runLocalIO
  , send
  , Sendable
  , Subset
  ) where

import Data.Type.Set (Subset)

import LCom.Internal.Communicate
import LCom.Internal.Data
import LCom.Internal.Local
