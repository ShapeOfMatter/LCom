module Communicate
    ( 
    ) where

import Data.Type.Nat (Nat)
import Data.Type.Set (AsSet, IsSet)

newtype Party = Party Nat deriving (Enum, Eq, Ord, Show)

data Located (ps :: '[Party]) v = Located v

    
-------- Effect Signatures --------

data Communicate (ps :: '[Party]) s m a where  -- s is for subject, as in the subject of the verb "communicate".
  SendAndReceive :: (IsSet recipients,
                     Subset recipients ps,
                     IsSet senders,
                     Subset senders ps) =>
                    Located senders s -> Communicate ps s m (Located (Union recipients senders) s)

makeSem ''Communicate  -- Uses template haskell to generate:
-- sendAndReceive :: Member (Communicate ps s) r => (Located senders s) -> Sem r (Located ... s)


-------- Effectful Helpers --------
