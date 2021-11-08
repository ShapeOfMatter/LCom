module Communicate
    ( address
    , addresses
    , Communicate()
    , noEffectSingleThread
    , locally
    , Party
    , send
    , runClique
    , runMyPart
    ) where

import Data.Distributive (distribute)
import Data.Maybe (fromJust)
import Data.Type.Nat (Mult, Nat(Z,S), Plus, SNatI)
import Data.Type.Set (IsSet, Union)
import qualified Data.Type.Set as Set
import Data.Vec.Lazy (chunks, singleton, split, Vec(VNil))
import qualified Data.Vec.Lazy as Vec
import Polysemy (interpret, Member, reinterpret, reinterpret2, Sem)
import Polysemy.Input (Input, input)
import qualified Polysemy.Internal as PI  -- God help us.
import Polysemy.Output (Output, output)

import Subset (immediateSubset, Subset, SubsetProof, transitiveSubset, unionOfSubsets)


-------- Parties --------

newtype Party = Party {address :: Int} deriving (Enum, Eq, Ord, Show)

addresses :: 

data Located (parties :: [Party]) v = Located v
instance Functor (Located parties) where
  fmap f (Located v) = Located (f v)
instance Applicative (Located parties) where
  pure = Located
  (Located f) <*> (Located v) = Located (f v)
instance Monad (Located parties) where
  (Located v) >>= f = f v

    
-------- Effect Signatures --------

data Communicate (parties :: [Party]) s m a where  -- s is for subject, as in the subject of the verb "communicate".
  SendMaybe :: forall recipients senders parties s m.
               SubsetProof recipients parties
               -> SubsetProof senders parties
               -> Located senders (Maybe s)
               -> Communicate parties s m (Located recipients (Maybe s))
  Locally :: forall parties s m a.
             Located parties a -> Communicate parties s m a

sendMaybe :: forall recipients senders parties s r.
             (Member (Communicate parties s) r) =>
             SubsetProof recipients parties
             -> SubsetProof senders parties
             -> Located senders (Maybe s)
             -> Sem r (Located recipients (Maybe s))
sendMaybe rp sp x = PI.send $ SendMaybe rp sp x
locally :: (Member (Communicate parties s) r) => Located parties a  -> Sem r a
locally x = PI.send $ Locally x


-------- Effectful Helpers --------
-- In practice these will be used instead of the raw constructor.

-- Technically a handler, but it feels like it belongs here.
--clique :: forall parties cs s r a (recipients :: [Party]) (senders :: [Party]).
runClique :: forall parties clq s r a.
             (IsSet parties,
              IsSet clq,
              Subset clq parties) =>
             Sem (Communicate clq s ': r) a -> Sem (Communicate parties s ': r) (Located clq a)
runClique = (Located <$>) . (reinterpret _clique)
  where cp = immediateSubset :: SubsetProof clq parties
        _clique :: forall rInitial x.
                   Communicate clq s (Sem rInitial) x -> Sem (Communicate parties s ': r) x
        _clique (SendMaybe rc sc l) = sendMaybe (transitiveSubset rc cp) (transitiveSubset sc cp) l
        _clique (Locally (Located v)) = return v

class (SNatI n) => Sendable s t n where
  -- Implementations must guarentee that `deserialize . serialize == id`.
  serialize :: t -> Vec n (Maybe s)
  deserialize :: Vec n (Maybe s) -> t

send :: forall (recipients :: [Party]) (senders :: [Party]) (parties :: [Party]) r s t n.
        (IsSet recipients,
         IsSet senders,
         IsSet parties,
         Subset recipients parties,
         Subset senders parties,
         Member (Communicate parties s) r,
         Sendable s t n) =>
        Located senders t -> Sem r (Located (Union recipients senders) t)
send l = do vl' <- sendVec vl
            return (deserialize <$> sequence vl')
  where rp = immediateSubset @recipients
        sp = immediateSubset @senders
        sendMb = sendMaybe (unionOfSubsets rp sp) sp
        vl = distribute $ serialize <$> l
        sendVec :: Vec n (Located senders (Maybe s)) -> Sem r (Vec n (Located (Union recipients senders) (Maybe s)))
        sendVec = sequence . (sendMb <$>)

instance Sendable s s ('S 'Z) where
  serialize = singleton . Just
  deserialize = fromJust . Vec.head
instance Sendable s () 'Z where
  serialize = const VNil
  deserialize = const ()
instance Sendable s (Maybe s) ('S 'Z) where
  serialize = singleton
  deserialize = Vec.head
instance (Sendable s t n,
          SNatI m,
          SNatI mn,
          mn ~ (Mult m n)) =>
         Sendable s (Vec m t) mn where
  serialize = Vec.concatMap @t @n serialize
  deserialize = (deserialize <$>) . (chunks @m @n)
instance (Sendable s t1 n1,
          Sendable s t2 n2,
          SNatI nn,
          nn ~ (Plus n1 n2)) =>
         Sendable s (t1, t2) nn where
  serialize (t1, t2) = (Vec.++) @n1 @(Maybe s) @n2 (serialize t1) (serialize t2)
  deserialize vv = let (v1, v2) = split @n1 @n2 vv in (deserialize v1, deserialize v2)
  

-------- Handlers --------

-- Not very useful, but easy to write, and I wanna validate any of this works today.
noEffectSingleThread :: (IsSet parties) =>
                        Sem (Communicate parties s ': r) a -> Sem r a
noEffectSingleThread = interpret $ \case
  SendMaybe _ _ (Located v) -> return (Located v)
  Locally (Located v) -> return v

-- Communication by the local party would turn into IO read/write on a network port;
-- all other communication should simply be skipped.
runMyPart :: forall p parties s r a.
             (IsSet parties,
              Set.Member p parties) =>
             Sem (Communicate parties s ': r) a -> Sem (Input (Maybe s) ': Output (Maybe s) ': r) a
runMyPart = reinterpret2 $ \case  -- I think I can make this work using a closed type family or something; IDK.
  SendMaybe rp sp (Located v) -> undefined
  Locally (Located v) -> undefined


-- And there should be another handler, similar to noEffectSingleThread,
-- which will run single-threaded by collect a structured log of all communication. 


