module Communicate
    ( Communicate()
    , noEffectSingleThread
    , locally
    , send
    , runClique
    --, ignoreHead
    ) where

import Data.Distributive (distribute)
import Data.Type.Set (Subset)
import Data.Vec.Lazy (Vec)
import Polysemy (interpret, Member, reinterpret, Sem)
import qualified Polysemy.Internal as PI  -- God help us.

import Data (deserialize, Located(Located), Party, Sendable, serialize)


-------- Effect Signatures --------

data Communicate (parties :: [Party]) s m a where  -- s is for subject, as in the subject of the verb "communicate".
  SendMaybe :: forall (recipients :: [Party]) (senders :: [Party]) parties s m.
               Located senders (Maybe s) -> Communicate parties s m (Located recipients (Maybe s))
  Locally :: Located parties a -> Communicate parties s m a

sendMaybe :: forall recipients senders parties s r.
             (Member (Communicate parties s) r) =>
             Located senders (Maybe s) -> Sem r (Located recipients (Maybe s))
sendMaybe x = PI.send $ SendMaybe @recipients x
locally :: (Member (Communicate parties s) r) => Located parties a  -> Sem r a
locally x = PI.send $ Locally x


-------- Effectful Helpers --------
-- In practice these will be used instead of the raw constructor.

-- Technically a handler, but it feels like it belongs here.
--clique :: forall parties cs s r a (recipients :: [Party]) (senders :: [Party]).
runClique :: forall parties clq s r a.
             (Subset clq parties) =>
             Sem (Communicate clq s ': r) a -> Sem (Communicate parties s ': r) (Located clq a)
runClique = (Located <$>) . (reinterpret _clique)
  where _clique :: forall rInitial x.
                   Communicate clq s (Sem rInitial) x -> Sem (Communicate parties s ': r) x
        _clique (SendMaybe l) = sendMaybe l
        _clique (Locally (Located v)) = return v

send :: forall (recipients :: [Party]) n (senders :: [Party]) (parties :: [Party]) r s t .
        (Subset recipients parties,
         Subset senders parties,
         Member (Communicate parties s) r,
         Sendable s t n) =>
        Located senders t -> Sem r (Located recipients t)
send l = do vl' <- sendVec vl
            return (deserialize <$> sequence vl')
  where vl = distribute $ serialize <$> l
        sendVec :: Vec n (Located senders (Maybe s)) -> Sem r (Vec n (Located recipients (Maybe s)))
        sendVec = sequence . (sendMaybe <$>)


-------- Handlers --------

-- Not very useful, but easy to write, and I wanna validate any of this works today.
noEffectSingleThread :: Sem (Communicate parties s ': r) a -> Sem r a
noEffectSingleThread = interpret $ \case
  SendMaybe (Located v) -> return (Located v)
  Locally (Located v) -> return v

{-
-- Requisite for all the other handlers:
data Transmit (parties :: [Party]) s m a where
  TransmitMaybe :: forall senders parties s m.
                   SubsetProof senders parties
                   -> Located senders (Maybe s)
                   -> Transmit parties s m ()
transmitMaybe :: forall senders parties s r.
                 (Member (Transmit parties s) r) =>
                 SubsetProof senders parties
                 -> Located senders (Maybe s)
                 -> Sem r ()
transmitMaybe sp x = PI.send $ TransmitMaybe sp x
data Recieve (parties :: [Party]) s m a where
  RecieveMaybe :: forall recipients parties s m.
                  SubsetProof recipients parties
                  -> Recieve parties s m (Located recipients (Maybe s))
recieveMaybe :: forall recipients parties s r.
                (Member (Recieve parties s) r) =>
                SubsetProof recipients parties
                -> Sem r (Located recipients (Maybe s))
recieveMaybe sp = PI.send $ RecieveMaybe sp

splitTasks :: forall parties s r a.
              Sem (Communicate parties s ': r) a -> Sem (Transmit parties s ': Recieve parties s ': r) a
splitTasks = reinterpret2 $ \case -- possibly a layer of State here would help with the dispatching?
  SendMaybe rp sp x -> do transmitMaybe sp x
                          recieveMaybe rp
  Locally (Located v) -> return v


class IgnoreSend (p :: Party) (recipients :: [Party]) (senders :: [Party]) (parties :: [Party]) where
  ignoreSend :: (Member (Communicate parties s) r) =>
                SubsetProof recipients (p ': parties)
                -> SubsetProof senders (p ': parties)
                -> Located senders (Maybe s)
                -> Sem r (Located recipients (Maybe s))
--instance p recipients senders '[] where
--  ignoreSend _ _ _ = return pretend
instance IgnoreSend p (p ': recipients) (p ': senders) (p ': parties) where
  ignoreSend rp sp (Located m) = do (Located m') <- sendMaybe (subsetTail rp) (subsetTail sp) (Located m)
                                    return (Located m')
 

{-
ignoreHead :: forall p parties s r a.
              (IsSet (p ': parties)) =>
              Sem (Communicate (p ': parties) s ': r) a -> Sem (Communicate parties s ': r) a
ignoreHead = reinterpret $ \case  -- I think I can make this work using a closed type family or something; IDK.
  SendMaybe rp sp (Located v) -> ignoreSend rp sp (Located v)
  Locally (Located v) -> undefined

class MakeSend (p :: Party) (recipients :: [Party]) (senders :: [Party]) (parties :: [Party]) where
  makeSend :: (Members '[Input (Maybe s), Output ([Integer], Maybe s), Communicate parties s] r) =>
              SubsetProof recipients (p ': parties)
              -> SubsetProof senders (p ': parties)
              -> Located senders v
              -> Sem r (Located recipients v)
--instance MakeSend p recipients senders '[] where
--  makeSend _ _ _ = return pretend
instance MakeSend p recipients '[] (p ': parties) where
  makeSend _ _ _ = return pretend
instance MakeSend p '[] senders parties where
  makeSend _ _ _ = return pretend
instance MakeSend p (p ': recipients) (p ': senders) (p ': parties) where
  makeSend _ _ (Located v) = return (Located v)
instance MakeSend p (p ': recipients) senders (p ': parties) where
  makeSend _ _ (Located v) = undefined

-- Communication by the local party would turn into IO read/write on a network port;
-- all other communication should simply be skipped.
runHead :: forall p parties s r a.
           (IsSet (p ': parties)) =>
           Sem (Communicate (p ': parties) s ': r) a -> Sem (Communicate parties s ': Input (Maybe s) ': Output ([Integer], Maybe s) ': r) a
runHead = reinterpret3 $ \case  -- I think I can make this work using a closed type family or something; IDK.
  SendMaybe rp sp (Located v) -> undefined
  Locally (Located v) -> undefined
-}

-- And there should be another handler, similar to noEffectSingleThread,
-- which will run single-threaded by collect a structured log of all communication. 
-}

