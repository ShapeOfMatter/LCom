module LCom.Internal.Communicate
    ( Communicate()
    , noEffectSingleThread
    , locally
    , logTransmissionsSingleThread
    , send
    , runClique
    , runParty
    , Transmission(Transmission)
    ) where

import Data.Distributive (distribute)
import Data.Type.Set (Subset)
import Data.Vec.Lazy (Vec)
import Polysemy (interpret, Member, reinterpret, reinterpret2, Sem, subsume_)
import Polysemy.Input (Input, input)
import qualified Polysemy.Internal as PI  -- God help us.
import Polysemy.Output (Output, output, runOutputList)

import LCom.Internal.Data (Address, address, Addresses, addresses, deserialize, Located(Located), Party, pretend, Sendable, serialize)



-------- Effect Signatures --------

data Communicate (parties :: [Party]) s m a where  -- s is for subject, as in the subject of the verb "communicate".
  SendMaybe :: forall (recipients :: [Party]) (senders :: [Party]) parties s m.
               (Addresses recipients, Addresses senders) =>
               Located senders (Maybe s) -> Communicate parties s m (Located recipients (Maybe s))
  Locally :: Located parties a -> Communicate parties s m a

sendMaybe :: forall recipients senders parties s r.
             (Addresses recipients, Addresses senders,
              Member (Communicate parties s) r) =>
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

-- |Send a value from one or more parties to one or more recipients.  
-- It's typically necessary to specify the recipients with a type application, _e.g._ `send @('[p1, p2]) myVal`.
send :: forall (recipients :: [Party]) n (senders :: [Party]) (parties :: [Party]) r s t .
        (Subset recipients parties,
         Subset senders parties,
         Addresses recipients,
         Addresses senders,
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

data Transmission s where
  Transmission :: [Integer] -> [Integer] -> Maybe s -> Transmission s
instance (Show s) => Show (Transmission s) where
  show (Transmission f t m) = (show f) <> "→" <> (show t) <> ": " <> (maybe "∅" show m)

logTransmissionsSingleThread :: forall parties s r a.
                                Sem (Communicate parties s ': r) a
                                -> Sem r ([Transmission s], a)
logTransmissionsSingleThread = runOutputList . (reinterpret $ \case
  smlv@(SendMaybe (Located v)) -> do logSend smlv
                                     return (Located v)
  Locally (Located v) -> return v
  )
  where logSend :: forall recipients m.
                   (Addresses recipients) =>
                   Communicate parties s m (Located recipients (Maybe s))
                   -> Sem (Output (Transmission s) ': r) ()
        logSend (SendMaybe lv@(Located v)) = output $ Transmission (getSenders lv) (addresses @recipients) v
        logSend _ = error "This is impossible because this is only called from the pattern match above."
        getSenders :: forall senders.
                      (Addresses senders) =>
                      Located senders (Maybe s) -> [Integer]
        getSenders _ = addresses @senders

-- Requisite for all the other handlers:
data Transmit (parties :: [Party]) s m a where
  TransmitMaybe :: forall senders parties s m.
                   (Addresses senders) =>
                   Located senders (Maybe s)
                   -> Transmit parties s m ()
transmitMaybe :: forall senders parties s r.
                 (Addresses senders,
                  Member (Transmit parties s) r) =>
                 Located senders (Maybe s)
                 -> Sem r ()
transmitMaybe x = PI.send $ TransmitMaybe x

runTransmit :: forall p parties s r a.
               (Address p) =>
               Sem (Transmit parties s ': r) a -> Sem (Output ([Integer], Maybe s) ': r) a
runTransmit = reinterpret $ \case
  TransmitMaybe l -> rt l
  where rt :: forall senders.
              (Addresses senders) =>
              Located senders (Maybe s) -> Sem (Output ([Integer], Maybe s) ': r) ()
        rt (Located ms) = if address @p `elem` addresses @senders then output (addresses @senders, ms) else return ()

data Recieve (parties :: [Party]) s m a where
  RecieveMaybe :: forall recipients parties s m.
                  (Addresses recipients) =>
                  Recieve parties s m (Located recipients (Maybe s))
recieveMaybe :: forall recipients parties s r.
                (Addresses recipients,
                 Member (Recieve parties s) r) =>
                Sem r (Located recipients (Maybe s))
recieveMaybe = PI.send $ RecieveMaybe

runRecieve :: forall p parties s r a.
              (Address p) =>
              Sem (Recieve parties s ': r) a -> Sem (Input (Maybe s) ': r) a
runRecieve = reinterpret $ \case
  rm@(RecieveMaybe) -> rr rm
  where rr :: forall recipients m.
              (Addresses recipients) =>
              Recieve parties s m (Located recipients (Maybe s)) -> Sem (Input (Maybe s) ': r) (Located recipients (Maybe s))
        rr = if address @p `elem` addresses @recipients then const (Located <$> input) else const (return pretend)

splitTasks :: forall parties s r a.
              Sem (Communicate parties s ': r) a -> Sem (Transmit parties s ': Recieve parties s ': r) a
splitTasks = reinterpret2 $ \case -- possibly a layer of State here would help with the dispatching?
  SendMaybe x -> do transmitMaybe x
                    recieveMaybe
  Locally (Located v) -> return v

-- Communication by the local party would turn into IO read/write on a network port;
-- all other communication should simply be skipped.
runParty :: forall p parties s r a.
            (Address p) =>
            Sem (Communicate parties s ': r) a -> Sem (Input (Maybe s) ': Output ([Integer], Maybe s) ': r) a
runParty = runRecieve @p . subsume_ . runTransmit @p . splitTasks

-- And there should be another handler, similar to noEffectSingleThread,
-- which will run single-threaded by collect a structured log of all communication. 
--}

