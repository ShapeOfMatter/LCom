module Communicate
    ( 
    ) where

import Data.Type.Nat (Nat)
import Data.Type.Set (AsSet, IsSet)


-------- Parties --------

newtype Party = Party Nat deriving (Enum, Eq, Ord, Show)

data Located (ps :: '[Party]) v = Located v
instance Functor (Located ps) where
  fmap f (Located v) = Located (f v)
instance Applicative (Located ps) where
  pure = Located
  (Located f) <*> (Located v) = Located (f v)
instance Monad (Located ps) where
  (Located v) >>= f = f a

    
-------- Effect Signatures --------

data Communicate (ps :: '[Party]) s m a where  -- s is for subject, as in the subject of the verb "communicate".
  SendMaybe :: (IsSet recipients,
                Subset recipients ps,
                IsSet senders,
                Subset senders ps) =>
               Located senders (Maybe s) -> Communicate ps s m (Located (Union recipients senders) (Maybe s))
    
makeSem ''Communicate  -- Uses template haskell to generate:
-- sendOne :: Member (Communicate ps s) r => (Located senders s) -> Sem r (Located ... s)


-------- Effectful Helpers --------
-- In practice these will be used instead of the raw constructor.

clique :: (IsSet ps,  -- Technically a handler, but it feels like it belongs here.
           IsSet cs,
           Subset cs ps) =>
          Sem (Communicate cs s ': r) a -> Sem (Communicate ps s ': r) a
clique = reinterpret (\case
  SendMaybe l -> sendMaybe l
  )

class Sendable s t where
  send :: (IsSet recipients,
           Subset recipients ps,
           IsSet senders,
           Subset senders ps) =>
          Located senders t -> Communicate ps s m (Located (Union recipients senders) t)

instance Sendable s s where
  send l = fromJust <$> (sendMaybe $ Just <$> l)
instance Sendable s () where
  send = return
instance Sendable s t => Sendable s (Maybe t) where  -- Introduces a level of indirection, but flatens the API.
  send Nothing = return Nothing
  send (Just t) = Just <$> (send t)
instance Sendable s t => Sendable s [t] where
  send [] = return []
  send (t:ts) = liftA2 (:) (send t) (send ts)
instance (Sendable s t1, Sendable s t2) => Sendable s (t1, t2) where
  send (t1, t2) = liftA2 (,) (send t1) (send t2)


-------- Handlers --------

noEffectSingleThread :: (IsSet ps) =>  -- Not very useful, but easy to write, and I wanna validate any of this works today.
                        Sem (Communicate ps s ': r) a -> Sem r a
noEffectSingleThread = interpret (\case
  SendMaybe (Located v) -> return (Located v)
  )

runMyPart :: (isSet ps) =>  -- In theory communication would turn into IO read/write on a network port...
             Sem (Communicate ps s ': r) 





