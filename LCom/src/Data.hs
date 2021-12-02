module Data
    ( Address
    , address
    , Addresses
    , addresses
    , deserialize
    , downcast
    , Located(Located)
    , Party(Party)
    , pretend
    , Sendable
    , serialize
    ) where

import Data.Fin (Fin)
import Data.Maybe (fromJust)
import Data.Type.Nat (Mult, Nat(Z,S), Plus, SNatI)
import Data.Vec.Lazy (chunks, singleton, split, Vec)
import qualified Data.Vec.Lazy as Vec

import Subset (Subset)

newtype Party = Party { a :: Nat } deriving (Enum, Eq, Ord, Show)

class Address (p :: Party) where
  address :: Integer
instance (SNatI n) => Address ('Party n) where
  address = toInteger $ maxBound @(Fin ('S n))

class Addresses (parties :: [Party]) where
  addresses :: [Integer]
instance Addresses '[] where
  addresses = []
instance (SNatI n, Addresses ps) => Addresses ('Party n ': ps) where
  addresses = (address @('Party n)) : (addresses @ps)


data Located (parties :: [Party]) v = Located v

instance Functor (Located parties) where
  fmap f (Located v) = Located (f v)
instance Applicative (Located parties) where
  pure = Located
  (Located f) <*> (Located v) = Located (f v)
instance Monad (Located parties) where
  (Located v) >>= f = f v

pretend :: forall ps v. Located ps v
pretend = Located undefined

downcast :: (Subset ps' ps) => Located ps x -> Located ps' x
downcast (Located x) = Located x


class (SNatI n) => Sendable s t n | s t -> n where
  -- Implementations must guarentee that `deserialize . serialize == id`.
  serialize :: t -> Vec n (Maybe s)
  deserialize :: Vec n (Maybe s) -> t

instance Sendable s s ('S 'Z) where
  serialize = singleton . Just
  deserialize = fromJust . Vec.head
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

