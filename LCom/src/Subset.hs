module Subset (
  immediateSubset,
  Subset,
  SubsetProof,
  transitiveSubset
) where

import Data.Type.Set (Subset)
import Logic.Classes (Transitive, transitive)
import Logic.Proof (axiom, Proof)

data Subset' s t where {}
instance Transitive Subset' where {}
type SubsetProof s t = Proof (Subset' s t)

immediateSubset :: (Subset s t) => Proof (Subset' s t)
immediateSubset = axiom
transitiveSubset :: forall k (s :: [k]) (t :: [k]) (v :: [k]). Proof (Subset' s t) -> Proof (Subset' t v) -> Proof (Subset' s v)
transitiveSubset = transitive
