module Subset (
  immediateSubset,
  Subset,
  SubsetProof,
  transitiveSubset,
  unionOfSubsets
) where

import Data.Type.Set (Subset, Union)
import Logic.Classes (Transitive, transitive)
import Logic.Proof (axiom, Proof, sorry)

data Subset' s t where {}
instance Transitive Subset' where {}
type SubsetProof s t = Proof (Subset' s t)

immediateSubset :: (Subset s t) =>
                   SubsetProof s t
immediateSubset = axiom
transitiveSubset :: forall k (s :: [k]) (t :: [k]) (v :: [k]).
                    SubsetProof s t -> SubsetProof t v -> SubsetProof s v
transitiveSubset = transitive
unionOfSubsets :: forall k (s1 :: [k]) (s2 :: [k]) (t :: [k]).
                  SubsetProof s1 t -> SubsetProof s2 t -> SubsetProof (Union s1 s2) t
unionOfSubsets s1t s2t = sorry

