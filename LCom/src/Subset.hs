module Subset (
  extendedSubset,
  immediateSubset,
  Subset,
  subsetHeadOuter,
  SubsetProof,
  subsetTail,
  transitiveSubset,
  unionOfSubsets
) where

import Data.Type.Set (IsSet, Subset, Union)
import Logic.Classes (Transitive, transitive)
import Logic.Proof (axiom, Proof)

data Subset' s t where {}
instance Transitive Subset' where {}
type SubsetProof s t = Proof (Subset' s t)

immediateSubset :: (Subset s t) =>
                   SubsetProof s t
immediateSubset = axiom

extensionSubset :: (IsSet (s ': ss)) => SubsetProof ss (s ': ss)
extensionSubset = axiom

extendedSubset :: (IsSet (x ': s),
                   IsSet (x ': t)) =>
                  SubsetProof s t -> SubsetProof (x ': t) (x ': s)
extendedSubset = const axiom

transitiveSubset :: forall k (s :: [k]) (t :: [k]) (v :: [k]).
                    SubsetProof s t -> SubsetProof t v -> SubsetProof s v
transitiveSubset = transitive

unionOfSubsets :: forall k (s1 :: [k]) (s2 :: [k]) (t :: [k]).
                  SubsetProof s1 t -> SubsetProof s2 t -> SubsetProof (Union s1 s2) t
unionOfSubsets _ _ = axiom

subsetHeadOuter :: forall k (x :: k) (s :: [k]) (t :: [k]).
                   (IsSet (x ': t)) =>
                   SubsetProof s t -> SubsetProof s (x ': t)
subsetHeadOuter st = transitive st extensionSubset

class VacousSubset (s :: [k]) where
  vacousSubset :: SubsetProof ('[] :: [k]) s
instance VacousSubset '[] where
  vacousSubset = immediateSubset
instance forall k (s :: k) (ss :: [k]).
         (VacousSubset ss,
          IsSet (s ': ss)) =>
         VacousSubset (s ': ss) where
  vacousSubset = transitive (vacousSubset) (extensionSubset @s @ss)
  
subsetTail :: SubsetProof (x ': s) (x ': t) -> SubsetProof s t
subsetTail _ = axiom
