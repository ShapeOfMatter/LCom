module Lib {-()-} where

import Data.Type.Nat (Nat)
import Data.Type.Set (IsSet)
import Polysemy (Sem, makeSem, reinterpret)

import Subset (immediateSubset, Subset, SubsetProof, transitiveSubset)


data Located (parties :: [Nat]) v = Located v

data Com (parties :: [Nat]) m a where
  SendInt :: forall recipients senders parties m.
             SubsetProof recipients parties 
             -> SubsetProof senders parties
             -> Located senders Int
             -> Com parties m (Located recipients Int)
  FromUniversal :: forall parties m a.
                   Located parties a -> Com parties m a

-- Polysemy uses template haskell:
makeSem ''Com
--sendInt :: Member (Com parties) r => (Located senders Int) -> Sem r (Located recipients Int)
--fromUniversal :: Member (Com parties) r => (Located parties a) -> Sem r a
--we can manually write out the functions instead of useing makeSem;
--that might help make Located's type artument explicit, but I don't think it matters here.

-- "lift" a program in a small community (clique) into a larger community's monad. 
runClique :: forall parties clq r a.
          (IsSet parties,
           IsSet clq,
           Subset clq parties) =>
          Sem (Com clq ': r) a
          -> Sem (Com parties ': r) (Located clq a)
runClique = (Located <$>) . (reinterpret _clique)
  where cp = immediateSubset :: SubsetProof clq parties
        _clique :: forall rInitial x.
                   Com clq (Sem rInitial) x -> Sem (Com parties ': r) x
        _clique (SendInt rc sc x) = sendInt (transitiveSubset rc cp) (transitiveSubset sc cp) x
        _clique (FromUniversal (Located v)) = return v
        
