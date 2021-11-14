module Examples
    ( shareAnInt
    ) where

import Data.Type.Nat (Nat(Z,S))
import Polysemy (Sem)

import Communicate (Communicate, locally, send)
import Data (downcast, Party(Party))
import Local (Local, localInput, localOutput)

type Party0 = 'Party 'Z
type Party1 = 'Party ('S 'Z)
type Party2 = 'Party ('S ('S 'Z))

type Couple = '[Party0, Party1]

shareAnInt :: Sem '[Local Int Int, Communicate Couple Int] Int
shareAnInt = do i <- localInput @Party0
                shared <- send @Couple @('S 'Z) i
                localOutput @Party1 (downcast shared)
                opened <- locally shared
                return opened
