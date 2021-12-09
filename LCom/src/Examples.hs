module Examples
    ( shareAnInt
    ) where

import Data.Type.Nat (Nat(Z,S))
import Polysemy (Sem)

import Communicate (Communicate, locally, send)
import Data (downcast)
import Local (Local, localInput, localOutput)
import Parties (Party0, Party1)

type Couple = '[Party0, Party1]

shareAnInt :: Sem '[Local Int Int, Communicate Couple Int] Int
shareAnInt = do i <- localInput @Party0
                shared <- send @Couple i
                localOutput @Party1 (downcast shared)
                opened <- locally shared
                return opened
