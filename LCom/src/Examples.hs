module Examples
    ( shareAnInt
    ) where

import Polysemy (Sem)

import LCom (Communicate, downcast, Local, localInput, localOutput, locally, send)
import Parties (Party0, Party1)

type Couple = '[Party0, Party1]

shareAnInt :: Sem '[Local Int Int, Communicate Couple Int] Int
shareAnInt = do i <- localInput @Party0
                shared <- send @Couple i
                localOutput @Party1 (downcast shared)
                opened <- locally shared
                return opened
