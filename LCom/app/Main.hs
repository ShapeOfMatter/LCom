module Main where

import Polysemy (run)

import LCom (noEffectSingleThread, runLocalIO)
import Examples (shareAnInt)
import Parties (Party0)

shareAnIntParty0 :: Int -> IO ()
shareAnIntParty0 i = do let (outputs, result) = run $ noEffectSingleThread $ runner shareAnInt
                        print outputs
                        print $ result
  where runner = runLocalIO @Party0 i

main :: IO ()
main = do shareAnIntParty0 200
