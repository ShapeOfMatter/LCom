module Main where

import Polysemy (run)

import Communicate (noEffectSingleThread)
import Examples (shareAnInt)
import Local (runLocalIO)
import Parties (Party0)

shareAnIntParty0 :: Int -> IO ()
shareAnIntParty0 i = do let (outputs, result) = run $ noEffectSingleThread $ runner shareAnInt
                        print outputs
                        print $ result
  where runner = runLocalIO @Party0 i

main :: IO ()
main = do shareAnIntParty0 200
