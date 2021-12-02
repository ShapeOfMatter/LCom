module Main where

import Polysemy (run)

import Communicate (noEffectSingleThread)
import Examples (shareAnInt)
import Local (runLocalIO)
import Parties (Party0)


main :: IO ()
main = do i :: Int <- read <$> getLine
          let runner = runLocalIO @Party0 i
          let (outputs, result) = run $ noEffectSingleThread $ runner shareAnInt
          print outputs
          print $ id result
