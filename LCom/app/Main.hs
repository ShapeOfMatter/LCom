module Main where

import Polysemy (run)

import Communicate (noEffectSingleThread)
import Examples (shareAnInt)
import Local (runLocalIO)

main :: IO ()
main = do i :: Int <- read <$> getLine
          let runner = runLocalIO True i
          let (outputs, result) = run $ noEffectSingleThread $ runner shareAnInt
          print outputs
          print result
