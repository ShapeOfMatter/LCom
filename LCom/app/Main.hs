module Main where

import Prelude hiding (log)

import Data.Bifunctor (first)
import Data.Foldable (for_)
import Data.List (uncons)
import Polysemy (run, runM)
import System.Random (newStdGen)
import Test.QuickCheck (quickCheck)

import LCom (noEffectSingleThread, logTransmissionsSingleThread, runAllLocalIO, runLocalIO, runParty)
import Examples (raceTo100, runInputOutputAsIO, shareAnInt, threePartyXOR)
import Parties (Party0)
import Transmission (byRecipient, bySender, message)

log :: (Show a) => String -> a -> IO ()
log label item = putStrLn $ label <> ": " <> (show item)

logS :: (Show a) => String -> [a] -> IO ()
logS label items = do let (firstorPlaceholder, rest) = maybe ("∅", []) (first show) (uncons items)
                      let label' = label <> ": "
                      let tab = replicate (length label') ' '
                      putStrLn $ label' <> firstorPlaceholder
                      for_ rest (putStrLn . (tab <>) . show)

shareAnIntParty0 :: Int -> IO ()
shareAnIntParty0 i = do log "Share an Int" i
                        let (outputs, result) = run $ noEffectSingleThread $ runner shareAnInt
                        logS "Outputs" outputs
                        log "Result" result
  where runner = runLocalIO @Party0 i

testIntSharing :: IO ()
testIntSharing = quickCheck assertion
  where assertion int = let (transmissions, _) = share int
                            partyAddress `sends` i = not $ null $ filter ((==) (Just i) . message) $ (bySender transmissions) !! partyAddress
                      in and [1 == length transmissions,  -- Count transmissions
                              0 `sends` int]
        share int = run $ logTransmissionsSingleThread $ runAllLocalIO [int, undefined] $ shareAnInt

mpcXOR :: (Bool, Bool, Bool) -> IO ()
mpcXOR inputs@(in0, in1, in2) = do log "MPC three-party XOR" inputs
                                   (r0, r1, r2) <- (,,) <$> newStdGen <*> newStdGen <*> newStdGen
                                   let (transmissions, (outputs, result)) = run $ logTransmissionsSingleThread $ runner r0 r1 r2 threePartyXOR
                                   logS "Transmissions" transmissions
                                   logS "By recipient" $ byRecipient transmissions
                                   logS "Outputs" outputs
                                   log "Result" result
  where runner r0 r1 r2 = runAllLocalIO [(in0, r0), (in1, r1), (in2, r2)]

playGame :: IO ()
playGame = do log "roll random numbers" "Get to 100!"
              rng <- newStdGen
              (outputs, result) <- runM $ runInputOutputAsIO $ runParty @Party0 $ runLocalIO @Party0 rng $ raceTo100
              logS "Outputs" outputs
              log "Result" result

main :: IO ()
main = do shareAnIntParty0 200
          testIntSharing
          mpcXOR (True, False, False)
          playGame
