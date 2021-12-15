module Main where

import Prelude hiding (log)

import Polysemy (run)
import System.Random (newStdGen)

import LCom (noEffectSingleThread, logTransmissionsSingleThread, runAllLocalIO, runLocalIO)
import Examples (shareAnInt, threePartyXOR)
import Parties (Party0)

log :: (Show a) => String -> a -> IO ()
log label item = putStrLn $ label <> ": " <> (show item)

shareAnIntParty0 :: Int -> IO ()
shareAnIntParty0 i = do log "Share an Int" i
                        let (outputs, result) = run $ noEffectSingleThread $ runner shareAnInt
                        log "Outputs" outputs
                        log "Results" result
  where runner = runLocalIO @Party0 i

mpcXOR :: (Bool, Bool, Bool) -> IO ()
mpcXOR inputs@(in0, in1, in2) = do log "MPC three-party XOR" inputs
                                   (r0, r1, r2) <- (,,) <$> newStdGen <*> newStdGen <*> newStdGen
                                   let (transmissions, (outputs, result)) = run $ logTransmissionsSingleThread $ runner r0 r1 r2 threePartyXOR
                                   log "Transmissions" transmissions
                                   log "Outputs" outputs
                                   log "Results" result
  where runner r0 r1 r2 = runAllLocalIO [(in0, r0), (in1, r1), (in2, r2)]

main :: IO ()
main = do shareAnIntParty0 200
          mpcXOR (True, False, False)
