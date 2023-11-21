module Main where

import           Choreography       (Choreo, locally, mkHttpConfig,
                                     runChoreo, runChoreography, type (@), (~>))
import           Choreography.Location (toLocTm)
import           Control.Monad      (void)
import           Data.Proxy         (Proxy (..))
import           GHC.TypeLits       (KnownSymbol)
import           System.Environment (getArgs)

alpha :: Proxy "A"
alpha = Proxy

beta :: Proxy "B"
beta = Proxy

output :: (Show a, KnownSymbol l) => Proxy l -> a @ l -> Choreo IO ()
output loc a = void $ loc `locally` \un -> putStrLn $ "[" ++ toLocTm loc ++ "]" ++ (show $ un a)

input :: (KnownSymbol l) => Proxy l -> Choreo IO (String @ l)
input loc = loc `locally` \_ -> do putStrLn $ "Enter input for " ++ toLocTm loc ++ ":"
                                   getLine

choreography :: String -> Choreo IO ()
choreography context = do
  inputA <- input alpha
  inputB <- input beta
  (outputA, outputB) <- if "switch" == context
                          then do oB <- (alpha, inputA) ~> beta
                                  oA <- (beta, inputB) ~> alpha
                                  return (oA, oB)
                          else do oA <- (beta, inputB) ~> alpha
                                  oB <- (alpha, inputA) ~> beta
                                  return (oA, oB)
  output alpha outputA
  output beta outputB


main :: IO ()  -- To break: run A with context as "noSwitch" and B with context as "switch".
main = do
    [loc, context] <- getArgs
    putStrLn "running simulation"
    runChoreo $ choreography context
    putStrLn $ "running communicative as " ++ show loc
    runChoreography cfg (choreography context) loc
    where
        cfg = mkHttpConfig
            [ ("A",     ("localhost", 4242))
            , ("B",    ("localhost", 4343))
            ]
