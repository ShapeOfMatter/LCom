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

choreography :: Choreo IO ()
choreography = do
  inputA <- input alpha
  inputB <- input beta
  outputB <- (alpha, inputA) ~> beta
  outputA <- (beta, inputB) ~> alpha
  output alpha outputA
  output beta outputB


main :: IO ()
main = do
    putStrLn "running simulation"
    runChoreo choreography
    [loc] <- getArgs
    putStrLn $ "running communicative as " ++ show loc
    runChoreography cfg choreography loc
    where
        cfg = mkHttpConfig
            [ ("A",     ("localhost", 4242))
            , ("B",    ("localhost", 4343))
            ]
