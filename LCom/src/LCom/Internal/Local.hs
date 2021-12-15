module LCom.Internal.Local
    ( Local
    , localInput
    , localOutput
    , runAllLocalIO
    , runLocalIO
    ) where

import Data.List (genericIndex)
import Polysemy (Member, reinterpret2, Sem)
import Polysemy.Input (Input, input, inputs, runInputConst)
import qualified Polysemy.Internal as PI  -- God help us.
import Polysemy.Output (Output, output, runOutputList)

import LCom.Internal.Data (Address, address, Located(Located), Party, pretend)


-------- Effect Signatures --------

data Local (i :: *) (o :: *) m a where -- no membership/subset constraints?
  LocalInput :: forall (p :: Party) i o m.
                (Address p) =>
                Local i o m (Located '[p] i)
  LocalOutput :: forall (p :: Party) i o m.
                 (Address p) =>
                 Located '[p] o -> Local i o m ()

localInput :: forall (p :: Party) i o r.
              (Address p,
               Member (Local i o) r) =>
              Sem r (Located '[p] i)
localInput = PI.send $ LocalInput
localOutput :: forall (p :: Party) i o r.
               (Address p,
                Member (Local i o) r) =>
               Located '[p] o -> Sem r ()
localOutput x = PI.send $ LocalOutput x


-------- Handlers --------

runLocalIO :: forall me i o r a.
              (Address me) =>
              i
              -> Sem (Local i o ': r) a
              -> Sem r ([o], a)
runLocalIO i = runOutputList . (runInputConst i) . interpretMyIO
  where myOutput :: forall (p :: Party).
                    (Address p) =>
                    Located '[p] o -> Sem (Input i ': Output o ': r) ()
        -- I'm avoiding binding to preserve lazyness; IDK if it matters.
        myOutput = if (address @me == address @p)
                   then (\case Located o -> output o)
                   else (const $ return ())
        myInput :: forall (p :: Party) m.
                   (Address p) =>
                   Local i o m (Located '[p] i) -> Sem (Input i ': Output o ': r) (Located '[p] i)
        myInput _ = if (address @me == address @p)
                    then (Located <$> input)
                    else (return pretend)
        interpretMyIO :: forall b.
                         Sem (Local i o ': r) b
                         -> Sem (Input i ': Output o ': r) b
        interpretMyIO = reinterpret2 $ \case
          li@(LocalInput) -> myInput li
          LocalOutput l -> myOutput l

runAllLocalIO :: forall i o r a.
                 [i]  -- Index-addressed inputs
                 -> Sem (Local i o ': r) a
                 -> Sem r ([(Integer, o)], a)
runAllLocalIO is = runOutputList . (runInputConst is) . interpretAllIO
  where runOutput :: forall (p :: Party).
                     (Address p) =>
                     Located '[p] o
                     -> Sem (Input [i] ': Output (Integer, o) ': r) ()
        -- I'm avoiding binding to preserve lazyness; IDK if it matters.
        runOutput = \case Located o -> output (address @p, o)
        runInput :: forall (p :: Party) m.
                    (Address p) =>
                    Local i o m (Located '[p] i)
                    -> Sem (Input [i] ': Output (Integer, o) ': r) (Located '[p] i)
        runInput _ = let index = (`genericIndex` address @p)
                     in Located <$> inputs index
        interpretAllIO :: forall b.
                          Sem (Local i o ': r) b
                          -> Sem (Input [i] ': Output (Integer, o) ': r) b
        interpretAllIO = reinterpret2 $ \case
          li@(LocalInput) -> runInput li
          LocalOutput l -> runOutput l

