module Local
    ( Local
    , localInput
    , localOutput
    , runLocalIO
    ) where

import Polysemy (Member, reinterpret2, Sem)
import Polysemy.Input (Input, input, runInputConst)
import qualified Polysemy.Internal as PI  -- God help us.
import Polysemy.Output (Output, output, runOutputList)

import Data (Located(Located), Party, pretend)


-------- Effect Signatures --------

data Local (i :: *) (o :: *) m a where -- no membership/subset constraints?
  LocalInput :: forall (p :: Party) i o m.
                Local i o m (Located '[p] i)
  LocalOutput :: forall (p :: Party) i o m.
                 Located '[p] o -> Local i o m ()

localInput :: forall (p :: Party) i o r.
              (Member (Local i o) r) =>
              Sem r (Located '[p] i)
localInput = PI.send $ LocalInput
localOutput :: forall (p :: Party) i o r.
               (Member (Local i o) r) =>
               Located '[p] o -> Sem r ()
localOutput x = PI.send $ LocalOutput x


-------- Handlers --------

runLocalIO :: forall i o r a.
              (forall (p :: Party). Bool)
              -> i
              -> Sem (Local i o ': r) a
              -> Sem r ([o], a)
runLocalIO me i = runOutputList . (runInputConst i) . interpretMyIO
  where myOutput :: forall (p :: Party).
                     Located '[p] o -> Sem (Input i ': Output o ': r) ()
        -- I'm avoiding binding to preserve lazyness; IDK if it matters.
        myOutput = if (me @p) then (\case Located o -> output o) else (const $ return ())
        myInput :: forall (p :: Party) m.
                   Local i o m (Located '[p] i) -> Sem (Input i ': Output o ': r) (Located '[p] i)
        myInput _ = if (me @p) then (Located <$> input) else (return pretend)
        interpretMyIO :: forall b.
                         Sem (Local i o ': r) b
                         -> Sem (Input i ': Output o ': r) b
        interpretMyIO = reinterpret2 $ \case
          li@(LocalInput) -> myInput li
          LocalOutput l -> myOutput l


