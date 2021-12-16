module Examples
    ( raceTo100
    , runInputOutputAsIO
    , shareAnInt
    , threePartyXOR
    ) where

import Data.Bits (xor)
import Polysemy (Embed, embed, interpret, Member, reinterpret, Sem, subsume_)
import Polysemy.Input (Input(Input))
import Polysemy.Output (Output(Output))
import Polysemy.State (execState, modify, State)
import System.Random (random, randomR, RandomGen)

import LCom (Address, Communicate, downcast, Located, Local, localInput, localOutput, locally, Party, runClique, send, Subset)
import Parties (Party0, Party1, Party2)

type Couple = '[Party0, Party1]

shareAnInt :: Sem '[Local Int Int, Communicate Couple Int] Int
shareAnInt = do i <- localInput @Party0
                shared <- send @Couple i
                localOutput @Party1 (downcast shared)
                opened <- locally shared
                return opened

type Trio = '[Party0, Party1, Party2]

threePartyXOR :: forall g.
                 (RandomGen g) =>
                 Sem '[Local (Bool, g) Bool, Communicate Trio Bool] Bool
threePartyXOR = do inputs0 <- setup @Party0
                   inputs1 <- setup @Party1
                   inputs2 <- setup @Party2
                   (message00, message10, message20) <- round1 @Party0 @Party1 @Party2 inputs0
                   (message11, message01, message21) <- round1 @Party1 @Party0 @Party2 inputs1
                   (message22, message02, message12) <- round1 @Party2 @Party0 @Party1 inputs2
                   total0 <- round2 (message00, message01, message02)
                   total1 <- round2 (message10, message11, message12)
                   total2 <- round2 (message20, message21, message22)
                   let total = xor <$> total0 <*> (xor <$> total1 <*> total2)
                   localOutput @Party0 $ downcast total
                   localOutput @Party1 $ downcast total
                   localOutput @Party2 $ downcast total
                   locally total
  where setup :: forall (p :: Party) r.
                 (Address p,
                  Member (Local (Bool, g) Bool) r) =>
                 Sem r (Located '[p] Bool, Located '[p] Bool, Located '[p] Bool)
        setup = do pInput <- localInput @p
                   let values = (do  -- This is in the `instance Monad (Located '[p])`:
                                     secret <- fst <$> pInput
                                     rng <- snd <$> pInput
                                     let (randomA :: Bool, rng') = random rng
                                     let (randomB :: Bool, _) = random rng'
                                     return (secret, randomA, randomB)
                                )
                   return (  -- Obviously there are better ways to write this, but none are in arms reach ATM.
                     (\(s, _, _) -> s) <$> values,
                     (\(_, rA, _) -> rA) <$> values,
                     (\(_, _, rB) -> rB) <$> values)
        round1 :: forall (sender :: Party) (a :: Party) (b :: Party) r.
                  (Address sender,
                   Address a,
                   Address b,
                   Subset '[sender] Trio,
                   Subset '[a] Trio,
                   Subset '[b] Trio,
                   Member (Communicate Trio Bool) r) =>
                  (Located '[sender] Bool, Located '[sender] Bool, Located '[sender] Bool) ->
                  Sem r (Located '[sender] Bool, Located '[a] Bool, Located '[b] Bool)
        round1 (secret, randomA, randomB) = do let keepForSelf = xor <$> secret <*> (xor <$> randomA <*> randomB)
                                               messageToA <- send @'[a] randomA
                                               messageToB <- send @'[b] randomB
                                               return (keepForSelf, messageToA, messageToB)
        round2 :: forall (recipient :: Party) r.
                  (Address recipient,
                   Subset '[recipient] Trio,
                   Member (Communicate Trio Bool) r) =>
                  (Located '[recipient] Bool, Located '[recipient] Bool, Located '[recipient] Bool) ->
                  Sem r (Located Trio Bool)
        round2 (fromA, fromB, fromC) = do let total = xor <$> fromA <*> (xor <$> fromB <*> fromC)
                                          send @Trio total

raceTo100 :: forall g.
             (RandomGen g) =>
             Sem '[Local g String, Communicate Trio Int] Int
raceTo100 = execState 0 $ subsume_ race
  where race = do rng0 <- localInput @Party0
                  rng1 <- localInput @Party1
                  rng2 <- localInput @Party2
                  turn startingBase rng0 rng1 rng2
        turn :: forall p1 p2 p3.
                (Address p1, Subset '[p1] Trio,
                 Address p2, Subset '[p2] Trio,
                 Address p3, Subset '[p3] Trio) =>
                Int ->
                Located '[p1] g -> Located '[p2] g -> Located '[p3] g ->
                Sem '[Communicate Trio Int, State Int, Local g String] ()
        turn base rng1 rng2 rng3 = do modify (+ 1)
                                      p1Trun <- runClique (
                                        do localRNG <- locally rng1
                                           let (roll, localRNG') = randomR (base - startingBase, 100) localRNG
                                           let progress = roll > base
                                           localOutput @p1 $ pure $ privateLog progress roll
                                           return (if progress then Just roll else Nothing,
                                                   localRNG')
                                        )
                                      let (mRoll, rng1') = (fst <$> p1Trun, snd <$> p1Trun)
                                      opened <- send @Trio mRoll >>= locally
                                      let base' = maybe base (max base) opened
                                      if base' < 100
                                        then turn base' rng2 rng3 rng1'
                                        else do localOutput @p1 $ pure "I won!"
        privateLog progress roll = "Rolled " <> (show roll) <> "; " <> if progress then "Progress!" else "Failure."
        startingBase = 2

runInputOutputAsIO :: forall o i r a.
                      (Show o,
                       Read i) =>
                      Sem (Input i ': Output o ': r) a ->
                      Sem (Embed IO ': r) a
runInputOutputAsIO = outputToIO . subsume_ . inputToIO
  where inputToIO :: Sem (Input i ': Output o ': r) a -> Sem (Embed IO ': Output o ': r) a
        inputToIO = reinterpret $ \case Input -> embed $ do putStrLn "Input: "
                                                            read <$> getLine
        outputToIO :: Sem (Output o ': Embed IO ': r) a -> Sem (Embed IO ': r) a
        outputToIO = interpret $ \case Output o -> embed $ do putStrLn "Output:"
                                                              print o



