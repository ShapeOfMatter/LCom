module Examples
    ( shareAnInt
    , threePartyXOR
    ) where

import Data.Bits (xor)
import Polysemy (Member, Sem)
import System.Random (random, RandomGen)

import LCom (Address, Communicate, downcast, Located, Local, localInput, localOutput, locally, Party, send, Subset)
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
                   total <- locally $ xor <$> total0 <*> (xor <$> total1 <*> total2)
                   return total
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






