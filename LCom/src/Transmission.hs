module Transmission 
  ( byRecipient
  , bySender
  , message
  , recipients
  , senders
  , Transmission(Transmission)
  ) where

import Data.Function (on)
import Data.List (groupBy, sortOn)

import LCom.Internal.Communicate (Transmission(Transmission))

senders :: Transmission s -> [Integer]
senders (Transmission from _ _) = from
recipients :: Transmission s -> [Integer]
recipients (Transmission _ to _) = to
message :: Transmission s -> Maybe s
message (Transmission _ _ m) = m

byRecipient :: [Transmission s] -> [[Transmission s]]
byRecipient = (groupBy recipientEq) . (sortOn recipient) . splitRecipients
  where recipient = head . recipients
        recipientEq = (==) `on` recipient
        splitRecipients :: [Transmission s] -> [Transmission s]
        splitRecipients transmissions = do Transmission from to m <- transmissions  -- We're in the [] monad!
                                           [Transmission from [p] m | p <- to]

bySender :: [Transmission s] -> [[Transmission s]]
bySender = (groupBy senderEq) . (sortOn sender) . splitSenders
  where sender = head . senders
        senderEq = (==) `on` sender
        splitSenders :: [Transmission s] -> [Transmission s]
        splitSenders transmissions = do Transmission from to m <- transmissions  -- We're in the [] monad!
                                        [Transmission [p] to m | p <- from]

