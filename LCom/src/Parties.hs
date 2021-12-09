module Parties where

import Data.Type.Nat (Nat(Z,S))

import LCom (Party(Party))

type Party0 = 'Party                                                  'Z
type Party1 = 'Party                                              ('S 'Z)
type Party2 = 'Party                                          ('S ('S 'Z))
type Party3 = 'Party                                      ('S ('S ('S 'Z)))
type Party4 = 'Party                                  ('S ('S ('S ('S 'Z))))
type Party5 = 'Party                              ('S ('S ('S ('S ('S 'Z)))))
type Party6 = 'Party                          ('S ('S ('S ('S ('S ('S 'Z))))))
type Party7 = 'Party                      ('S ('S ('S ('S ('S ('S ('S 'Z)))))))
type Party8 = 'Party                  ('S ('S ('S ('S ('S ('S ('S ('S 'Z))))))))
type Party9 = 'Party              ('S ('S ('S ('S ('S ('S ('S ('S ('S 'Z)))))))))
type Party10 = 'Party         ('S ('S ('S ('S ('S ('S ('S ('S ('S ('S 'Z))))))))))
type Party11 = 'Party     ('S ('S ('S ('S ('S ('S ('S ('S ('S ('S ('S 'Z)))))))))))
type Party12 = 'Party ('S ('S ('S ('S ('S ('S ('S ('S ('S ('S ('S ('S 'Z))))))))))))

