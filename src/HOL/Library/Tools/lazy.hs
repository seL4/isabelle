{- Author: Pascal Stoop, ETH Zurich
   Author: Andreas Lochbihler, Digital Asset -}

module Lazy(Lazy, delay, force) where

newtype Lazy a = Lazy a
delay f = Lazy (f ())
force (Lazy x) = x
