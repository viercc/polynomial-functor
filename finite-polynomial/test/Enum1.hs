{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Enum1 where

import GHC.Generics
import Data.Traversable (mapAccumL)

type Enum1 f = forall a. [a] -> [f a]

prodEnum :: Enum1 f -> Enum1 g -> Enum1 (f :*: g)
prodEnum genF genG as = (:*:) <$> genF as <*> genG as

sumEnum :: Enum1 f -> Enum1 g -> Enum1 (f :+: g)
sumEnum genF genG as = (L1 <$> genF as) ++ (R1 <$> genG as)

compEnum :: Enum1 f -> Enum1 g -> Enum1 (f :.: g)
compEnum genF genG as = Comp1 <$> genF (genG as)

skolem :: Traversable f => Enum1 f -> [f Int]
skolem genF = ixes <$> genF [()]

ixes :: Traversable t => t () -> t Int
ixes = snd . mapAccumL (\s _ -> (1 + s, 1 + s)) 0
