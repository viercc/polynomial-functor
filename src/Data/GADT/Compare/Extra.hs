{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
module Data.GADT.Compare.Extra where

import Data.GADT.Compare ( GOrdering(..) )

fromOrdering :: Ordering -> GOrdering a a
fromOrdering ordering = case ordering of
    LT -> GLT
    EQ -> GEQ
    GT -> GGT

infixr 3 >>?
(>>?) :: forall k (a :: k) b a' b'. GOrdering a b -> ((a ~ b) => GOrdering a' b') -> GOrdering a' b'
GLT >>? _ = GLT
GEQ >>? r = r
GGT >>? _ = GGT
