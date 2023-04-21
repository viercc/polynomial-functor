{-

Implementation of
"Directed Containers as Categories," D. Ahman and T. Uustalu, EPTCS 207, 2016, pp. 89-98

https://arxiv.org/abs/1604.01187

-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE DerivingStrategies #-}
module PolyComonad where

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Type)

import Control.Comonad

import BabySingleton

type Poly :: (k -> k -> Type) -> Type -> Type
data Poly (cat :: k -> k -> Type) r where
    MkPoly :: Sing k a -> (forall b. Sing k b -> cat a b -> r) -> Poly cat r

instance Functor (Poly cat) where
    fmap f (MkPoly sa k) = MkPoly sa (fmap (fmap f) k)

instance Category cat => Comonad (Poly (cat :: k -> k -> Type)) where
    extract :: forall r. Poly cat r -> r
    extract (MkPoly (sa :: Sing k a) g) = g sa (id :: cat a a)

    duplicate :: forall r. Poly cat r -> Poly cat (Poly cat r)
    duplicate (MkPoly sa k) = MkPoly sa \sb ab -> MkPoly sb \sc bc -> k sc (bc . ab)
