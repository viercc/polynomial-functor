{-# LANGUAGE BlockArguments #-}
module PolyComonad where

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Type)

import Type.Reflection
import Control.Comonad

type Poly :: (k -> k -> Type) -> Type -> Type
data Poly cat r where
    MkPoly :: (Typeable a) => (forall b. Typeable b => cat a b -> r) -> Poly cat r

instance Functor (Poly cat) where
    fmap f (MkPoly k) = MkPoly (f . k)

instance Category cat => Comonad (Poly cat) where
    extract :: forall r. Poly cat r -> r
    extract (MkPoly @a k) = k (id :: cat a a)

    duplicate :: forall r. Poly cat r -> Poly cat (Poly cat r)
    duplicate (MkPoly @a k) = MkPoly @a \(ab :: cat a b) -> MkPoly @b \(bc :: cat b c) -> k (bc . ab)