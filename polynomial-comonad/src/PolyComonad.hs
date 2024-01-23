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

import Data.Singletons
import Data.Singletons.Sigma

type Poly :: (k -> k -> Type) -> Type -> Type
data Poly (cat :: k -> k -> Type) r where
    MkPoly
      :: forall k (cat :: k -> k -> Type) (r :: Type) (a :: k).
         Sing a -> (Sigma k (TyCon (cat a)) -> r)
      -> Poly cat r

instance Functor (Poly cat) where
    fmap f (MkPoly sa k) = MkPoly sa (f . k)

instance Category cat => Comonad (Poly (cat :: k -> k -> Type)) where
    extract :: forall r. Poly cat r -> r
    extract (MkPoly sa g) = g (sa :&: id)

    duplicate :: forall r. Poly cat r -> Poly cat (Poly cat r)
    duplicate (MkPoly sa k) = MkPoly sa \(sb :&: ab) -> MkPoly sb \(sc :&: bc) -> k (sc :&: (bc . ab))
