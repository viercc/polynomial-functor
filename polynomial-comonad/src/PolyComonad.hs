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

import Type.Reflection
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

-- * Trivial example: Discrete category on @k@ corresponds to @Comonad ((,) k)@

-- | Discrete categories on kind @k@
type Discrete :: k -> k -> Type
type Discrete = (:~:)

-- | @Poly |k| r ~ (k, r) ~ Env k r@
discreteCat :: Demote k => (Val k, r) -> Poly (Discrete @k) r
discreteCat (x, r) = toSing x \sx -> MkPoly sx \_ Refl -> r

runDiscreteCat :: Demote k => Poly (Discrete @k) r -> (Val k, r)
runDiscreteCat (MkPoly sx k) = (fromSing sx, k sx Refl)

-- * The other trivial example: one-object category

newtype OneObject m (a :: ()) (b :: ()) = OneObject m
    deriving stock (Show)
    deriving newtype (Eq, Ord, Semigroup, Monoid)

instance Monoid m => Category (OneObject m) where
    id = OneObject mempty
    OneObject m1 . OneObject m2 = OneObject (m1 <> m2)

-- | @Poly (OneObject m) r ~ (m -> r) ~ Traced m r@
oneObjectCat :: (m -> r) -> Poly (OneObject m) r
oneObjectCat f = MkPoly SU \SU (OneObject m) -> f m

runOneObjectCat :: Poly (OneObject m) r -> m -> r
runOneObjectCat (MkPoly _ f) = f SU . OneObject

-- * A small but non-trivial example

data H r = H1 r | H2 r r
    deriving Functor

instance Comonad H where
    extract (H1 r) = r
    extract (H2 r _) = r

    duplicate (H1 r0) = H1 (H1 r0)
    duplicate (H2 r1 r0) = H2 (H2 r1 r0) (H1 r0)

-- |
--   > False ---> True 
--   >   ↺         ↺
--   
-- Note: Roughly speaking, there are only three values in
-- types @Implies b1 b2@, where @b1, b2@ are chosen from either @False@ or @True@.
--
-- @
-- ImpId :: Implies False False
-- ImpId :: Implies True True
-- ImpFT :: Implies False True
-- @
type Implies :: Bool -> Bool -> Type
data Implies x y where
    ImpId :: Implies x x
    ImpFT :: Implies False True

instance Category Implies where
    id = ImpId
    ImpId . g = g
    ImpFT . ImpId = ImpFT

-- | 'Poly' 'Implies' is isomorphic to 'H', including its 'Comonad' instance.
toH :: Poly Implies r -> H r
toH (MkPoly STrue k) = H1 (k STrue ImpId)
toH (MkPoly SFalse k) = H2 (k SFalse ImpId) (k STrue ImpFT)

fromH :: H r -> Poly Implies r
fromH (H1 r0) = MkPoly STrue \_ tt -> case tt of
    ImpId -> r0
fromH (H2 r1 r0) = MkPoly SFalse \_ fz -> case fz of
    ImpId -> r1
    ImpFT -> r0
