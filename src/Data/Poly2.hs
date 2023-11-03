{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}

module Data.Poly2 where

import Data.Kind (Constraint, Type)
import Data.Type.Equality
import Data.Void
import GHC.Generics ((:*:) (..), type (:.:) (..))
import Data.Functor.Day
import Data.Reflection

import Data.Additive

-- * Type of polynomials (most generic)

data Poly t a where
  Poly :: t x -> (x -> a) -> Poly t a

deriving instance Functor (Poly t)

-- * Summable types

type Summable :: Type -> Constraint
class Summable x where
  type Pow (x :: Type) (t :: Type -> Type) :: Type -> Type
  tabulateP :: (x -> Poly t a) -> Poly (Pow x t) a
  indexP :: Poly (Pow x t) a -> (x -> Poly t a)

  summation :: forall t f z. Additive f => (forall y. t y -> f y) -> Pow x t z -> f z

instance Summable () where
  type Pow () t = t
  tabulateP f = f ()
  indexP pa _ = pa
  summation h = h

instance Summable Void where
  type Pow Void _ = (:~:) Void
  tabulateP _ = Poly Refl absurd
  indexP _ = absurd
  summation _ Refl = zeroA

instance (Summable x, Summable y) => Summable (x + y) where
  type Pow (x + y) t = TagMul (Pow x t) (Pow y t)
  tabulateP f =
    case (tabulateP (f . Left), tabulateP (f . Right)) of
      (Poly tx fx, Poly ty fy) ->
        Poly (TagMul tx ty) (either fx fy)

  indexP (Poly (TagMul tx ty) f) xy = case xy of
    Left x  -> indexP (Poly tx (f . Left)) x
    Right y -> indexP (Poly ty (f . Right)) y

  summation h (TagMul tx ty) = summation @x h tx `sumA` summation @y h ty

instance (Summable x, Summable y) => Summable (x, y) where
  type Pow (x,y) t = Pow x (Pow y t)
  tabulateP f = tabulateP (\x -> tabulateP (\y -> f (x,y)))
  indexP (Poly txy f) (x,y) = Poly txy f `indexP` x `indexP` y
  summation h = summation @x (summation @y h)

-- * Tags

type (+) = Either

data TagMul f g a where
  TagMul :: f a -> g b -> TagMul f g (a + b)

data TagDay t u x where
  TagDay :: t a -> u b -> TagDay t u (a,b)

data TagComp t u x where
  TagComp :: t x -> Pow x u y -> TagComp t u y

-- * IsSummable and AllSummable

data IsSummable x where
  IsSummable :: Summable x => IsSummable x

withSummable :: IsSummable x -> (Summable x => r) -> r
withSummable IsSummable r = r

instance Additive IsSummable where
  zeroA = IsSummable
  sumA IsSummable IsSummable = IsSummable

class AllSummable t where
  getSummable :: t x -> IsSummable x

instance Summable x => AllSummable ((:~:) x) where
  getSummable Refl = IsSummable

instance (AllSummable t, AllSummable u) => AllSummable (TagMul t u) where
  getSummable (TagMul ta ub) = sumA (getSummable ta) (getSummable ub)

instance (AllSummable t, AllSummable u) => AllSummable (TagDay t u) where
  getSummable (TagDay ta ub) = withSummable (getSummable ta) $ withSummable (getSummable ub) IsSummable

instance (AllSummable t, AllSummable u) => AllSummable (TagComp t u) where
  getSummable (TagComp tx xuy) = case getSummable tx of
    IsSummable @x -> summation @x (getSummable @u) xuy

-- Isomorphisms

productPoly :: (Poly t :*: Poly u) a -> Poly (TagMul t u) a
productPoly (Poly t f :*: Poly u g) = Poly (TagMul t u) (either f g)

productPoly' :: Poly (TagMul t u) a -> (Poly t :*: Poly u) a
productPoly' (Poly (TagMul t u) f) = Poly t (f . Left) :*: Poly u (f . Right)

dayPoly :: Day (Poly t) (Poly u) a -> Poly (TagDay t u) a
dayPoly (Day (Poly t f) (Poly u g) op) = Poly (TagDay t u) (\(x,y) -> op (f x) (g y))

dayPoly' :: Poly (TagDay t u) a -> Day (Poly t) (Poly u) a
dayPoly' (Poly (TagDay t u) f) = Day (Poly t id) (Poly u id) (curry f)

composePoly :: AllSummable t => (Poly t :.: Poly u) a -> Poly (TagComp t u) a
composePoly (Comp1 (Poly tx f)) = withSummable (getSummable tx) $
  case tabulateP f of
    Poly uy g -> Poly (TagComp tx uy) g

composePoly' :: AllSummable t => Poly (TagComp t u) a -> (Poly t :.: Poly u) a
composePoly' (Poly (TagComp tx xuy) g) = withSummable (getSummable tx) $
  Comp1 $ Poly tx $ \x -> indexP (Poly xuy g) x


-- Utility instances

instance Summable Bool where
  type Pow Bool t = TagMul t t
  tabulateP f = case (f False, f True) of
    (Poly t0 f0, Poly t1 f1) -> Poly (TagMul t0 t1) (either f0 f1)
  indexP (Poly (TagMul t0 t1) f) b = if b then Poly t1 (f . Right) else Poly t0 (f . Left)

  summation h (TagMul t0 t1) = h t0 `sumA` h t1

instance Summable x => Summable (Maybe x) where
  type Pow (Maybe x) t = TagMul t (Pow x t)
  tabulateP f = case (f Nothing, tabulateP (f . Just)) of
    (Poly t0 f0, Poly tx fx) -> Poly (TagMul t0 tx) (either f0 fx)
  indexP (Poly (TagMul t0 tx) f) mx = case mx of
    Nothing -> Poly t0 (f . Left)
    Just x  -> indexP (Poly tx (f . Right)) x

  summation h (TagMul t0 tx) = h t0 `sumA` summation @x h tx

-- Natural numbers and List polynomials

data Nat' = Z | S Nat'

data SNat' (n :: Nat') where
  IZ :: SNat' 'Z
  IS :: SNat' n -> SNat' ('S n)

data Finite (n :: Nat') where
  FZ :: Finite ('S n)
  FS :: Finite n -> Finite ('S n)

absurdFinite' :: Finite 'Z -> a
absurdFinite' i = case i of { }

data PowNat (n :: Nat') t x where
  PowNatZ :: PowNat 'Z t Void
  PowNatS :: t a -> PowNat n t b -> PowNat ('S n) t (a + b)

instance Given (SNat' n) => Summable (Finite n) where
  type Pow (Finite n) t = PowNat n t
  tabulateP = tabulateNat (given @(SNat' n))
  indexP = indexNat
  summation = summationNat

tabulateNat :: SNat' n -> (Finite n -> Poly t a) -> Poly (PowNat n t) a
tabulateNat IZ _ = Poly PowNatZ absurd
tabulateNat (IS m) f =
  case (f FZ, tabulateNat m (f . FS)) of
    (Poly t0 f0, Poly tm fm) -> Poly (PowNatS t0 tm) (either f0 fm)

indexNat :: Poly (PowNat n t) a -> Finite n -> Poly t a
indexNat (Poly ntx f) i = case ntx of
  PowNatZ -> absurdFinite' i
  PowNatS t0 tm -> case i of
    FZ -> Poly t0 (f . Left)
    FS i' -> indexNat (Poly tm (f . Right)) i'

summationNat :: Additive f => (forall a. t a -> f a) -> PowNat n t b -> f b
summationNat _ PowNatZ = zeroA
summationNat h (PowNatS t0 tm) = h t0 `sumA` summationNat h tm

data TagList a where
  TagList :: SNat' n -> TagList (Finite n)

instance AllSummable TagList where
  getSummable (TagList sn) = give sn IsSummable

listToPoly :: [a] -> Poly TagList a
listToPoly = foldr consP nilP
  where
    nilP :: forall b. Poly TagList b
    nilP = Poly (TagList IZ) absurdFinite'

    consP :: forall b. b -> Poly TagList b -> Poly TagList b
    consP a (Poly (TagList sn) f) = Poly (TagList (IS sn)) $ \case
        FZ -> a
        FS i' -> f i'

polyToList :: Poly TagList a -> [a]
polyToList (Poly (TagList sn) f) = case sn of
  IZ -> []
  IS sm -> f FZ : polyToList (Poly (TagList sm) (f . FS))
