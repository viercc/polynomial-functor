{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}

module Data.Functor.Polynomial(
  HasSNat(..),
  Poly(..),
  Polynomial(..),

  Pow(..),

  TagFn, TagV(), TagK(..), TagSum(..), TagMul(..), TagPow(..), TagComp(..)
) where

import Data.Functor.Identity(Identity(..))
import Data.Functor.Classes ( Eq1(..), eq1 )

import Data.Finitary
import Data.Finite
import Data.Finite.Extra (SNat (..), absurdFinite, combineSumS, separateSumS)
import Data.Kind (Type)

import Data.Type.Equality ((:~:)(..), TestEquality(..))
import GHC.Generics
import GHC.TypeLits.Witnesses
import GHC.TypeNats

import qualified Data.Vector.Sized as SV

-- | @'HasSNat' t@ indicates @t n@ contains sufficient data
--   to construct the @'SNat' n@ value.
--
--   Such @t@ can be seen as a type of inverse images of a function @α :: U -> Nat@ on some type @U@.
--   In other words, the type @t n@ corresponds to @α⁻¹(n)@, a subset of @U@ such that @x ∈ α⁻¹(n)@ if and only if @α x == n@.
class HasSNat t where
  toSNat :: t n -> SNat n

instance HasSNat SNat where
  toSNat = id

-- | Uniformly represented polynomial functor.
--
--   Given a @'HasSNat' tag@ instance, @Poly tag@ is a polynomial functor.
--   When @tag@ is the inverse images of @α :: U -> Nat@, @Poly@ is isomorphic to:
--
--   > Poly tag x
--   >  = ∑{n :: Nat} (tag n, x^n)
--   >  = ∑{n :: Nat} ∑{u :: U, α(u) == n} x^n
--   >  = ∑{u :: U} x^(α(u))
type Poly :: (Nat -> Type) -> Type -> Type
data Poly tag x where
  P :: tag n -> (Finite n -> x) -> Poly tag x

deriving instance Functor (Poly tag)

instance HasSNat tag => Foldable (Poly tag) where
  null (P tag _) = case toSNat tag of
    Zero -> True
    _    -> False
  length (P tag _) = fromIntegral (fromSNat (toSNat tag))

  foldMap f (P tag rep) = foldMap (f . rep) (withKnownNat (toSNat tag) finites)

instance HasSNat tag => Traversable (Poly tag) where
  traverse f (P tag rep) = P tag <$> traverseFiniteFn (toSNat tag) f rep

traverseFiniteFn :: (Applicative g) => SNat n -> (a -> g b) -> (Finite n -> a) -> g (Finite n -> b)
traverseFiniteFn SNat f fromN = fmap SV.index $ traverse f (SV.generate fromN)

instance (Eq x, TestEquality tag, HasSNat tag) => Eq (Poly tag x) where
  (==) = eq1

instance (TestEquality tag, HasSNat tag) => Eq1 (Poly tag) where
  liftEq eq = eqP
    where
      eqP (P tag rep) (P tag' rep') = case testEquality tag tag' of
        Nothing -> False
        Just Refl -> all (\i -> rep i `eq` rep' i) (withKnownNat (toSNat tag) finites)

-- | A class for 'Functor' which can be represented as 'Poly'.
class (Functor f, HasSNat (Tag f)) => Polynomial f where
  type Tag f :: Nat -> Type

  toPoly :: f x -> Poly (Tag f) x
  fromPoly :: Poly (Tag f) x -> f x

instance Finitary r => Polynomial ((->) r) where
  type Tag ((->) r) = (:~:) (Cardinality r)

  toPoly f = P Refl (f . fromFinite)
  fromPoly (P Refl f) r = f (toFinite r)

-- | @TagFn n@ represents just a natural number @n@. In other words, function @α@ from a singleton set pointing to @n@:
--
--   > α = const n :: () -> Nat
--
--   This is the tag of @(->) r@ functor, where @r@ is 'Finitary' type of cardinality @n@.
--   It's also the tag of @U1@ and @Par1@,
--   by being isomorphic to @(->) Void@ and @(->) ()@ respectively.
type TagFn :: Nat -> Nat -> Type
type TagFn = (:~:)

-- | Instance for 'TagFn'
instance KnownNat n => HasSNat ((:~:) n) where
  toSNat Refl = SNat

-- | @TagV n@ is empty type for any @n@. It's the inverse images of the empty function @α = absurd :: ∅ -> Nat@. 
--
--   This is the tag of 'V1'.
data TagV (n :: Nat)

instance HasSNat TagV where
  toSNat v = case v of {}

instance TestEquality TagV where
  testEquality v = case v of {}

-- | @TagK c n@ represents a constant function:
--   
--   > α = const 0 :: c -> Nat
--   
--   This is the tag of 'K1'.
type TagK :: Type -> Nat -> Type
data TagK c n where
  TagK :: c -> TagK c 0

deriving instance Eq c => Eq (TagK c n)

instance HasSNat (TagK c) where
  toSNat (TagK _) = SNat

instance Eq c => TestEquality (TagK c) where
  testEquality (TagK c) (TagK c')
      | c == c' = Just Refl
      | otherwise = Nothing

-- | When @t1, t2@ represents a function @α1, α2@ respectively,
--   
--   > α1 :: U -> Nat
--   > α2 :: V -> Nat
--   
--   @TagSum t1 t2@ represents @either α1 α2@.
--   
--   > either α1 α2 :: Either U V -> Nat
--
--   This is the tag of @f :+: g@, when @t1, t2@ is the tag of @f, g@ respectively.
type TagSum :: (Nat -> Type) -> (Nat -> Type) -> Nat -> Type
data TagSum t1 t2 n = TagLeft (t1 n) | TagRight (t2 n)

instance (HasSNat t1, HasSNat t2) => HasSNat (TagSum t1 t2) where
  toSNat (TagLeft t1) = toSNat t1
  toSNat (TagRight t2) = toSNat t2

instance (TestEquality t1, TestEquality t2) => TestEquality (TagSum t1 t2) where
  testEquality (TagLeft t1) (TagLeft t1') = fmap (\Refl -> Refl) $ testEquality t1 t1'
  testEquality (TagRight t2) (TagRight t2') = fmap (\Refl -> Refl) $ testEquality t2 t2'
  testEquality _ _ = Nothing

-- |  When @t1, t2@ represents a function @α1, α2@ respectively,
--   
--   > α1 :: U -> Nat
--   > α2 :: V -> Nat
--   
--   @TagMul t1 t2@ represents the function @α@ on the direct product of @U, V@:
--   
--   > α :: (U,V) -> Nat
--   > α(u,v) = α u + β v
--   
--   This is the tag of @f :*: g@ when @t1, t2@ is the tag of @f, g@ respectively.
data TagMul f g x where
  TagMul :: !(f x) -> !(g y) -> TagMul f g (x + y)

instance (HasSNat t1, HasSNat t2) => HasSNat (TagMul t1 t2) where
  toSNat (TagMul t1 t2) = toSNat t1 %+ toSNat t2

instance (TestEquality t1, TestEquality t2) => TestEquality (TagMul t1 t2) where
  testEquality (TagMul t1 t2) (TagMul t1' t2') =
    do Refl <- testEquality t1 t1'
       Refl <- testEquality t2 t2'
       pure Refl

-- | When @t@ represents @(U,α :: U -> Nat)@,
--   @TagPow n t xs@ represents @α^n@:
--
--   > α^n :: U^n -> Nat
--   > α^n(u1, u2, ..., u_n) = α u1 + α u2 + ... + α u_n
--
--   This is the tag of @Pow n f@ when @t@ is the tag of @f@.
data TagPow n t xs where
  PowZeroTag :: TagPow 0 t 0
  PowSuccTag :: KnownNat n => TagPow n t xs -> t x -> TagPow (n + 1) t (xs + x)

instance (HasSNat t) => HasSNat (TagPow n t) where
  toSNat PowZeroTag = Zero
  toSNat (PowSuccTag l r) = toSNat l %+ toSNat r

instance TestEquality t => TestEquality (TagPow n t) where
  testEquality t t' = fmap snd (testEqualityPow t t')

testEqualityPow :: TestEquality t => TagPow n t xs -> TagPow n' t xs' -> Maybe (n :~: n', xs :~: xs')
testEqualityPow PowZeroTag PowZeroTag = Just (Refl, Refl)
testEqualityPow (PowSuccTag ts t) (PowSuccTag ts' t') =
  do Refl <- testEquality t t'
     (Refl, Refl) <- testEqualityPow ts ts'
     pure (Refl, Refl)
testEqualityPow _ _ = Nothing

-- | When @t, u@ is the tag of @f, g@ respectively,
--   @TagComp t u@ is the tag of @f :.: g@.
data TagComp t u n where
  TagComp :: t a -> TagPow a u n -> TagComp t u n

instance (HasSNat t, HasSNat u) => HasSNat (TagComp t u) where
  toSNat (TagComp t pu) = withKnownNat (toSNat t) (toSNat pu)

instance (TestEquality t, TestEquality u) => TestEquality (TagComp t u) where
  testEquality (TagComp t pu) (TagComp t' pu') =
    do Refl <- testEquality t t'
       Refl <- testEquality pu pu'
       pure Refl

---- Instances ----
instance Polynomial Identity where
  type Tag Identity = TagFn 1

  toPoly (Identity x) = P Refl (const x)
  fromPoly (P Refl e) = Identity (e minBound)

instance Polynomial [] where
  type Tag [] = SNat

  toPoly :: forall x. [x] -> Poly SNat x
  toPoly xs = SV.withSizedList xs $ \v -> P SNat (SV.index v)

  fromPoly :: forall x. Poly SNat x -> [x]
  fromPoly (P sn f) = f <$> withKnownNat sn finites

instance Polynomial V1 where
  type Tag V1 = TagV
  toPoly v = case v of { }
  fromPoly (P v _) = case v of { }

instance Polynomial U1 where
  type Tag U1 = TagFn 0

  toPoly _ = P Refl absurdFinite
  fromPoly _ = U1

instance Polynomial (K1 i c) where
  type Tag (K1 i c) = TagK c

  toPoly (K1 c) = P (TagK c) absurdFinite
  fromPoly (P (TagK c) _) = K1 c

instance Polynomial f => Polynomial (M1 i c f) where
  type Tag (M1 i c f) = Tag f
  fromPoly = M1 . fromPoly
  toPoly = toPoly . unM1

instance Polynomial f => Polynomial (Rec1 f) where
  type Tag (Rec1 f) = Tag f
  fromPoly = Rec1 . fromPoly
  toPoly = toPoly . unRec1

instance Polynomial Par1 where
  type Tag Par1 = TagFn 1

  toPoly (Par1 x) = P Refl (const x)
  fromPoly (P Refl x') = Par1 (x' (finite 0))

instance (Polynomial f, Polynomial g) => Polynomial (f :+: g) where
  type Tag (f :+: g) = TagSum (Tag f) (Tag g)

  toPoly (L1 fx) = case toPoly fx of
    P tag rep -> P (TagLeft tag) rep
  toPoly (R1 gx) = case toPoly gx of
    P tag rep -> P (TagRight tag) rep

  fromPoly (P (TagLeft tag) rep) = L1 (fromPoly (P tag rep))
  fromPoly (P (TagRight tag) rep) = R1 (fromPoly (P tag rep))

instance (Polynomial f, Polynomial g) => Polynomial (f :*: g) where
  type Tag (f :*: g) = TagMul (Tag f) (Tag g)

  toPoly (fx :*: gx) =
    case (toPoly fx, toPoly gx) of
      (P tagF repF, P tagG repG) ->
        P (TagMul tagF tagG) (either repF repG . separateSumS (toSNat tagF) (toSNat tagG))

  fromPoly (P (TagMul tagF tagG) rep) =
    let combine = combineSumS (toSNat tagF) (toSNat tagG)
        pf = P tagF (rep . combine . Left)
        pg = P tagG (rep . combine . Right)
     in fromPoly pf :*: fromPoly pg

-- | @Pow n f = f :*: f :*: ...(n)... :*: f@
newtype Pow n f x = Pow (Finite n -> f x)

deriving instance Functor f => Functor (Pow n f)

instance (KnownNat n, Polynomial f) => Polynomial (Pow n f) where
  type Tag (Pow n f) = TagPow n (Tag f)

  toPoly :: forall x. Pow n f x -> Poly (TagPow n (Tag f)) x
  toPoly (Pow e) = case SNat @n of
    Zero -> P PowZeroTag absurdFinite
    Succ SNat ->
      let fs = Pow (e . weaken)
          f = e (maxBound @(Finite n))
      in case (toPoly fs, toPoly f) of
        (P tagFs repFs, P tagF repF) ->
          P (PowSuccTag tagFs tagF) (either repFs repF . separateSumS (toSNat tagFs) (toSNat tagF))

  fromPoly :: forall x. Poly (TagPow n (Tag f)) x -> Pow n f x
  fromPoly (P tag rep) = case tag of
    PowZeroTag -> Pow absurdFinite
    PowSuccTag tagFs tagF ->
      let combine = combineSumS (toSNat tagFs) (toSNat tagF)
          Pow e' = fromPoly (P tagFs (rep . combine . Left))
          f      = fromPoly (P tagF  (rep . combine . Right))
       in Pow (maybe f e' . strengthen)

instance (Polynomial f, Polynomial g) => Polynomial (f :.: g) where
  type Tag (f :.: g) = TagComp (Tag f) (Tag g)

  toPoly :: forall x. (f :.: g) x -> Poly (TagComp (Tag f) (Tag g)) x
  toPoly (Comp1 fgy) = case toPoly fgy of
    P tagF repF -> withKnownNat (toSNat tagF) $
      case toPoly (Pow repF) of
        P tagPowG repPow -> P (TagComp tagF tagPowG) repPow

  fromPoly :: forall x. Poly (TagComp (Tag f) (Tag g)) x -> (f :.: g) x
  fromPoly (P (TagComp tagF tagPowG) rep) =
    withKnownNat (toSNat tagF) $
      case fromPoly (P tagPowG rep) of
        Pow repF -> Comp1 $ fromPoly (P tagF repF)

---- Generic definitions ----
instance (Generic1 f, Polynomial (Rep1 f)) => Polynomial (Generically1 f) where
  type Tag (Generically1 f) = Tag (Rep1 f)

  toPoly (Generically1 fx) = toPoly (from1 fx)
  fromPoly p = Generically1 $ to1 (fromPoly p)

deriving via (Generically1 Maybe)
  instance Polynomial Maybe

deriving via (Generically1 (Either a))
  instance Polynomial (Either a)

deriving via (Generically1 ((,) a))
  instance Polynomial ((,) a)