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

module Data.Functor.Polynomial where

import Data.Finitary
import Data.Finite
import Data.Finite.Extra (SNat (..), absurdFinite, shiftSRight, weakenS)
import Data.Kind (Type)
import GHC.Generics
import GHC.TypeLits.Witnesses
import GHC.TypeNats

-- | Uniformly represented polynomial functor.
type Poly :: (Nat -> Type) -> Type -> Type
data Poly tag x where
  P :: tag n -> (Finite n -> x) -> Poly tag x

deriving instance Functor (Poly tag)

-- | @'HasSNat' t@ indicates @t n@ contains sufficient data
--   to construct the @'SNat' n@ value.
--
--   Here, @t@ represents a function @α :: U -> Nat@ on some type @U@.
--   A value @x :: t n@ corresponds to a member of @x' :: U@ such that @α x' = n@.
class HasSNat t where
  toSNat :: t n -> SNat n

-- | A class for polynomial 'Functor's @f@
class (Functor f, HasSNat (Tag f)) => Polynomial f where
  type Tag f :: Nat -> Type

  toPoly :: f x -> Poly (Tag f) x
  fromPoly :: Poly (Tag f) x -> f x

-- | @NatEq n@ represents a singleton set equipped with constant function @α = const n :: () -> Nat@
data NatEq n m where
  NRefl :: KnownNat n => NatEq n n

instance HasSNat (NatEq n) where
  toSNat NRefl = SNat

instance Finitary r => Polynomial ((->) r) where
  type Tag ((->) r) = NatEq (Cardinality r)

  toPoly f = P NRefl (f . fromFinite)
  fromPoly (P NRefl f) r = f (toFinite r)

-- | Any empty set have a unique \"function\" @α = absurd :: ∅ -> Nat@
instance HasSNat V1 where
  toSNat = absurdV1

instance Polynomial V1 where
  type Tag V1 = V1
  toPoly = absurdV1
  fromPoly (P tag _) = absurdV1 tag

absurdV1 :: V1 a -> b
absurdV1 v1 = case v1 of {}

-- | @TagK c n@ represents a constant function @α = const n :: c -> Nat@
type TagK :: Type -> Nat -> Type
data TagK c n where
  TagK :: c -> TagK c 0

deriving instance Eq c => Eq (TagK c n)

instance HasSNat (TagK c) where
  toSNat (TagK _) = SNat

instance Polynomial U1 where
  type Tag U1 = TagK ()

  toPoly _ = P (TagK ()) absurdFinite
  fromPoly _ = U1

instance Polynomial (K1 i c) where
  type Tag (K1 i c) = TagK c

  toPoly (K1 c) = P (TagK c) absurdFinite
  fromPoly (P (TagK c) _) = K1 c

instance Polynomial Par1 where
  type Tag Par1 = NatEq 1

  toPoly (Par1 x) = P NRefl (const x)
  fromPoly (P NRefl x') = Par1 (x' (finite 0))

instance (HasSNat t1, HasSNat t2) => HasSNat (t1 :+: t2) where
  toSNat (L1 t1) = toSNat t1
  toSNat (R1 t2) = toSNat t2

instance (Polynomial f, Polynomial g) => Polynomial (f :+: g) where
  type Tag (f :+: g) = (Tag f :+: Tag g)

  toPoly (L1 fx) = case toPoly fx of
    P tag rep -> P (L1 tag) rep
  toPoly (R1 gx) = case toPoly gx of
    P tag rep -> P (R1 tag) rep

  fromPoly (P (L1 tag) rep) = L1 (fromPoly (P tag rep))
  fromPoly (P (R1 tag) rep) = R1 (fromPoly (P tag rep))

-- | When @f@ represents @(U,α :: U -> Nat)@ and @g@ represents @(V,β :: V -> Nat)@,
--   @TagMul f g x@ represents @((U,V), \(u,v) -> α u + β v)@.
data TagMul f g x where
  TagMul :: !(f x) -> !(g y) -> TagMul f g (x + y)

instance (HasSNat t1, HasSNat t2) => HasSNat (TagMul t1 t2) where
  toSNat (TagMul t1 t2) = toSNat t1 %+ toSNat t2

instance (Polynomial f, Polynomial g) => Polynomial (f :*: g) where
  type Tag (f :*: g) = TagMul (Tag f) (Tag g)

  toPoly (fx :*: gx) =
    case (toPoly fx, toPoly gx) of
      (P tagF repF, P tagG repG) ->
        P (TagMul tagF tagG) (either repF repG . withKnownNat (toSNat tagF) separateSum)

  fromPoly (P (TagMul tagF tagG) rep) =
    let n1 = toSNat tagF
        n2 = toSNat tagG
        pf = P tagF (rep . weakenS n1 n2)
        pg = P tagG (rep . shiftSRight n1 n2)
     in fromPoly pf :*: fromPoly pg

-- | When @f@ represents @(U,α :: U -> Nat)@,
--   @TagPow n f xs@ represents @(U^n, \(u1,u2, ..., u_n) -> α u1 + α u2 + ... + α u_n)@.
--
--   In other words, @TagPow n f@ is equivalent to @f `TagMul` f `TagMul` ...(n times)... `TagMul` f@.
data TagPow n f xs where
  PowZeroTag :: TagPow 0 f 0
  PowSuccTag :: !(TagPow n f xs) -> !(f x) -> !(SNat (xs + x)) -> TagPow (n + 1) f (xs + x)

instance (HasSNat f) => HasSNat (TagPow n f) where
  toSNat PowZeroTag = Zero
  toSNat (PowSuccTag _ _ n) = n

-- | @Pow n f x = (f x, f x, ... (product of /n/ (f x)) ... , f x)@
data Pow n f x = Pow !(SNat n) (Finite n -> f x)

deriving instance Functor f => Functor (Pow n f)

-- | Destruct @Pow n f x@ one by one.
data PowView n f x where
  PowZero :: PowView 0 f x
  PowSucc :: Pow n f x -> f x -> PowView (n + 1) f x

viewPow :: Pow n f x -> PowView n f x
viewPow (Pow n e) = case n of
  Zero -> PowZero
  Succ n' -> PowSucc (Pow n' (e . weaken)) (e (withKnownNat n maxBound))

reviewPow :: PowView n f x -> Pow n f x
reviewPow PowZero = Pow Zero absurdFinite
reviewPow (PowSucc (Pow n e) fx) = Pow (Succ n) (either e (const fx) . withKnownNat n separateSum)

instance Polynomial f => Polynomial (Pow n f) where
  type Tag (Pow n f) = TagPow n (Tag f)

  toPoly :: forall x. Pow n f x -> Poly (TagPow n (Tag f)) x
  toPoly pf = case viewPow pf of
    PowZero -> P PowZeroTag absurdFinite
    PowSucc fs fx -> case (toPoly fs, toPoly fx) of
      (P tagFs repFs, P tagF repF) ->
        let ns = toSNat tagFs
            ns' = ns %+ toSNat tagF
         in P (PowSuccTag tagFs tagF ns') (either repFs repF . withKnownNat ns separateSum)

  fromPoly :: forall x. Poly (TagPow n (Tag f)) x -> Pow n f x
  fromPoly (P tag rep) = reviewPow $ case tag of
    PowZeroTag -> PowZero
    PowSuccTag tagFs tagF _ ->
      let ns = toSNat tagFs
          n = toSNat tagF
          pfs = P tagFs (rep . weakenS ns n)
          pf = P tagF (rep . shiftSRight ns n)
       in PowSucc (fromPoly pfs) (fromPoly pf)

data TagComp f g n where
  TagComp :: f a -> TagPow a g n -> TagComp f g n

instance (HasSNat g) => HasSNat (TagComp f g) where
  toSNat (TagComp _ pg) = toSNat pg

instance (Polynomial f, Polynomial g) => Polynomial (f :.: g) where
  type Tag (f :.: g) = TagComp (Tag f) (Tag g)

  toPoly :: forall x. (f :.: g) x -> Poly (TagComp (Tag f) (Tag g)) x
  toPoly (Comp1 fgy) = case toPoly fgy of
    P tagF repF ->
      case toPoly (Pow (toSNat tagF) repF) of
        P tagPowG repPow -> P (TagComp tagF tagPowG) repPow

  fromPoly :: forall x. Poly (TagComp (Tag f) (Tag g)) x -> (f :.: g) x
  fromPoly (P (TagComp tagF tagPowG) rep) =
    case fromPoly (P tagPowG rep) of
      Pow _ repF -> Comp1 $ fromPoly (P tagF repF)
