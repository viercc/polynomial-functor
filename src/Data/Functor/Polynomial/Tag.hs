{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}

{- | This module provides a way to represent \"tag\" of various polynomial data types. For example,
a GADT 'TagMaybe' represents a functor of the same shape of 'Maybe'.

> data TagMaybe n where
>    TagNothing :: TagMaybe 0 -- ^ Nothing takes 0 parameter
>    TagJust    :: TagMaybe 1 -- ^ Just takes 1 paramerer

The class 'HasSNat' abstracts such GADTs in a uniform way.

Any instance @t@ of @HasSNat@ is a GADTs representing a type of \"tags\" of a polynomial functor.
But note that a \"tag\" is not the same thing to the constructors of a @data@ type. For example,
the following one-constructor type @F@ has four tags.

> data F x = F Bool (Maybe x) x

The four tags corresponds to the ways of distinguish @F x@ without comparing @x@ parts.
In fact, each tag corresponds to a unique value of @F ()@.

> [ F False Nothing (), F True Nothing (), F False (Just ()) (), F True (Just ()) () ]

-}
module Data.Functor.Polynomial.Tag(
  -- * The type class for tags
  HasSNat(..),
  
  -- * Tags
  TagMaybe(..),
  TagFn, TagV(), TagK(..), TagSum, TagMul(..),
  TagPow(..), geqPow, gcomparePow,
  TagComp(..),

  -- * Reexports
  GShow(..), GEq(..), GCompare(..), GOrdering(..)
) where

import Data.Kind (Type)

import Data.Type.Equality ((:~:)(..))
import GHC.Generics ( type (:+:)(..) )

import GHC.TypeNats
import GHC.TypeLits.Witnesses ( SNat(..), withKnownNat, (%+) )
import Data.Finite.Extra (SNat (Zero) )

import Data.GADT.Show
import Data.GADT.Compare
    ( defaultCompare, defaultEq, GCompare(..), GEq(..), GOrdering(..) )
import Data.GADT.Compare.Extra ( fromOrdering, (>>?) )

-- | An instance @'HasSNat' t@ indicates @t n@ contains sufficient data
--   to construct the @'SNat' n@ value.
--
--   For example, the following GADT defines a type with @HasSNat@ instance.
--   
--   > data T n where
--   >     A :: T 0
--   >     B :: T 2
--   >     C :: Bool -> T 2
--   >
--   > instance HasSNat T where
--   >    toSNat A = SNat :: SNat 0
--   >    toSNat B = SNat :: SNat 1
--   >    toSNat (C _) = SNat :: SNat 2
--   
--   Such @t@ can be seen as a representation of a type @U@ equipped with a function @α :: U -> Nat@,
--   where each of @t n@ is a inverse images of a function @α :: U -> Nat@. In the above example, @T@ represents @(U,α) below.@ 
--   
--   > data U = A' | B' | C' False | C' True
--   > α A' = 0
--   > α B' = 1
--   > α (C' False) = α (C' True) = 2
class HasSNat t where
  toSNat :: t n -> SNat n

-- | Represents @(Nat, id :: Nat -> Nat)
instance HasSNat SNat where
  toSNat = id

-- | Tag of 'Maybe'.
data TagMaybe n where
    TagNothing :: TagMaybe 0
    TagJust    :: TagMaybe 1

deriving instance Eq (TagMaybe n)
deriving instance Ord (TagMaybe n)
deriving instance Show (TagMaybe n)

instance HasSNat TagMaybe where
    toSNat TagNothing = SNat
    toSNat TagJust = SNat

instance GEq TagMaybe where
    geq TagNothing TagNothing = Just Refl
    geq TagJust TagJust = Just Refl
    geq _ _ = Nothing

instance GCompare TagMaybe where
    gcompare TagNothing TagNothing = GEQ
    gcompare TagNothing TagJust = GLT
    gcompare TagJust TagNothing = GGT
    gcompare TagJust TagJust = GEQ

instance GShow TagMaybe where
    gshowsPrec = showsPrec

-- | @TagFn n@ represents @((), const n :: () -> Nat)@.
--
--   This is the tag of @(->) r@ functor, where @r@ is 'Data.Finitary.Finitary' type of cardinality @n@.
--
--   > TagFn (Cardinality r)   -- Tag of ((->) r)
--
--   It's also the tag of 'Data.Proxy.Proxy' and 'Data.Functor.Identity',
--   by being isomorphic to @(->) Void@ and @(->) ()@ respectively.
--
--   > TagFn 0   -- Tag of Proxy
--   > TagFn 1   -- Tag of Identity
type TagFn = (:~:)

instance KnownNat n => HasSNat (TagFn n) where
  toSNat Refl = SNat

-- | @TagV n@ is an empty type for any @n@. It represents @(∅, α = absurd :: ∅ -> Nat)@. 
--
--   This is the tag of 'GHC.Generics.V1'.
type TagV :: Nat -> Type
data TagV n
  deriving (Eq, Ord, Show)

absurdTagV :: TagV n -> any
absurdTagV v = case v of { }

instance HasSNat TagV where
  toSNat = absurdTagV

instance GEq TagV where
  geq = absurdTagV

instance GCompare TagV where
  gcompare = absurdTagV

instance GShow TagV where
  gshowsPrec = showsPrec

-- | @TagK c n@ represents @(c, α)@, where @α@ is a constant function to zero:
--   
--   > α = const 0 :: c -> Nat
--   
--   This is the tag of 'Data.Functor.Const'.
type TagK :: Type -> Nat -> Type
data TagK c n where
  TagK :: c -> TagK c 0

deriving instance Eq c => Eq (TagK c n)
deriving instance Ord c => Ord (TagK c n)
deriving instance Show c => Show (TagK c n)

instance HasSNat (TagK c) where
  toSNat (TagK _) = SNat

instance Eq c => GEq (TagK c) where
  geq (TagK c) (TagK c')
      | c == c' = Just Refl
      | otherwise = Nothing

instance Ord c => GCompare (TagK c) where
  gcompare (TagK c) (TagK c') = fromOrdering (compare c c')

instance Show c => GShow (TagK c) where
  gshowsPrec = showsPrec

-- | When @t1, t2@ represents @(U, α1)@ and @(V,α2)@ respectively,
--   
--   > α1 :: U -> Nat
--   > α2 :: V -> Nat
--   
--   @TagSum t1 t2@ represents @(Either U V, β = either α1 α2)@.
--
--   > β :: Either U V -> Nat
--   > β (Left u)  = α1(u)
--   > β (Right v) = α2(v)
--
--   This is the tag of @f :+: g@, when @t1, t2@ is the tag of @f, g@ respectively.
type TagSum = (:+:)

instance (HasSNat t1, HasSNat t2) => HasSNat (TagSum t1 t2) where
  toSNat (L1 t1) = toSNat t1
  toSNat (R1 t2) = toSNat t2

-- |  When @t1, t2@ represents @(U, α1)@ and @(V,α2)@ respectively,
--   
--   > α1 :: U -> Nat
--   > α2 :: V -> Nat
--   
--   @TagMul t1 t2@ represents the direct product @(U,V)@ and the function @β@ on it:
--   
--   > β :: (U,V) -> Nat
--   > β(u,v) = α1 u + α2 v
--   
--   This is the tag of @f :*: g@ when @t1, t2@ is the tag of @f, g@ respectively.
data TagMul f g x where
  TagMul :: !(f x) -> !(g y) -> TagMul f g (x + y)

instance (HasSNat t1, HasSNat t2) => HasSNat (TagMul t1 t2) where
  toSNat (TagMul t1 t2) = toSNat t1 %+ toSNat t2

deriving instance (forall n. Show (t1 n), forall n. Show (t2 n)) => Show (TagMul t1 t2 m)
instance (forall n. Show (t1 n), forall n. Show (t2 n)) => GShow (TagMul t1 t2) where
  gshowsPrec = showsPrec

instance (GEq t1, GEq t2) => Eq (TagMul t1 t2 n) where
  (==) = defaultEq

instance (GEq t1, GEq t2) => GEq (TagMul t1 t2) where
  geq (TagMul t1 t2) (TagMul t1' t2') =
    do Refl <- geq t1 t1'
       Refl <- geq t2 t2'
       pure Refl

instance (GCompare t1, GCompare t2) => Ord (TagMul t1 t2 n) where
  compare = defaultCompare

instance (GCompare t1, GCompare t2) => GCompare (TagMul t1 t2) where
  gcompare (TagMul t1 t2) (TagMul t1' t2') = gcompare t1 t1' >>? gcompare t2 t2' >>? GEQ

-- | When @t@ represents @(U,α :: U -> Nat)@,
--   @TagPow n t xs@ represents @α^n@ below:
--
--   > α^n :: U^n -> Nat
--   > α^n(u1, u2, ..., u_n) = α u1 + α u2 + ... + α u_n
--
--   This is the tag of @'Data.Functor.Polynomial.Pow' n f@ when @t@ is the tag of @f@.
data TagPow n t xs where
  ZeroTag :: TagPow 0 t 0
  (:+|)   :: TagPow n t xs -> t x -> TagPow (n + 1) t (xs + x)

infixl 6 :+|

deriving instance (forall n. Show (t n)) => Show (TagPow m t xs)
instance (forall n. Show (t n)) => GShow (TagPow m t) where
  gshowsPrec = showsPrec

instance (HasSNat t) => HasSNat (TagPow n t) where
  toSNat ZeroTag = Zero
  toSNat (l :+| r) = toSNat l %+ toSNat r

instance GEq t => GEq (TagPow n t) where
  geq t t' = fmap snd (geqPow t t')

instance GEq t => Eq (TagPow n t xs) where
  (==) = defaultEq

geqPow :: GEq t => TagPow n t xs -> TagPow n' t xs' -> Maybe (n :~: n', xs :~: xs')
geqPow ZeroTag ZeroTag = Just (Refl, Refl)
geqPow (ts :+| t) (ts' :+| t') =
  do Refl <- geq t t'
     (Refl, Refl) <- geqPow ts ts'
     pure (Refl, Refl)
geqPow _ _ = Nothing

instance GCompare t => GCompare (TagPow n t) where
  gcompare t t' = gcomparePow t t' >>? GEQ

instance GCompare t => Ord (TagPow n t xs) where
  compare = defaultCompare

gcomparePow :: GCompare t => TagPow n t xs -> TagPow n' t xs' -> GOrdering '(n,xs) '(n',xs')
gcomparePow ZeroTag ZeroTag = GEQ
gcomparePow ZeroTag (_ :+| _) = GLT
gcomparePow (_ :+| _) ZeroTag = GGT
gcomparePow (ts :+| t) (ts' :+| t') = gcomparePow ts ts' >>? gcompare t t' >>? GEQ

-- | When @t, u@ is the tag of @f, g@ respectively,
--   @TagComp t u@ is the tag of @f :.: g@.
data TagComp t u n where
  TagComp :: t a -> TagPow a u n -> TagComp t u n

instance (HasSNat t, HasSNat u) => HasSNat (TagComp t u) where
  toSNat (TagComp t pu) = withKnownNat (toSNat t) (toSNat pu)

deriving instance (forall n. Show (t n), forall n. Show (u n)) => Show (TagComp t u m)
instance (forall n. Show (t n), forall n. Show (u n)) => GShow (TagComp t u) where
  gshowsPrec = showsPrec

instance (GEq t, GEq u) => GEq (TagComp t u) where
  geq (TagComp t pu) (TagComp t' pu') =
    do Refl <- geq t t'
       Refl <- geq pu pu'
       pure Refl

instance (GEq t, GEq u) => Eq (TagComp t u n) where
  (==) = defaultEq

instance (GCompare t, GCompare u) => GCompare (TagComp t u) where
  gcompare (TagComp t pu) (TagComp t' pu') = gcompare t t' >>? gcompare pu pu' >>? GEQ

instance (GCompare t, GCompare u) => Ord (TagComp t u n) where
  compare = defaultCompare
