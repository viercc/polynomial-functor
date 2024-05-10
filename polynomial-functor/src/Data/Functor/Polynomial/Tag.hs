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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{- | This module provides a way to represent \"tag\" of various polynomial data types. For example,
a GADT 'TagMaybe' represents a functor of the same shape of 'Maybe'.

> data TagMaybe n where
>    TagNothing :: TagMaybe Void -- ^ Nothing takes 0 parameter
>    TagJust    :: TagMaybe ()   -- ^ Just takes 1 paramerer

-}
module Data.Functor.Polynomial.Tag(
  -- * The type class for tags
  HasFinitary(..),

  -- * Tags
  TagMaybe(..),
  TagList(..),

  TagFn, TagV(), TagK(..), TagSum, TagMul(..),
  TagPow(..), geqPow, gcomparePow,
  TagComp(..),
  TagDay(..),

  -- * Reexports

  GShow(..), GEq(..), GCompare(..), GOrdering(..)
) where

import Data.Kind (Type)

import Data.Type.Equality ((:~:)(..))
import GHC.Generics ( type (:+:)(..) )

import GHC.TypeNats hiding (pattern SNat)
import GHC.TypeNats.Extra (SNat(SNat))
import Data.Void
import Data.Finitary (Finitary(..))
import Data.Finite (Finite)
import Data.Functor.Classes (showsUnaryWith)

import Data.GADT.HasFinitary
import Data.GADT.Show
import Data.GADT.Compare
    ( defaultCompare, defaultEq, GCompare(..), GEq(..), GOrdering(..) )
import Data.GADT.Compare.Extra ( fromOrdering, (>>?) )


import Data.Functor.Pow

-- | Tag of 'Maybe'.
data TagMaybe n where
    TagNothing :: TagMaybe Void
    TagJust    :: TagMaybe ()

deriving instance Eq (TagMaybe n)
deriving instance Ord (TagMaybe n)
deriving instance Show (TagMaybe n)

instance HasFinitary TagMaybe where
    withFinitary TagNothing body = body
    withFinitary TagJust body = body

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

data TagList a where
  TagList :: KnownNat n => TagList (Finite n)

deriving instance Eq (TagList a)
deriving instance Ord (TagList a)

instance Show (TagList a) where
  showsPrec = gshowsPrec

instance HasFinitary TagList where
  withFinitary TagList body = body

instance GEq TagList where
  geq (TagList @n) (TagList @m) =
    let sn = SNat :: SNat n
        sm = SNat :: SNat m
    in case geq sn sm of
          Nothing -> Nothing
          Just Refl -> Just Refl

instance GCompare TagList where
  gcompare (TagList @n) (TagList @m) =
    let sn = SNat :: SNat n
        sm = SNat :: SNat m
    in case gcompare sn sm of
          GLT -> GLT
          GEQ -> GEQ
          GGT -> GGT

instance GShow TagList where
  gshowsPrec p (TagList @n) = showsUnaryWith (const (++)) "TagList" p ("@" ++ show (natVal @n SNat))

-- | @TagFn n@ represents @((), const n :: () -> Type)@.
--
--   This is the tag of @(->) r@ functor.
--
--   It's also the tag of 'Data.Proxy.Proxy' and 'Data.Functor.Identity',
--   by being isomorphic to @(->) Void@ and @(->) ()@ respectively.
--
--   > TagFn Void   -- Tag of Proxy
--   > TagFn ()     -- Tag of Identity
type TagFn = (:~:)

-- | @TagV n@ is an empty type for any @n@. It represents @(∅, α = absurd :: ∅ -> Nat)@. 
--
--   This is the tag of 'GHC.Generics.V1'.
type TagV :: Type -> Type
data TagV n
  deriving (Eq, Ord, Show)

absurdTagV :: TagV n -> any
absurdTagV v = case v of { }

instance HasFinitary TagV where
  withFinitary v _ = absurdTagV v

instance GEq TagV where
  geq = absurdTagV

instance GCompare TagV where
  gcompare = absurdTagV

instance GShow TagV where
  gshowsPrec = showsPrec

-- | @TagK c n@ represents @(c, α)@, where @α@ is a constant function to @Void@:
--   
--   > α = const Void :: c -> Type
--   
--   This is the tag of 'Data.Functor.Const'.
type TagK :: Type -> Type -> Type
data TagK c n where
  TagK :: c -> TagK c Void

deriving instance Eq c => Eq (TagK c n)
deriving instance Ord c => Ord (TagK c n)
deriving instance Show c => Show (TagK c n)

instance HasFinitary (TagK c) where
  withFinitary (TagK _) body = body

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
  TagMul :: !(f x) -> !(g y) -> TagMul f g (Either x y)

instance (HasFinitary t1, HasFinitary t2) => HasFinitary (TagMul t1 t2) where
  withFinitary (TagMul t1 t2) body =
    withFinitary t1 $ withFinitary t2 body

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

-- | When @t, u@ is the tag of @f, g@ respectively,
--   @TagComp t u@ is the tag of @f :.: g@.
data TagComp t u n where
  TagComp :: t a -> TagPow (Cardinality a) u n -> TagComp t u n

instance (HasFinitary u) => HasFinitary (TagComp t u) where
  withFinitary (TagComp _ pu) body = withFinitary pu body

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

type TagDay :: (Type -> Type) -> (Type -> Type) -> Type -> Type
data TagDay t u n where
  TagDay :: t n -> u m -> TagDay t u (n, m)

instance (HasFinitary t, HasFinitary u) => HasFinitary (TagDay t u) where
  withFinitary (TagDay t u) body = withFinitary t (withFinitary u body)

deriving instance (forall n. Show (t n), forall n. Show (u n)) => Show (TagDay t u m)

instance (forall n. Show (t n), forall n. Show (u n)) => GShow (TagDay t u) where
  gshowsPrec = showsPrec

instance (GEq t, GEq u) => GEq (TagDay t u) where
  TagDay t u `geq` TagDay t' u' =
    do Refl <- geq t t'
       Refl <- geq u u'
       pure Refl

instance (GEq t, GEq u) => Eq (TagDay t u n) where
  (==) = defaultEq

instance (GCompare t, GCompare u) => GCompare (TagDay t u) where
  gcompare (TagDay t u) (TagDay t' u') = gcompare t t' >>? gcompare u u' >>? GEQ

instance (GCompare t, GCompare u) => Ord (TagDay t u m) where
  compare = defaultCompare

