{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE BangPatterns #-}
module Data.Functor.Pow (
  -- * Powers of a functor 
  Pow(..), Pow'(..),
  functionToPow, powToFunction,
  
  -- * Tag of powers of a polynomial functor
  TagPow(..), TagPow'(..),
  geqPow, geqPow', gcomparePow, gcomparePow'
) where

import GHC.TypeNats
import GHC.TypeNats.Extra ( SNat(Succ, Zero) )
import Data.Finite
import Data.Void
import Data.Type.Equality ( type (:~:)(..) )

import Data.GADT.HasFinitary
import Data.GADT.Show ( GShow(..) )
import Data.GADT.Compare
import Data.GADT.Compare.Extra ((>>?))
import Data.Some (Some(..))
import Unsafe.Coerce (unsafeCoerce)
import Data.Finite.Extra (combineSumS, separateSumS, absurdFinite)


-- | @Pow n f = f :*: f :*: ...(n)... :*: f@
data Pow n f x where
  Pow0 :: Pow 0 f x
  PowNZ :: Pow' n f x -> Pow n f x

deriving instance Functor f => Functor (Pow n f)
data Pow' n f x where
  Pow1 :: f x -> Pow' 1 f x
  PowEven :: (KnownNat n, n ~ m * 2) => Pow' m f x -> Pow' m f x -> Pow' n f x
  PowOdd  :: (KnownNat n, n ~ m * 2 + 1) => f x -> Pow' m f x -> Pow' m f x -> Pow' n f x

deriving instance Functor f => Functor (Pow' n f)

withKnownNatPow' :: Pow' n f x -> (KnownNat n => r) -> r
withKnownNatPow' fs body = case fs of
  Pow1{} -> body
  PowEven{} -> body
  PowOdd{} -> body

powEven :: Pow n f x -> Pow n f x -> Pow (n * 2) f x
powEven Pow0 Pow0 = Pow0
powEven (PowNZ l) (PowNZ r) = withKnownNatPow' l $ PowNZ (PowEven l r)
powEven !_ !_ = error "unreachable"

powOdd :: f x -> Pow n f x -> Pow n f x -> Pow (n * 2 + 1) f x
powOdd f0 (PowNZ l) (PowNZ r) = withKnownNatPow' l $ PowNZ (PowOdd f0 l r)
powOdd _ !_ !_ = error "unreachable"

functionToPow :: SNat n -> (Finite n -> f x) -> Pow n f x
functionToPow sn f = case binView sn of
  View0 -> Pow0
  ViewNZ View1 -> PowNZ (Pow1 (f minBound))
  ViewNZ (ViewEven sn') ->
    let f1 = f . combineSumS sn' sn' . Left
        f2 = f . combineSumS sn' sn' . Right
    in powEven (functionToPow sn' f1) (functionToPow sn' f2)
  ViewNZ (ViewOdd sn') ->
    let f0 = withKnownNat sn (f minBound)
        f1 = f . shift . combineSumS sn' sn' . Left
        f2 = f . shift . combineSumS sn' sn' . Right
    in powOdd f0 (functionToPow sn' f1) (functionToPow sn' f2)

powToFunction :: Pow n f x -> Finite n -> f x
powToFunction Pow0 = absurdFinite
powToFunction (PowNZ fs) = powToFunction' fs

powToFunction' :: Pow' n f x -> Finite n -> f x
powToFunction' (Pow1 fx) _ = fx
powToFunction' (PowEven fs1 fs2) k =
  case separateSumS sn' sn' k of
      Left k1 -> powToFunction' fs1 k1
      Right k2 -> powToFunction' fs2 k2
  where
    sn' = withKnownNatPow' fs1 SNat
powToFunction' (PowOdd f0 fs1 fs2) k =
  case unshift k of
    Nothing -> f0
    Just k' -> case separateSumS sn' sn' k' of
      Left k1 -> powToFunction' fs1 k1
      Right k2 -> powToFunction' fs2 k2
  where
    sn' = withKnownNatPow' fs1 SNat

-- * Tag for Pow of polynomial functors

-- | When @t@ represents @(U,α :: U -> Type)@,
--   @TagPow n t xs@ represents @α^n@ below:
--
--   > α^n :: U^n -> Type
--   > α^n(u1, u2, ..., u_n) = α u1 + α u2 + ... + α u_n
--
--   This is the tag of @'Pow' n f@ when @t@ is the tag of @f@.
data TagPow n t xs where
  TagPow0 :: TagPow 0 t Void
  TagPowNZ :: TagPow' n t xs -> TagPow n t xs

deriving instance (forall n. Show (t n)) => Show (TagPow m t xs)

instance (forall n. Show (t n)) => GShow (TagPow m t) where
  gshowsPrec = showsPrec

instance (HasFinitary t) => HasFinitary (TagPow n t) where
  withFinitary TagPow0 body = body
  withFinitary (TagPowNZ ts) body = withFinitary ts body

instance GEq t => GEq (TagPow n t) where
  geq t t' = fmap snd (geqPow t t')

instance GEq t => Eq (TagPow n t xs) where
  (==) = defaultEq

instance GCompare t => GCompare (TagPow n t) where
  gcompare t t' = gcomparePow t t' >>? GEQ

instance GCompare t => Ord (TagPow n t xs) where
  compare = defaultCompare

data TagPow' n t xs where
  TagPow1 :: t x -> TagPow' 1 t x
  TagPowEven :: (KnownNat n, n ~ m * 2) => TagPow' m t xs1 -> TagPow' m t xs2 -> TagPow' n t (Either xs1 xs2)
  TagPowOdd :: (KnownNat n, n ~ m * 2 + 1) => t x -> TagPow' m t xs1 -> TagPow' m t xs2 -> TagPow' n t (Either x (Either xs1 xs2))

instance HasFinitary t => HasFinitary (TagPow' n t) where
  withFinitary ts body = case ts of
    TagPow1 t -> withFinitary t body
    TagPowEven ts1 ts2 -> withFinitary ts1 $ withFinitary ts2 body
    TagPowOdd t0 ts1 ts2 -> withFinitary t0 $ withFinitary ts1 $ withFinitary ts2 body

deriving instance (forall m. Show (t m)) => Show (TagPow' n t xs)

instance (forall m. Show (t m)) => GShow (TagPow' n t) where
  gshowsPrec = showsPrec

instance GEq t => GEq (TagPow' n t) where
  geq t t' = fmap snd (geqPow' t t')

instance GEq t => Eq (TagPow' n t xs) where
  (==) = defaultEq

instance GCompare t => GCompare (TagPow' n t) where
  gcompare t t' = gcomparePow' t t' >>? GEQ

instance GCompare t => Ord (TagPow' n t xs) where
  compare = defaultCompare

-- *

geqPow :: GEq t => TagPow n t xs -> TagPow n' t xs' -> Maybe (n :~: n', xs :~: xs')
geqPow TagPow0 TagPow0 = Just (Refl, Refl)
geqPow (TagPowNZ ts1) (TagPowNZ ts2) = geqPow' ts1 ts2 >>= \(Refl, Refl) -> Just (Refl, Refl)
geqPow _ _ = Nothing

geqPow' :: GEq t => TagPow' n t xs -> TagPow' n' t xs' -> Maybe (n :~: n', xs :~: xs')
geqPow' (TagPow1 t) (TagPow1 t') = geq t t' >>= \eq -> Just (Refl, eq)
geqPow' (TagPowEven t1 t2) (TagPowEven t1' t2') = do
  (Refl, Refl) <- geqPow' t1 t1'
  (Refl, Refl) <- geqPow' t2 t2'
  Just (Refl, Refl)
geqPow' (TagPowOdd t0 t1 t2) (TagPowOdd t0' t1' t2') = do
  Refl <- geq t0 t0'
  (Refl, Refl) <- geqPow' t1 t1'
  (Refl, Refl) <- geqPow' t2 t2'
  Just (Refl, Refl)
geqPow' _ _ = Nothing

gcomparePow :: GCompare t => TagPow n t xs -> TagPow n' t xs' -> GOrdering '(n,xs) '(n',xs')
gcomparePow TagPow0 TagPow0 = GEQ
gcomparePow TagPow0 TagPowNZ{} = GLT
gcomparePow TagPowNZ{} TagPow0 = GGT
gcomparePow (TagPowNZ ts) (TagPowNZ ts') = gcomparePow' ts ts' >>? GEQ

gcomparePow' :: GCompare t => TagPow' n t xs -> TagPow' n' t xs' -> GOrdering '(n,xs) '(n',xs')
gcomparePow' ts1 ts2 = gcompare sn1 sn2 >>? gcomparePowN' ts1 ts2 >>? GEQ
  where
    sn1 = toSNatTagPow' ts1
    sn2 = toSNatTagPow' ts2

gcomparePowN' :: GCompare t => TagPow' n t xs -> TagPow' n t xs' -> GOrdering xs xs'
gcomparePowN' (TagPow1 t) (TagPow1 t') = gcompare t t'
gcomparePowN' (TagPowEven t1 t2) (TagPowEven t1' t2') = gcomparePowN' t1 t1' >>? gcomparePowN' t2 t2' >>? GEQ
gcomparePowN' (TagPowOdd t t1 t2) (TagPowOdd t' t1' t2') = gcompare t t' >>? gcomparePowN' t1 t1' >>? gcomparePowN' t2 t2' >>? GEQ
gcomparePowN' _ _ = error "unreachable!"

toSNatTagPow' :: TagPow' n t xs -> SNat n
toSNatTagPow' TagPow1{} = SNat
toSNatTagPow' TagPowEven{} = SNat
toSNatTagPow' TagPowOdd{} = SNat

-- *

-- | Binary representation of Nat
data BinView (n :: Nat) where
  View0 :: BinView 0
  ViewNZ :: BinView' n -> BinView n

data BinView' (n :: Nat) where
  View1 :: BinView' 1
  ViewEven :: SNat n -> BinView' (n * 2)
  ViewOdd :: SNat n -> BinView' (n * 2 + 1)

binView :: SNat n -> BinView n
binView Zero = View0
binView sn@(Succ _) = ViewNZ (binView' sn)

binView' :: SNat (n + 1) -> BinView' (n + 1)
binView' sn = unsafeCoerceFromSome res
  where
    n = fromSNat sn
    res = case n of
      0 -> error "unreachable!"
      1 -> Some View1
      _ | even n    -> withSomeSNat (n `div` 2) $ \sn' -> Some (ViewEven sn')
        | otherwise -> withSomeSNat (n `div` 2) $ \sn' -> Some (ViewOdd sn')

unsafeCoerceFromSome :: Some f -> f any
unsafeCoerceFromSome (Some fb) = unsafeCoerce fb