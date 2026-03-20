{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Polynomial(
  -- * Formal polynomials with natural-number (ℕ) coefficients
  P(..), P₀(..),
  Zero(..), Plus(..), One(..), Times(..),
  evalPoly, evalPoly₀,
  countSummands, polynomialOrder,

  -- * Type-level formal polynomials
  SZero(..), SPlus(..), SOne(..), STimes(..),
  SId(..), SCompose(..),

  SingP(..), SingP₀(..),
  
  EvalPoly, sEvalPoly,
  EvalPoly₀, sEvalPoly₀
) where

import Numeric.Natural (Natural)
import Data.Semigroup (Max(..))

import Data.Singletons
import Data.Kind (Type)

-- * Formal polynomials with natural-number (ℕ) coefficients

-- | A __nonzero__ formal polynomial with natural-number coefficient. If we write @{p}@ for the
--   meaning of @p :: P@ as a polynomial, the following holds:
--
-- @
-- {U}(x) = 1
-- {S p}(x) = 1 + {p}(x)
-- {T p}(x) = x * {p}(x)
-- @
-- 
-- In other words:
-- 
-- * @U :: P@ represents a constant polynomial @{U}(x) = 1@
-- * @S p :: P@ represents 1 plus the polynomial @{p}@.
-- * @T p :: P@ represents @{p}@ multiplied by the parameter of the polynomial.
-- 
-- Any __nonzero__ polynomial with coefficients in ℕ can be represented using 'P'.
-- In fact, they are /uniquely/ represented as a 'P' value.
-- For example, @1 + x^2 + x^3@ is uniquely represented as @S (T (T (S (T U))))@.
--
-- @
-- {S (T (T (S (T U))))}(x)
--   = 1 + {T (T (S (T U)))}(x)
--   = 1 + x * {T (S (T U))}(x)
--   = 1 + x * x * {S (T U)}(x)
--   = 1 + x * x * (1 + {T U}(x))
--   = 1 + x * x * (1 + x * {U}(x))
--   = 1 + x * x * (1 + x * 1)
--   = 1 + x^2 + x^3
-- @
data P = U | S P | T P
    deriving (Show, Eq, Ord)

-- | 'P₀' is either zero or a 'P'.
--
-- @
-- {Z}(x) = 0
-- {NZ p}(x) = {p}(x)
-- @
data P₀ = Z | NZ P
    deriving (Show, Eq, Ord)

-- * Semiring
--
-- The algebra of natural-number-coefficient polynomial can be seen as the free semiring on a singleton set.
-- In other words, it's an expression with one unknown parameter @x@, interpretable in any semiring.

class Zero a where
    zero :: a
    default zero :: Num a => a
    zero = 0

class Plus a where
    plus :: a -> a -> a
    default plus :: Num a => a -> a -> a
    plus = (+)

class One a where
    one :: a
    default one :: Num a => a
    one = 1

class Times a where
    times :: a -> a -> a
    default times :: Num a => a -> a -> a
    times = (*)

evalPoly :: (Plus a, One a, Times a) => P -> a -> a
evalPoly U = const one
evalPoly (S p) = \a -> one `plus` evalPoly p a
evalPoly (T p) = \a -> a `times` evalPoly p a

evalPoly₀ :: (Zero a, Plus a, One a, Times a) => P₀ -> a -> a
evalPoly₀ Z = const zero
evalPoly₀ (NZ p) = evalPoly p

countSummands :: P₀ -> Int
countSummands p = evalPoly₀ p 1

polynomialOrder :: P -> Int
polynomialOrder p = getMax $ evalPoly p (Max 1)

instance Zero Int
instance Plus Int
instance One Int
instance Times Int

instance Zero Natural
instance Plus Natural
instance One Natural
instance Times Natural

instance (Bounded a, Ord a) => Zero (Max a) where
    zero = Max minBound

-- | max-plus algebra (assuming addition in 'Num' preserves order)
instance (Ord a) => Plus (Max a) where
    plus = (<>)

-- | max-plus algebra (assuming addition in 'Num' preserves order)
instance (Ord a, Num a) => One (Max a) where
    one = 0

-- | max-plus algebra
instance (Ord a, Num a) => Times (Max a) where
    times (Max x) (Max y) = Max (x + y)

instance Plus P where
    plus U y = S y
    plus (S x) y = S (plus x y)
    plus (T x) U = S (T x)
    plus (T x) (S y) = S (plus (T x) y)
    plus (T x) (T y) = T (plus x y)

instance One P where
    one = U

instance Times P where
    times U y = y
    times (S x) U = S x
    times (S x) (S y) = S (plus (plus x y) (times x y))
    times (S x) (T y) = T (times (S x) y)
    times (T x) y = T (times x y)

instance Zero P₀ where
    zero = Z

instance Plus P₀ where
    plus Z y = y
    plus (NZ x) Z = NZ x
    plus (NZ x) (NZ y) = NZ (plus x y)

instance One P₀ where
    one = NZ one

instance Times P₀ where
    times Z _ = Z
    times (NZ _) Z = Z
    times (NZ x) (NZ y) = NZ (times x y)


-- * Singletons

data SingP a where
    SingU :: SingP 'U
    SingS :: SingP p -> SingP ('S p)
    SingT :: SingP p -> SingP ('T p)

type instance Sing = SingP
deriving instance Show (SingP p)

instance SingKind P where
    type Demote P = P

    fromSing SingU = U
    fromSing (SingS p) = S (fromSing p)
    fromSing (SingT p) = T (fromSing p)

    toSing U = SomeSing SingU
    toSing (S p) = withSomeSing p (SomeSing . SingS)
    toSing (T p) = withSomeSing p (SomeSing . SingT)

instance SingI 'U where sing = SingU
instance SingI p => SingI ('S p) where sing = SingS sing
instance SingI p => SingI ('T p) where sing = SingT sing

data SingP₀ a where
    SingZ :: SingP₀ 'Z
    SingNZ :: SingP p -> SingP₀ ('NZ p)

type instance Sing = SingP₀
deriving instance Show (SingP₀ p)

instance SingKind P₀ where
    type Demote P₀ = P₀

    fromSing SingZ = Z
    fromSing (SingNZ p) = NZ (fromSing p)

    toSing Z = SomeSing SingZ
    toSing (NZ p) = withSomeSing p (SomeSing . SingNZ)

instance SingI 'Z where sing = SingZ
instance SingI p => SingI ('NZ p) where sing = SingNZ sing

--------

-- * Promoted semiring classes

class SZero (k :: Type) where
    type TZero k :: k
    sZero :: Sing (TZero k)

infixl 6 +
infixl 6 %+
class SPlus (k :: Type) where
    type (+) (x :: k) (y :: k) :: k
    (%+) :: forall (x :: k) (y :: k). Sing x -> Sing y -> Sing (x + y)

class SOne (k :: Type) where
    type TOne k :: k
    sOne :: Sing (TOne k)

infixl 7 *
infixl 7 %*
class STimes (k :: Type) where
    type (*) (x :: k) (y :: k) :: k
    (%*) :: forall (x :: k) (y :: k). Sing x -> Sing y -> Sing (x * y)

class SId (k :: Type) where
    type TId k :: k
    sId :: Sing (TId k)

infixl 8 <<
infixl 8 %<<
class SCompose (k :: Type) where
    type (<<) (x :: k) (y :: k) :: k
    (%<<) :: forall (x :: k) (y :: k). Sing x -> Sing y -> Sing (x << y)



instance SZero P₀ where
    type TZero P₀ = 'Z
    sZero = SingZ

type family PlusPoly (x :: P) (y :: P) :: P where
    PlusPoly U y = S y
    PlusPoly (S x) y = S (PlusPoly x y)
    PlusPoly (T x) U = S (T x)
    PlusPoly (T x) (S y) = S (PlusPoly (T x) y)
    PlusPoly (T x) (T y) = T (PlusPoly x y)

instance SPlus P where
    type x + y = PlusPoly x y

    SingU %+ y = SingS y
    SingS x %+ y = SingS (x %+ y)
    SingT x %+ y = case y of
        SingU -> SingS (SingT x)
        SingS y' -> SingS (SingT x %+ y')
        SingT y' -> SingT (x %+ y')

type family PlusPoly₀ x y :: P₀ where
    PlusPoly₀ Z y = y
    PlusPoly₀ (NZ x) Z = NZ x
    PlusPoly₀ (NZ x) (NZ y) = NZ (PlusPoly x y)

instance SPlus P₀ where
    type x + y = PlusPoly₀ x y

    SingZ %+ y = y
    SingNZ x %+ SingZ = SingNZ x
    SingNZ x %+ SingNZ y = SingNZ (x %+ y)


instance SOne P where
    type TOne P = 'U
    sOne = SingU

instance SOne P₀ where
    type TOne P₀ = 'NZ 'U
    sOne = SingNZ sOne

type family TimesPoly x y :: P where
    TimesPoly U y = y
    TimesPoly (S x) U = S x
    TimesPoly (S x) (S y) = S ((x + y) + TimesPoly x y)
    TimesPoly (S x) (T y) = T (TimesPoly (S x) y)
    TimesPoly (T x) y = T (TimesPoly x y)

type family TimesPoly₀ x y :: P₀ where
    TimesPoly₀ Z _ = Z
    TimesPoly₀ (NZ _) Z = Z
    TimesPoly₀ (NZ x) (NZ y) = NZ (TimesPoly x y)

instance STimes P where
    type x * y = TimesPoly x y
    SingU %* y = y
    SingS x %* SingU = SingS x
    SingS x %* SingS y = SingS ((x %+ y) %+ (x %* y))
    SingS x %* SingT y = SingT (SingS x %* y)
    SingT x %* y = SingT (x %* y)

instance STimes P₀ where
    type x * y = TimesPoly₀ x y
    SingZ %* _ = SingZ
    SingNZ _ %* SingZ = SingZ
    SingNZ x %* SingNZ y = SingNZ (x %* y)

instance SId P where
    type TId P = 'S 'U
    sId = SingS SingU

instance SId P₀ where
    type TId P₀ = 'NZ ('S 'U)
    sId = SingNZ sId

type family ComposePoly (x :: P) (y :: P) where
    ComposePoly U _ = U
    ComposePoly (S x) y = S (ComposePoly x y)
    ComposePoly (T x) y = TimesPoly y (ComposePoly x y)

type family ConstantPart' (x :: P) where
    ConstantPart' U = S U
    ConstantPart' (S x) = S (ConstantPart' x)
    ConstantPart' (T _) = U

type family ComposePoly₀ (x :: P₀) (y :: P₀) where
    ComposePoly₀ Z _ = Z
    ComposePoly₀ (NZ U) Z = NZ U
    ComposePoly₀ (NZ (S x)) Z = NZ (ConstantPart' x)
    ComposePoly₀ (NZ (T _)) Z = Z
    ComposePoly₀ (NZ x) (NZ y) = NZ (ComposePoly x y)

instance SCompose P where
    type x << y = ComposePoly x y
    SingU %<< _ = SingU
    SingS x %<< y = SingS (x %<< y)
    SingT x %<< y = y %* (x %<< y)

instance SCompose P₀ where
    type x << y = ComposePoly₀ x y

    SingZ %<< _ = SingZ
    SingNZ SingU %<< SingZ = SingNZ SingU
    SingNZ (SingS x) %<< SingZ = SingNZ (sConstantPart x)
    SingNZ (SingT _) %<< SingZ = SingZ
    SingNZ x %<< SingNZ y = SingNZ (x %<< y)

sConstantPart :: SingP x -> SingP (ConstantPart' x)
sConstantPart SingU = SingS SingU
sConstantPart (SingS x) = SingS (sConstantPart x)
sConstantPart (SingT _) = SingU

type family EvalPoly (x :: P) k (arg :: k) :: k where
    EvalPoly U k _ = TOne k
    EvalPoly (S p) k arg = TOne k + EvalPoly p k arg
    EvalPoly (T p) k arg = arg * EvalPoly p k arg

sEvalPoly :: (SOne k, SPlus k, STimes k) => SingP x -> Sing arg -> Sing (EvalPoly x k arg)
sEvalPoly SingU _ = sOne
sEvalPoly (SingS p) arg = sOne %+ sEvalPoly p arg
sEvalPoly (SingT p) arg = arg %* sEvalPoly p arg

type family EvalPoly₀ (x :: P₀) k (arg :: k) :: k where
    EvalPoly₀ Z k _ = TZero k
    EvalPoly₀ (NZ p) k arg = EvalPoly p k arg

sEvalPoly₀ :: (SZero k, SOne k, SPlus k, STimes k) => SingP₀ x -> Sing arg -> Sing (EvalPoly₀ x k arg)
sEvalPoly₀ SingZ _ = sZero
sEvalPoly₀ (SingNZ p) arg = sEvalPoly p arg