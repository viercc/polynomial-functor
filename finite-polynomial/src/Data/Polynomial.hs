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
  Poly(..), Poly₀(..),
  Zero(..), Plus(..), One(..), Times(..),
  evalPoly, evalPoly₀,
  countSummands, polynomialOrder,

  -- * Type-level formal polynomials
  SZero(..), SPlus(..), SOne(..), STimes(..),
  SId(..), SCompose(..),

  SPoly(..), SPoly₀(..),
  
  EvalPoly, sEvalPoly,
  EvalPoly₀, sEvalPoly₀
) where

import Numeric.Natural (Natural)
import Data.Semigroup (Max(..))

import Data.Singletons
import Data.Kind (Type)

-- * Formal polynomials with natural-number (ℕ) coefficients

-- | A __nonzero__ formal polynomial with natural-number coefficient. If we write @{p}@ for the
--   meaning of @p :: Poly@ as a polynomial, the following holds:
--
-- @
-- {U}(x) = 1
-- {S p}(x) = 1 + {p}(x)
-- {T p}(x) = x * {p}(x)
-- @
-- 
-- In other words:
-- 
-- * @U :: Poly@ represents a constant polynomial @{U}(x) = 1@
-- * @S p :: Poly@ represents an addition of constant @1@ to the polynomial @{p}@.
-- * @T p :: Poly@ represents @{p}@ multiplied by the parameter of the polynomial.
-- 
-- Any __nonzero__ polynomial with coefficients in ℕ can be represented using 'Poly'.
-- In fact, they are /uniquely/ represented as a 'Poly' value.
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
data Poly = U | S Poly | T Poly
    deriving (Show, Eq, Ord)

-- | 'Poly₀' is 'Poly' but can be zero.
--
-- @
-- {Z}(x) = 0
-- {NZ p}(x) = {p}(x)
-- @
data Poly₀ = Z | NZ Poly
    deriving (Show, Eq, Ord)

-- * Semiring
--
-- The algebra of natural-number-coefficient polynomial can be seen as a free semiring with single generator.
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

evalPoly :: (Plus a, One a, Times a) => Poly -> a -> a
evalPoly U = const one
evalPoly (S p) = \a -> one `plus` evalPoly p a
evalPoly (T p) = \a -> a `times` evalPoly p a

evalPoly₀ :: (Zero a, Plus a, One a, Times a) => Poly₀ -> a -> a
evalPoly₀ Z = const zero
evalPoly₀ (NZ p) = evalPoly p

countSummands :: Poly₀ -> Int
countSummands p = evalPoly₀ p 1

polynomialOrder :: Poly -> Int
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

instance Plus Poly where
    plus U y = S y
    plus (S x) y = S (plus x y)
    plus (T x) U = S (T x)
    plus (T x) (S y) = S (plus (T x) y)
    plus (T x) (T y) = T (plus x y)

instance One Poly where
    one = U

instance Times Poly where
    times U y = y
    times (S x) U = S x
    times (S x) (S y) = S (plus (plus x y) (times x y))
    times (S x) (T y) = T (times (S x) y)
    times (T x) y = T (times x y)

instance Zero Poly₀ where
    zero = Z

instance Plus Poly₀ where
    plus Z y = y
    plus (NZ x) Z = NZ x
    plus (NZ x) (NZ y) = NZ (plus x y)

instance One Poly₀ where
    one = NZ one

instance Times Poly₀ where
    times Z _ = Z
    times (NZ _) Z = Z
    times (NZ x) (NZ y) = NZ (times x y)


-- * Singletons

data SPoly a where
    SingU :: SPoly 'U
    SingS :: SPoly p -> SPoly ('S p)
    SingT :: SPoly p -> SPoly ('T p)

type instance Sing = SPoly
deriving instance Show (SPoly p)

instance SingKind Poly where
    type Demote Poly = Poly

    fromSing SingU = U
    fromSing (SingS p) = S (fromSing p)
    fromSing (SingT p) = T (fromSing p)

    toSing U = SomeSing SingU
    toSing (S p) = withSomeSing p (SomeSing . SingS)
    toSing (T p) = withSomeSing p (SomeSing . SingT)

instance SingI 'U where sing = SingU
instance SingI p => SingI ('S p) where sing = SingS sing
instance SingI p => SingI ('T p) where sing = SingT sing

data SPoly₀ a where
    SingZ :: SPoly₀ 'Z
    SingNZ :: SPoly p -> SPoly₀ ('NZ p)

type instance Sing = SPoly₀
deriving instance Show (SPoly₀ p)

instance SingKind Poly₀ where
    type Demote Poly₀ = Poly₀

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



instance SZero Poly₀ where
    type TZero Poly₀ = 'Z
    sZero = SingZ

type family PlusPoly (x :: Poly) (y :: Poly) :: Poly where
    PlusPoly U y = S y
    PlusPoly (S x) y = S (PlusPoly x y)
    PlusPoly (T x) U = S (T x)
    PlusPoly (T x) (S y) = S (PlusPoly (T x) y)
    PlusPoly (T x) (T y) = T (PlusPoly x y)

instance SPlus Poly where
    type x + y = PlusPoly x y

    SingU %+ y = SingS y
    SingS x %+ y = SingS (x %+ y)
    SingT x %+ y = case y of
        SingU -> SingS (SingT x)
        SingS y' -> SingS (SingT x %+ y')
        SingT y' -> SingT (x %+ y')

type family PlusPoly₀ x y :: Poly₀ where
    PlusPoly₀ Z y = y
    PlusPoly₀ (NZ x) Z = NZ x
    PlusPoly₀ (NZ x) (NZ y) = NZ (PlusPoly x y)

instance SPlus Poly₀ where
    type x + y = PlusPoly₀ x y

    SingZ %+ y = y
    SingNZ x %+ SingZ = SingNZ x
    SingNZ x %+ SingNZ y = SingNZ (x %+ y)


instance SOne Poly where
    type TOne Poly = 'U
    sOne = SingU

instance SOne Poly₀ where
    type TOne Poly₀ = 'NZ 'U
    sOne = SingNZ sOne

type family TimesPoly x y :: Poly where
    TimesPoly U y = y
    TimesPoly (S x) U = S x
    TimesPoly (S x) (S y) = S ((x + y) + TimesPoly x y)
    TimesPoly (S x) (T y) = T (TimesPoly (S x) y)
    TimesPoly (T x) y = T (TimesPoly x y)

type family TimesPoly₀ x y :: Poly₀ where
    TimesPoly₀ Z _ = Z
    TimesPoly₀ (NZ _) Z = Z
    TimesPoly₀ (NZ x) (NZ y) = NZ (TimesPoly x y)

instance STimes Poly where
    type x * y = TimesPoly x y
    SingU %* y = y
    SingS x %* SingU = SingS x
    SingS x %* SingS y = SingS ((x %+ y) %+ (x %* y))
    SingS x %* SingT y = SingT (SingS x %* y)
    SingT x %* y = SingT (x %* y)

instance STimes Poly₀ where
    type x * y = TimesPoly₀ x y
    SingZ %* _ = SingZ
    SingNZ _ %* SingZ = SingZ
    SingNZ x %* SingNZ y = SingNZ (x %* y)

instance SId Poly where
    type TId Poly = 'S 'U
    sId = SingS SingU

instance SId Poly₀ where
    type TId Poly₀ = 'NZ ('S 'U)
    sId = SingNZ sId

type family ComposePoly (x :: Poly) (y :: Poly) where
    ComposePoly U _ = U
    ComposePoly (S x) y = S (ComposePoly x y)
    ComposePoly (T x) y = TimesPoly y (ComposePoly x y)

type family ConstantPart' (x :: Poly) where
    ConstantPart' U = S U
    ConstantPart' (S x) = S (ConstantPart' x)
    ConstantPart' (T _) = U

type family ComposePoly₀ (x :: Poly₀) (y :: Poly₀) where
    ComposePoly₀ Z _ = Z
    ComposePoly₀ (NZ U) Z = NZ U
    ComposePoly₀ (NZ (S x)) Z = NZ (ConstantPart' x)
    ComposePoly₀ (NZ (T _)) Z = Z
    ComposePoly₀ (NZ x) (NZ y) = NZ (ComposePoly x y)

instance SCompose Poly where
    type x << y = ComposePoly x y
    SingU %<< _ = SingU
    SingS x %<< y = SingS (x %<< y)
    SingT x %<< y = y %* (x %<< y)

instance SCompose Poly₀ where
    type x << y = ComposePoly₀ x y

    SingZ %<< _ = SingZ
    SingNZ SingU %<< SingZ = SingNZ SingU
    SingNZ (SingS x) %<< SingZ = SingNZ (sConstantPart x)
    SingNZ (SingT _) %<< SingZ = SingZ
    SingNZ x %<< SingNZ y = SingNZ (x %<< y)

sConstantPart :: SPoly x -> SPoly (ConstantPart' x)
sConstantPart SingU = SingS SingU
sConstantPart (SingS x) = SingS (sConstantPart x)
sConstantPart (SingT _) = SingU

type family EvalPoly (x :: Poly) k (arg :: k) :: k where
    EvalPoly U k _ = TOne k
    EvalPoly (S p) k arg = TOne k + EvalPoly p k arg
    EvalPoly (T p) k arg = arg * EvalPoly p k arg

sEvalPoly :: (SOne k, SPlus k, STimes k) => SPoly x -> Sing arg -> Sing (EvalPoly x k arg)
sEvalPoly SingU _ = sOne
sEvalPoly (SingS p) arg = sOne %+ sEvalPoly p arg
sEvalPoly (SingT p) arg = arg %* sEvalPoly p arg

type family EvalPoly₀ (x :: Poly₀) k (arg :: k) :: k where
    EvalPoly₀ Z k _ = TZero k
    EvalPoly₀ (NZ p) k arg = EvalPoly p k arg

sEvalPoly₀ :: (SZero k, SOne k, SPlus k, STimes k) => SPoly₀ x -> Sing arg -> Sing (EvalPoly₀ x k arg)
sEvalPoly₀ SingZ _ = sZero
sEvalPoly₀ (SingNZ p) arg = sEvalPoly p arg