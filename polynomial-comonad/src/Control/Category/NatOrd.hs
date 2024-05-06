{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Control.Category.NatOrd(
    (:<=:)(..),
    (:>=:),

    Finite'(..), shift',
    fromFinite, toFinite
) where

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Type)

import Data.Proxy (Proxy(..))

import GHC.TypeNats hiding (pattern SNat)
import GHC.TypeNats.Extra

import Data.Finite
import Control.Category.Dual (Dual)

-- | Inductively defined "less than or equals" relation
type (:<=:) :: Nat -> Nat -> Type
data (:<=:) n m where
    ReflLE :: m :<=: m
    SuccLE :: !(m :<=: n) -> m :<=: (1 + n)

instance Category (:<=:) where
    id :: a :<=: a
    id = ReflLE
    
    (.) :: (b :<=: c) -> (a :<=: b) -> a :<=: c
    ReflLE . ab = ab
    SuccLE bc . ab = SuccLE (bc . ab)

-- | "greater than or equals"
type (:>=:) = Dual (:<=:)

-- | Given a type-level @n :: Nat@, @Finite' n@ is the collection of all values
--   of type @m :<=: n@ for some @m :: Nat@.
--
--   Since Each values of @m :<=: n@
data Finite' n where
    Finite' :: (KnownNat m, KnownNat n) => (m :<=: n) -> Finite' (1 + n)

shift' :: Finite' n -> Finite' (1 + n)
shift' (Finite' @_ @n' le) = succKnownNat @n' $ Finite' (SuccLE le)

succKnownNat :: (KnownNat n) => (KnownNat (1 + n) => r) -> r
succKnownNat body = body

fromFinite :: forall n. KnownNat n => Finite n -> Finite' n
fromFinite k = case natSing @n of
    Zero -> absurdFinite k
    Succ n' -> withKnownNat n' $ case unshift k of
        Nothing -> Finite' ReflLE
        Just k' -> shift' (fromFinite k')

toFinite :: Finite' n -> Finite n
toFinite (Finite' @n @m nm) = case nm of
    ReflLE -> zeroFinite
    SuccLE n'm -> shift $ toFinite (Finite' n'm)

absurdFinite :: Finite 0 -> any
absurdFinite n = error $ "Finite 0 is uninhabited: getFinite n = " ++ show (getFinite n)

zeroFinite :: (KnownNat m) => Finite (1 + m)
zeroFinite = natToFinite (Proxy @0)
