{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Functor.Polynomial.Finitary.Tag(
    FinPolyTag(..),
) where

import Data.Kind (Type)
import Data.Void (Void)
import Data.Type.Equality ((:~:)(..))

import Data.GADT.Compare (GEq(..), GCompare(..), GOrdering(..))
import Data.GADT.HasFinitary (HasFinitary(..))

import Data.Polynomial (P(..))

-- | Tag GADT for @'Ev' p@.
--
--   @FinPolyTag p n@ witnesses that @n@ is the position type of one summand of @'Ev' p@.
--
--   This gives @'Ev' p@ an instance of 'Polynomial' from the @polynomial-functor@ package,
--   with @'Tag' ('Ev' p) = 'FinPolyTag' p@.
data FinPolyTag (p :: P) (n :: Type) where
    FinPolyEnd  ::                    FinPolyTag 'U       Void
    FinPolyStop ::                    FinPolyTag ('S p)   Void
    FinPolyGo   :: FinPolyTag p n ->  FinPolyTag ('S p)   n
    FinPolyCons :: FinPolyTag p n ->  FinPolyTag ('T p)   (Either () n)

instance HasFinitary (FinPolyTag p) where
    withFinitary FinPolyEnd      body = body
    withFinitary FinPolyStop     body = body
    withFinitary (FinPolyGo   t) body = withFinitary t body
    withFinitary (FinPolyCons t) body = withFinitary t body

instance GEq (FinPolyTag p) where
    geq FinPolyEnd       FinPolyEnd       = Just Refl
    geq FinPolyStop      FinPolyStop      = Just Refl
    geq (FinPolyGo   t) (FinPolyGo   t') = geq t t'
    geq (FinPolyCons t) (FinPolyCons t') = do
        Refl <- geq t t'
        pure Refl
    geq _ _ = Nothing

instance GCompare (FinPolyTag p) where
    gcompare FinPolyEnd      FinPolyEnd       = GEQ
    gcompare FinPolyStop     FinPolyStop      = GEQ
    gcompare (FinPolyGo   t) (FinPolyGo   t') = gcompare t t'
    gcompare (FinPolyCons t) (FinPolyCons t') = case gcompare t t' of
        GLT -> GLT
        GEQ -> GEQ
        GGT -> GGT
    -- Remaining cases: constructors with different arities/indices can't share p,
    -- so these are exhaustive within a fixed p.
    gcompare FinPolyStop     (FinPolyGo   _)  = GLT
    gcompare (FinPolyGo   _) FinPolyStop      = GGT
