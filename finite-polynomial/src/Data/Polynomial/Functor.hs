{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Data.Polynomial.Functor where

import Data.Kind (Type)

import Data.Polynomial
import Data.Functor.Identity
import Data.Proxy (Proxy (..))

import GHC.Generics

data Ev₀ (p :: Poly₀) (x :: Type) where
    MakeEv₀ :: Ev p x -> Ev₀ (NZ p) x

singFromEv₀ :: Ev₀ p x -> Sing Poly₀ p
singFromEv₀ (MakeEv₀ fx) = SingNZ (singFromEv fx)

data Ev (p :: Poly) (x :: Type) where
    EvU :: Ev 'U x
    EvSNothing :: Sing Poly p -> Ev ('S p) x
    EvSJust :: Ev p x -> Ev ('S p) x
    EvT :: x -> Ev p x -> Ev ('T p) x

singFromEv :: Ev p x -> Sing Poly p
singFromEv EvU = SingU
singFromEv (EvSNothing p) = SingS p
singFromEv (EvSJust fx) = SingS (singFromEv fx)
singFromEv (EvT _ fx) = SingT (singFromEv fx)

-- | Non-zero polynomial functor
class PolynomialFunctor f where
    type PolyRep f :: Poly
    sPolyRep :: Sing Poly (PolyRep f)
    toPoly :: f x -> Ev (PolyRep f) x
    fromPoly :: Ev (PolyRep f) x -> f x

instance PolynomialFunctor Proxy where
    type PolyRep Proxy = U
    sPolyRep = SingU
    toPoly _ = EvU
    fromPoly _ = Proxy
 
instance PolynomialFunctor Identity where
    type PolyRep Identity = T U

    sPolyRep = SingT SingU
    toPoly (Identity x) = EvT x EvU
    fromPoly (EvT x EvU) = Identity x

instance PolynomialFunctor U1 where -- wip

instance (PolynomialFunctor f, PolynomialFunctor g) => PolynomialFunctor (f :+: g) where
    type PolyRep (f :+: g) = PolyRep f + PolyRep g

    sPolyRep = sPolyRep @f %+ sPolyRep @g

    toPoly (L1 fx) = fromSum (sPolyRep @f) (sPolyRep @g) (L1 (toPoly fx))
    toPoly (R1 gx) = fromSum (sPolyRep @f) (sPolyRep @g) (R1 (toPoly gx))

    fromPoly hx = case toSum (sPolyRep @f) (sPolyRep @g) hx of
        L1 fx -> L1 (fromPoly fx)
        R1 gx -> R1 (fromPoly gx)

toSum :: Sing Poly p -> Sing Poly q -> Ev (p + q) x -> (Ev p :+: Ev q) x
toSum sp sq hx = case sp of
    SingU -> case hx of
        EvSNothing _ -> L1 EvU
        EvSJust gx -> R1 gx
    SingS sp' -> case hx of
        EvSNothing _ -> L1 (EvSNothing sp')
        EvSJust hx' -> case toSum sp' sq hx' of
            L1 fx -> L1 (EvSJust fx)
            R1 gx -> R1 gx
    SingT sp' -> case sq of
        SingU -> case hx of
            EvSNothing _ -> R1 EvU
            EvSJust fx -> L1 fx
        SingS sq' -> case hx of
            EvSNothing _ -> R1 (EvSNothing sq')
            EvSJust hx' -> case toSum sp sq' hx' of
                L1 fx -> L1 fx
                R1 gx -> R1 (EvSJust gx)
        SingT sq' -> case hx of
            EvT x hx' -> case toSum sp' sq' hx' of
                L1 fx -> L1 (EvT x fx)
                R1 gx -> R1 (EvT x gx)

fromSum :: Sing Poly p -> Sing Poly q -> (Ev p :+: Ev q) x -> Ev (p + q) x
fromSum sp sq fgx = case sp of
    SingU -> case fgx of
        L1 EvU -> EvSNothing sq
        R1 gx -> EvSJust gx
    SingS sp' -> case fgx of
        L1 (EvSNothing _) -> EvSNothing (sp' %+ sq)
        L1 (EvSJust fx) -> EvSJust (fromSum sp' sq (L1 fx))
        R1 gx -> EvSJust (fromSum sp' sq (R1 gx))
    SingT sp' -> case sq of
        SingU -> case fgx of
            L1 fx -> EvSJust fx
            R1 EvU -> EvSNothing sp
        SingS sq' -> case fgx of
            L1 fx -> EvSJust (fromSum sp sq' (L1 fx))
            R1 (EvSNothing _) -> EvSNothing (sp %+ sq')
            R1 (EvSJust gx) -> EvSJust (fromSum sp sq' (R1 gx))
        SingT sq' -> case fgx of
            L1 (EvT x fx) -> EvT x (fromSum sp' sq' (L1 fx))
            R1 (EvT x gx) -> EvT x (fromSum sp' sq' (R1 gx))


instance (PolynomialFunctor f, PolynomialFunctor g) => PolynomialFunctor (f :*: g) where -- wip

instance PolynomialFunctor Par1 where --wip
instance (PolynomialFunctor f, PolynomialFunctor g) => PolynomialFunctor (f :.: g) where -- wip