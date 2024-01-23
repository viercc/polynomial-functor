{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DerivingVia #-}
module Data.Polynomial.Functor(
    Ev(..), Ev₀(..),
    PolynomialFunctor(..),

    toSum, fromSum, toProduct, fromProduct,
    toComp, fromComp
) where

import Data.Kind (Type)

import Data.Functor.Identity
import GHC.Generics hiding (S,C,D)

import Data.Singletons
import Data.Polynomial

data Ev₀ (p :: Poly₀) (x :: Type) where
    MakeEv₀ :: Ev p x -> Ev₀ (NZ p) x

deriving instance Show x => Show (Ev₀ p x)
deriving instance Functor (Ev₀ p)

data Ev (p :: Poly) (x :: Type) where
    EvU :: Ev 'U x
    EvSNothing :: Ev ('S p) x
    EvSJust :: Ev p x -> Ev ('S p) x
    EvT :: x -> Ev p x -> Ev ('T p) x

deriving instance Show x => Show (Ev p x)
deriving instance Functor (Ev p)
deriving instance Foldable (Ev p)
deriving instance Traversable (Ev p)

-- | Non-zero polynomial functor
class Functor f => PolynomialFunctor f where
    type PolyRep f :: Poly

    sPolyRep :: Sing (PolyRep f)
    toPoly :: f x -> Ev (PolyRep f) x
    fromPoly :: Ev (PolyRep f) x -> f x

instance SingI p => PolynomialFunctor (Ev p) where
    type PolyRep (Ev p) = p
    sPolyRep = sing
    toPoly = id
    fromPoly = id

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

instance PolynomialFunctor U1 where
    type PolyRep U1 = U
    sPolyRep = SingU
    toPoly _ = EvU
    fromPoly _ = U1

-- | Quick&dirty alternative to @Finitary c => PolynomialFunctor (K1 i c)@
instance PolynomialFunctor (K1 i ()) where
    type PolyRep (K1 i ()) = U
    sPolyRep = SingU
    toPoly _ = EvU
    fromPoly _ = K1 ()

-- | Quick&dirty alternative to @Finitary c => PolynomialFunctor (K1 i c)@
instance PolynomialFunctor (K1 i Bool) where
    type PolyRep (K1 i Bool) = S U
    sPolyRep = sing

    toPoly (K1 b) = if b then EvSJust EvU else EvSNothing
    fromPoly EvSNothing = K1 False
    fromPoly (EvSJust _) = K1 True

instance PolynomialFunctor f => PolynomialFunctor (M1 i m f) where
    type PolyRep (M1 _ _ f) = PolyRep f
    sPolyRep = sPolyRep @f
    toPoly = toPoly . unM1
    fromPoly = M1 . fromPoly

instance PolynomialFunctor f => PolynomialFunctor (Rec1 f) where
    type PolyRep (Rec1 f) = PolyRep f
    sPolyRep = sPolyRep @f
    toPoly = toPoly . unRec1
    fromPoly = Rec1 . fromPoly

instance (PolynomialFunctor f, PolynomialFunctor g) => PolynomialFunctor (f :+: g) where
    type PolyRep (f :+: g) = PolyRep f + PolyRep g

    sPolyRep = sPolyRep @f %+ sPolyRep @g

    toPoly (L1 fx) = fromSum (sPolyRep @f) (sPolyRep @g) (L1 (toPoly fx))
    toPoly (R1 gx) = fromSum (sPolyRep @f) (sPolyRep @g) (R1 (toPoly gx))

    fromPoly hx = case toSum (sPolyRep @f) (sPolyRep @g) hx of
        L1 fx -> L1 (fromPoly fx)
        R1 gx -> R1 (fromPoly gx)

toSum :: Sing p -> Sing q -> Ev (p + q) x -> (Ev p :+: Ev q) x
toSum sp sq hx = case sp of
    SingU -> case hx of
        EvSNothing -> L1 EvU
        EvSJust gx -> R1 gx
    SingS sp' -> case hx of
        EvSNothing -> L1 EvSNothing
        EvSJust hx' -> case toSum sp' sq hx' of
            L1 fx -> L1 (EvSJust fx)
            R1 gx -> R1 gx
    SingT sp' -> case sq of
        SingU -> case hx of
            EvSNothing -> R1 EvU
            EvSJust fx -> L1 fx
        SingS sq' -> case hx of
            EvSNothing -> R1 EvSNothing
            EvSJust hx' -> case toSum sp sq' hx' of
                L1 fx -> L1 fx
                R1 gx -> R1 (EvSJust gx)
        SingT sq' -> case hx of
            EvT x hx' -> case toSum sp' sq' hx' of
                L1 fx -> L1 (EvT x fx)
                R1 gx -> R1 (EvT x gx)

fromSum :: Sing p -> Sing q -> (Ev p :+: Ev q) x -> Ev (p + q) x
fromSum sp sq fgx = case sp of
    SingU -> case fgx of
        L1 EvU -> EvSNothing
        R1 gx -> EvSJust gx
    SingS sp' -> case fgx of
        L1 EvSNothing -> EvSNothing
        L1 (EvSJust fx) -> EvSJust (fromSum sp' sq (L1 fx))
        R1 gx -> EvSJust (fromSum sp' sq (R1 gx))
    SingT sp' -> case sq of
        SingU -> case fgx of
            L1 fx -> EvSJust fx
            R1 EvU -> EvSNothing
        SingS sq' -> case fgx of
            L1 fx -> EvSJust (fromSum sp sq' (L1 fx))
            R1 EvSNothing -> EvSNothing
            R1 (EvSJust gx) -> EvSJust (fromSum sp sq' (R1 gx))
        SingT sq' -> case fgx of
            L1 (EvT x fx) -> EvT x (fromSum sp' sq' (L1 fx))
            R1 (EvT x gx) -> EvT x (fromSum sp' sq' (R1 gx))

instance (PolynomialFunctor f, PolynomialFunctor g) => PolynomialFunctor (f :*: g) where
    type PolyRep (f :*: g) = PolyRep f * PolyRep g
    
    sPolyRep = sPolyRep @f %* sPolyRep @g
    toPoly (fx :*: gx) = fromProduct (sPolyRep @f) (sPolyRep @g) (toPoly fx :*: toPoly gx)
    fromPoly hx = case toProduct (sPolyRep @f) (sPolyRep @g) hx of
        (fx :*: gx) -> fromPoly fx :*: fromPoly gx

fromProduct :: Sing p -> Sing q -> (Ev p :*: Ev q) x -> Ev (p * q) x
fromProduct sp sq (fx :*: gx) = case sp of
    SingU -> gx
    SingS sp' -> case sq of
        SingU -> fx
        SingS sq' -> case (fx, gx) of
            (EvSNothing,  EvSNothing)  -> EvSNothing
            (EvSJust fx', EvSNothing)  -> EvSJust $ fromSum (sp' %+ sq') (sp' %* sq') (L1 $ fromSum sp' sq' (L1 fx'))
            (EvSNothing,  EvSJust gx') -> EvSJust $ fromSum (sp' %+ sq') (sp' %* sq') (L1 $ fromSum sp' sq' (R1 gx'))
            (EvSJust fx', EvSJust gx') -> EvSJust $ fromSum (sp' %+ sq') (sp' %* sq') (R1 $ fromProduct sp' sq' (fx' :*: gx'))
        SingT sq' -> case gx of
            EvT x gx' -> EvT x $ fromProduct sp sq' (fx :*: gx')
    SingT sp' -> case fx of
        EvT x fx' -> EvT x $ fromProduct sp' sq (fx' :*: gx)

toProduct :: Sing p -> Sing q -> Ev (p * q) x -> (Ev p :*: Ev q) x
toProduct sp sq hx = case sp of
    SingU -> EvU :*: hx
    SingS sp' -> case sq of
        SingU -> hx :*: EvU
        SingS sq' -> case hx of
            EvSNothing -> EvSNothing :*: EvSNothing
            EvSJust hx' -> case toSum (sp' %+ sq') (sp' %* sq') hx' of
                L1 hx'' -> case toSum sp' sq' hx'' of
                    L1 fx' -> EvSJust fx' :*: EvSNothing
                    R1 gx' -> EvSNothing :*: EvSJust gx'
                R1 hx'' ->
                    let fx' :*: gx' = toProduct sp' sq' hx''
                    in EvSJust fx' :*: EvSJust gx'
        SingT sq' -> case hx of
            EvT x hx' ->
                let fx :*: gx' = toProduct sp sq' hx'
                in fx :*: EvT x gx'
    SingT sp' -> case hx of
        EvT x hx' ->
            let fx' :*: gx = toProduct sp' sq hx'
            in EvT x fx' :*: gx

instance PolynomialFunctor Par1 where
    type PolyRep Par1 = T U
    sPolyRep = SingT SingU

    toPoly (Par1 x) = EvT x EvU
    fromPoly (EvT x EvU) = Par1 x

instance (PolynomialFunctor f, PolynomialFunctor g) => PolynomialFunctor (f :.: g) where
    type PolyRep (f :.: g) = PolyRep f << PolyRep g
    sPolyRep = sPolyRep @f %<< sPolyRep @g

    toPoly (Comp1 fgx) = fromComp (sPolyRep @f) (sPolyRep @g) (fmap toPoly (toPoly fgx))
    fromPoly hx = Comp1 $ fromPoly @f $ fmap (fromPoly @g) $ toComp (sPolyRep @f) (sPolyRep @g) hx

fromComp :: SPoly p -> SPoly q -> (Ev p (Ev q x)) -> Ev (p << q) x
fromComp sp sq fgx = case sp of
    SingU -> EvU
    SingS sp' -> case fgx of
        EvSNothing -> EvSNothing
        EvSJust fgx' -> EvSJust (fromComp sp' sq fgx')
    SingT sp' -> case fgx of
        EvT gx fgx' -> fromProduct sq (sp' %<< sq) (gx :*: fromComp sp' sq fgx')

toComp :: SPoly p -> SPoly q -> Ev (p << q) x -> Ev p (Ev q x)
toComp sp sq hx = case sp of
    SingU -> EvU
    SingS sp' -> case hx of
        EvSNothing -> EvSNothing
        EvSJust hx' -> EvSJust (toComp sp' sq hx')
    SingT sp' -> 
        let gx :*: hx' = toProduct sq (sp' %<< sq) hx
        in EvT gx (toComp sp' sq hx')

-- via Generically1
instance (Generic1 f, PolynomialFunctor (Rep1 f)) => PolynomialFunctor (Generically1 f) where
    type PolyRep (Generically1 f) = PolyRep (Rep1 f)
    sPolyRep = sPolyRep @(Rep1 f)
    toPoly (Generically1 fx) = toPoly @(Rep1 f) . from1 $ fx
    fromPoly = Generically1 . to1 . fromPoly @(Rep1 f)

deriving
  via Generically1 Maybe
  instance PolynomialFunctor Maybe
