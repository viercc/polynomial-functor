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
    End :: Ev 'U x
    Stop :: Ev ('S p) x
    Go :: Ev p x -> Ev ('S p) x
    (:::) :: x -> Ev p x -> Ev ('T p) x

infixr 7 :::

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
    toPoly _ = End
    fromPoly _ = Proxy
 
instance PolynomialFunctor Identity where
    type PolyRep Identity = T U

    sPolyRep = SingT SingU
    toPoly (Identity x) = x ::: End
    fromPoly (x ::: End) = Identity x

instance PolynomialFunctor U1 where
    type PolyRep U1 = U
    sPolyRep = SingU
    toPoly _ = End
    fromPoly _ = U1

-- | Quick&dirty alternative to @Finitary c => PolynomialFunctor (K1 i c)@
instance PolynomialFunctor (K1 i ()) where
    type PolyRep (K1 i ()) = U
    sPolyRep = SingU
    toPoly _ = End
    fromPoly _ = K1 ()

-- | Quick&dirty alternative to @Finitary c => PolynomialFunctor (K1 i c)@
instance PolynomialFunctor (K1 i Bool) where
    type PolyRep (K1 i Bool) = S U
    sPolyRep = sing

    toPoly (K1 b) = if b then Go End else Stop
    fromPoly Stop = K1 False
    fromPoly (Go _) = K1 True

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
        Stop -> L1 End
        Go gx -> R1 gx
    SingS sp' -> case hx of
        Stop -> L1 Stop
        Go hx' -> case toSum sp' sq hx' of
            L1 fx -> L1 (Go fx)
            R1 gx -> R1 gx
    SingT sp' -> case sq of
        SingU -> case hx of
            Stop -> R1 End
            Go fx -> L1 fx
        SingS sq' -> case hx of
            Stop -> R1 Stop
            Go hx' -> case toSum sp sq' hx' of
                L1 fx -> L1 fx
                R1 gx -> R1 (Go gx)
        SingT sq' -> case hx of
            x ::: hx' -> case toSum sp' sq' hx' of
                L1 fx -> L1 (x ::: fx)
                R1 gx -> R1 (x ::: gx)

fromSum :: Sing p -> Sing q -> (Ev p :+: Ev q) x -> Ev (p + q) x
fromSum sp sq fgx = case sp of
    SingU -> case fgx of
        L1 End -> Stop
        R1 gx -> Go gx
    SingS sp' -> case fgx of
        L1 Stop -> Stop
        L1 (Go fx) -> Go (fromSum sp' sq (L1 fx))
        R1 gx -> Go (fromSum sp' sq (R1 gx))
    SingT sp' -> case sq of
        SingU -> case fgx of
            L1 fx -> Go fx
            R1 End -> Stop
        SingS sq' -> case fgx of
            L1 fx -> Go (fromSum sp sq' (L1 fx))
            R1 Stop -> Stop
            R1 (Go gx) -> Go (fromSum sp sq' (R1 gx))
        SingT sq' -> case fgx of
            L1 (x ::: fx) -> x ::: fromSum sp' sq' (L1 fx)
            R1 (x ::: gx) -> x ::: fromSum sp' sq' (R1 gx)

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
            (Stop,  Stop)  -> Stop
            (Go fx', Stop)  -> Go $ fromSum (sp' %+ sq') (sp' %* sq') (L1 $ fromSum sp' sq' (L1 fx'))
            (Stop,  Go gx') -> Go $ fromSum (sp' %+ sq') (sp' %* sq') (L1 $ fromSum sp' sq' (R1 gx'))
            (Go fx', Go gx') -> Go $ fromSum (sp' %+ sq') (sp' %* sq') (R1 $ fromProduct sp' sq' (fx' :*: gx'))
        SingT sq' -> case gx of
            x ::: gx' -> x ::: fromProduct sp sq' (fx :*: gx')
    SingT sp' -> case fx of
        x ::: fx' -> x ::: fromProduct sp' sq (fx' :*: gx)

toProduct :: Sing p -> Sing q -> Ev (p * q) x -> (Ev p :*: Ev q) x
toProduct sp sq hx = case sp of
    SingU -> End :*: hx
    SingS sp' -> case sq of
        SingU -> hx :*: End
        SingS sq' -> case hx of
            Stop -> Stop :*: Stop
            Go hx' -> case toSum (sp' %+ sq') (sp' %* sq') hx' of
                L1 hx'' -> case toSum sp' sq' hx'' of
                    L1 fx' -> Go fx' :*: Stop
                    R1 gx' -> Stop :*: Go gx'
                R1 hx'' ->
                    let fx' :*: gx' = toProduct sp' sq' hx''
                    in Go fx' :*: Go gx'
        SingT sq' -> case hx of
            x ::: hx' ->
                let fx :*: gx' = toProduct sp sq' hx'
                in fx :*: (x ::: gx')
    SingT sp' -> case hx of
        x ::: hx' ->
            let fx' :*: gx = toProduct sp' sq hx'
            in (x ::: fx') :*: gx

instance PolynomialFunctor Par1 where
    type PolyRep Par1 = T U
    sPolyRep = SingT SingU

    toPoly (Par1 x) = x ::: End
    fromPoly (x ::: End) = Par1 x

instance (PolynomialFunctor f, PolynomialFunctor g) => PolynomialFunctor (f :.: g) where
    type PolyRep (f :.: g) = PolyRep f << PolyRep g
    sPolyRep = sPolyRep @f %<< sPolyRep @g

    toPoly (Comp1 fgx) = fromComp (sPolyRep @f) (sPolyRep @g) (toPoly (fmap toPoly fgx))
    fromPoly hx = Comp1 $ fmap (fromPoly @g) $ fromPoly @f $ toComp (sPolyRep @f) (sPolyRep @g) hx

fromComp :: SPoly p -> SPoly q -> Ev p (Ev q x) -> Ev (p << q) x
fromComp sp sq fgx = case sp of
    SingU -> End
    SingS sp' -> case fgx of
        Stop -> Stop
        Go fgx' -> Go (fromComp sp' sq fgx')
    SingT sp' -> case fgx of
        gx ::: fgx' -> fromProduct sq (sp' %<< sq) (gx :*: fromComp sp' sq fgx')

toComp :: SPoly p -> SPoly q -> Ev (p << q) x -> Ev p (Ev q x)
toComp sp sq hx = case sp of
    SingU -> End
    SingS sp' -> case hx of
        Stop -> Stop
        Go hx' -> Go (toComp sp' sq hx')
    SingT sp' -> 
        let gx :*: hx' = toProduct sq (sp' %<< sq) hx
        in gx ::: toComp sp' sq hx'

-- via Generically1
instance (Generic1 f, PolynomialFunctor (Rep1 f)) => PolynomialFunctor (Generically1 f) where
    type PolyRep (Generically1 f) = PolyRep (Rep1 f)
    sPolyRep = sPolyRep @(Rep1 f)
    toPoly (Generically1 fx) = toPoly @(Rep1 f) . from1 $ fx
    fromPoly = Generically1 . to1 . fromPoly @(Rep1 f)

deriving
  via Generically1 Maybe
  instance PolynomialFunctor Maybe
