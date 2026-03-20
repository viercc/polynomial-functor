{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DerivingVia #-}
module Data.Functor.Polynomial.Finitary.Class(
    FinitaryPolynomial(..)
) where

import Data.Functor.Identity
import GHC.Generics hiding (S,C,D)

import Data.Singletons
import Data.Polynomial
import Data.Functor.Polynomial.Finitary

-- | Non-zero polynomial functor
class Functor f => FinitaryPolynomial f where
    type PolyRep f :: P

    sPolyRep :: Sing (PolyRep f)
    toPoly :: f x -> Ev (PolyRep f) x
    fromPoly :: Ev (PolyRep f) x -> f x

instance SingI p => FinitaryPolynomial (Ev p) where
    type PolyRep (Ev p) = p
    sPolyRep = sing
    toPoly = id
    fromPoly = id

instance FinitaryPolynomial Proxy where
    type PolyRep Proxy = U
    sPolyRep = SingU
    toPoly _ = End
    fromPoly _ = Proxy
 
instance FinitaryPolynomial Identity where
    type PolyRep Identity = T U

    sPolyRep = SingT SingU
    toPoly (Identity x) = x ::: End
    fromPoly (x ::: End) = Identity x

instance FinitaryPolynomial U1 where
    type PolyRep U1 = U
    sPolyRep = SingU
    toPoly _ = End
    fromPoly _ = U1

-- | Quick&dirty alternative to @Finitary c => FinitaryPolynomial (K1 i c)@
instance FinitaryPolynomial (K1 i ()) where
    type PolyRep (K1 i ()) = U
    sPolyRep = SingU
    toPoly _ = End
    fromPoly _ = K1 ()

-- | Quick&dirty alternative to @Finitary c => FinitaryPolynomial (K1 i c)@
instance FinitaryPolynomial (K1 i Bool) where
    type PolyRep (K1 i Bool) = S U
    sPolyRep = sing

    toPoly (K1 b) = if b then Go End else Stop
    fromPoly Stop = K1 False
    fromPoly (Go _) = K1 True

instance FinitaryPolynomial f => FinitaryPolynomial (M1 i m f) where
    type PolyRep (M1 _ _ f) = PolyRep f
    sPolyRep = sPolyRep @f
    toPoly = toPoly . unM1
    fromPoly = M1 . fromPoly

instance FinitaryPolynomial f => FinitaryPolynomial (Rec1 f) where
    type PolyRep (Rec1 f) = PolyRep f
    sPolyRep = sPolyRep @f
    toPoly = toPoly . unRec1
    fromPoly = Rec1 . fromPoly

instance (FinitaryPolynomial f, FinitaryPolynomial g) => FinitaryPolynomial (f :+: g) where
    type PolyRep (f :+: g) = PolyRep f + PolyRep g

    sPolyRep = sPolyRep @f %+ sPolyRep @g

    toPoly (L1 fx) = fromSum (sPolyRep @f) (sPolyRep @g) (L1 (toPoly fx))
    toPoly (R1 gx) = fromSum (sPolyRep @f) (sPolyRep @g) (R1 (toPoly gx))

    fromPoly hx = case toSum (sPolyRep @f) (sPolyRep @g) hx of
        L1 fx -> L1 (fromPoly fx)
        R1 gx -> R1 (fromPoly gx)

instance (FinitaryPolynomial f, FinitaryPolynomial g) => FinitaryPolynomial (f :*: g) where
    type PolyRep (f :*: g) = PolyRep f * PolyRep g
    
    sPolyRep = sPolyRep @f %* sPolyRep @g
    toPoly (fx :*: gx) = fromProduct (sPolyRep @f) (sPolyRep @g) (toPoly fx :*: toPoly gx)
    fromPoly hx = case toProduct (sPolyRep @f) (sPolyRep @g) hx of
        (fx :*: gx) -> fromPoly fx :*: fromPoly gx

instance FinitaryPolynomial Par1 where
    type PolyRep Par1 = T U
    sPolyRep = SingT SingU

    toPoly (Par1 x) = x ::: End
    fromPoly (x ::: End) = Par1 x

instance (FinitaryPolynomial f, FinitaryPolynomial g) => FinitaryPolynomial (f :.: g) where
    type PolyRep (f :.: g) = PolyRep f << PolyRep g
    sPolyRep = sPolyRep @f %<< sPolyRep @g

    toPoly (Comp1 fgx) = fromComp (sPolyRep @f) (sPolyRep @g) (toPoly (fmap toPoly fgx))
    fromPoly hx = Comp1 $ fmap (fromPoly @g) $ fromPoly @f $ toComp (sPolyRep @f) (sPolyRep @g) hx

-- via Generically1
instance (Generic1 f, FinitaryPolynomial (Rep1 f)) => FinitaryPolynomial (Generically1 f) where
    type PolyRep (Generically1 f) = PolyRep (Rep1 f)
    sPolyRep = sPolyRep @(Rep1 f)
    toPoly (Generically1 fx) = toPoly @(Rep1 f) . from1 $ fx
    fromPoly = Generically1 . to1 . fromPoly @(Rep1 f)

deriving
  via Generically1 Maybe
  instance FinitaryPolynomial Maybe
