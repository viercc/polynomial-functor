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
module Data.Polynomial.Functor(
    Ev(..), Ev₀(..),
    PolynomialFunctor(..),

    toSum, fromSum, toProduct, fromProduct,
    toComp, fromComp,

    ZipPoly(..),
    AlignPoly(..)
) where

import Data.Kind (Type)

import Data.Functor.Identity
import GHC.Generics
    ( U1(..), Par1(..), type (:+:)(..), type (:*:)(..), type (:.:)(..) )

import Data.Singletons
import Data.Polynomial
import Control.Monad ((<=<))


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
class PolynomialFunctor f where
    type PolyRep f :: Poly

    sPolyRep :: Sing (PolyRep f)
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

instance PolynomialFunctor U1 where
    type PolyRep U1 = U
    sPolyRep = SingU
    toPoly _ = EvU
    fromPoly _ = U1

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

-- | Any polynomial functor @'Ev' p@ can have a "zippy" applicative instance.
--
-- >>> type P = 'S ('T ('S ('T 'U))) -- P(x) = 1 + x + x^2
-- >>> pure 0 :: ZipPoly P Int
-- ZipPoly {runZipPoly = EvSJust (EvT 0 (EvSJust (EvT 0 EvU)))}
-- >>> fx = ZipPoly $ EvSJust (EvT "A" (EvSJust (EvT "a" EvU))) :: ZipPoly P String
-- >>> fy = ZipPoly $ EvSJust (EvT "B" EvSNothing) :: ZipPoly P String
-- >>> fz = ZipPoly $ EvSNothing :: ZipPoly P String
-- >>> (++) <$> fx <*> fy
-- ZipPoly {runZipPoly = EvSJust (EvT "AB" EvSNothing)}
-- >>> (++) <$> fx <*> fz
-- ZipPoly {runZipPoly = EvSNothing}
-- >>> (++) <$> fy <*> fz
-- ZipPoly {runZipPoly = EvSNothing}
-- 
newtype ZipPoly p x = ZipPoly { runZipPoly :: Ev p x }
    deriving (Show, Functor)

instance SingI p => Applicative (ZipPoly p) where
    pure = ZipPoly . pureZipPoly sing

    ZipPoly fx <*> ZipPoly fy = ZipPoly (apZipPoly fx fy)

pureZipPoly :: Sing p -> x -> Ev p x
pureZipPoly SingU = const EvU
pureZipPoly (SingS sp') = EvSJust . pureZipPoly sp'
pureZipPoly (SingT sp') =
    let pure' = pureZipPoly sp'
    in \x -> EvT x (pure' x)

apZipPoly :: Ev p (a -> b) -> Ev p a -> Ev p b
apZipPoly EvU _ = EvU
apZipPoly EvSNothing _ = EvSNothing
apZipPoly _ EvSNothing = EvSNothing
apZipPoly (EvSJust fx') (EvSJust fy') = EvSJust (apZipPoly fx' fy')
apZipPoly (EvT x fx') (EvT y fy') = EvT (x y) (apZipPoly fx' fy')


-- | Any polynomial functor /with no constant term/, @'Ev' (T p)@, can have an \"align-ey\" applicative and monad instance.
-- 
-- >>> type P = 'T ('S ('T 'U)) -- P(x) = x + x^2
-- >>> pure 0 :: AlignPoly P Int
-- AlignPoly {runAlignPoly = EvT 0 EvSNothing}
-- 
-- >>> fx = AlignPoly $ EvT "A" (EvSJust (EvT "a" EvU)) :: AlignPoly P String
-- >>> fy = AlignPoly $ EvT "B" (EvSJust (EvT "b" EvU)) :: AlignPoly P String
-- >>> fz = AlignPoly $ EvT "C" EvSNothing :: AlignPoly P String
-- >>> (++) <$> fx <*> fy
-- AlignPoly {runAlignPoly = EvT "AB" (EvSJust (EvT "ab" EvU))}
-- >>> (++) <$> fx <*> fz
-- AlignPoly {runAlignPoly = EvT "AC" (EvSJust (EvT "aC" EvU))}
-- >>> (++) <$> fy <*> fz
-- AlignPoly {runAlignPoly = EvT "BC" (EvSJust (EvT "bC" EvU))}
-- 
-- >>> fx >>= \x -> if x == "A" then fz else fy
-- AlignPoly {runAlignPoly = EvT "C" (EvSJust (EvT "b" EvU))}
newtype AlignPoly p x = AlignPoly { runAlignPoly :: Ev p x }
    deriving (Show, Functor)

instance SingI p => Applicative (AlignPoly (T p)) where
    pure = AlignPoly . pureAlignPoly sing
    AlignPoly fx <*> AlignPoly fy = AlignPoly (apAlignPoly fx fy)

pureAlignPoly :: Sing p -> x -> Ev p x
pureAlignPoly SingU _ = EvU
pureAlignPoly (SingS _) _ = EvSNothing
pureAlignPoly (SingT sp') x = EvT x (pureAlignPoly sp' x)

apAlignPoly :: Ev (T p) (a -> b) -> Ev (T p) a -> Ev (T p) b
apAlignPoly (EvT x fx') (EvT y fy') = EvT (x y) (apAlignAux x y fx' fy')

apAlignAux :: (a -> b) -> a -> Ev p (a -> b) -> Ev p a -> Ev p b
apAlignAux x y fx fy = case (fx, fy) of
    (EvU, EvU) -> EvU
    (EvSNothing, EvSNothing) -> EvSNothing
    (EvSNothing, EvSJust fy') -> EvSJust (x <$> fy')
    (EvSJust fx', EvSNothing) -> EvSJust (($ y) <$> fx')
    (EvSJust fx', EvSJust fy') -> EvSJust (apAlignAux x y fx' fy')
    (EvT x' fx', EvT y' fy') -> EvT (x' y') (apAlignAux x' y' fx' fy')

instance SingI p => Monad (AlignPoly (T p)) where
    AlignPoly fx >>= k = AlignPoly $ bindAlignPoly fx (runAlignPoly . k)

headPoly :: Ev (T p) x -> x
headPoly (EvT x _) = x
tailPoly :: Ev (T p) x -> Ev p x
tailPoly (EvT _ fx) = fx

bindAlignPoly :: Ev ('T p) a -> (a -> Ev ('T p) b) -> Ev ('T p) b
bindAlignPoly fx k = bindAlignPoly' fx (Right . k)

bindAlignPoly' :: Ev ('T p) a -> (a -> Either b (Ev ('T p) b)) -> Ev ('T p) b
bindAlignPoly' (EvT x fx) k = case fx of
    EvU -> either (\b -> EvT b EvU) id $ k x
    EvSNothing -> either (\b -> EvT b EvSNothing) id $ k x
    EvSJust fx' ->
        let EvT z fz' = bindAlignPoly' (EvT x fx') (lowerPolyS <=< k)
        in EvT z (EvSJust fz')
    EvT{} -> EvT (either id headPoly (k x)) (bindAlignPoly' fx (fmap tailPoly . k))

lowerPolyS :: Ev ('T ('S p)) a -> Either a (Ev ('T p) a)
lowerPolyS (EvT x EvSNothing) = Left x
lowerPolyS (EvT x (EvSJust fx)) = Right (EvT x fx)
