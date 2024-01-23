{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}

module Data.Polynomial.Functor.Deriving(
  ViaPolynomial(..),

  Zippy(..),
  Aligney(..)
) where

import Data.Kind (Type)

import GHC.Generics (Generic1, Generically1(..))

import Data.Singletons
import Data.Polynomial
import Control.Monad ((<=<))

import Data.Coerce

import Data.Polynomial.Functor

-- | Any polynomial functor @'Ev' p@ can have a "zippy" applicative instance.
--
-- >>> type P = 'S ('T ('S ('T 'U))) -- P(x) = 1 + x + x^2
-- >>> pure 0 :: Zippy P Int
-- Zippy {runZippy = EvSJust (EvT 0 (EvSJust (EvT 0 EvU)))}
-- >>> fx = Zippy $ EvSJust (EvT "A" (EvSJust (EvT "a" EvU))) :: Zippy P String
-- >>> fy = Zippy $ EvSJust (EvT "B" EvSNothing) :: Zippy P String
-- >>> fz = Zippy $ EvSNothing :: Zippy P String
-- >>> (++) <$> fx <*> fy
-- Zippy {runZippy = EvSJust (EvT "AB" EvSNothing)}
-- >>> (++) <$> fx <*> fz
-- Zippy {runZippy = EvSNothing}
-- >>> (++) <$> fy <*> fz
-- Zippy {runZippy = EvSNothing}
-- 
newtype Zippy p x = Zippy { runZippy :: Ev p x }
    deriving (Show, Functor, Foldable, Traversable)

instance SingI p => Applicative (Zippy p) where
    pure = Zippy . pureZippy sing

    Zippy fx <*> Zippy fy = Zippy $ apZippy fx fy

pureZippy :: Sing p -> x -> Ev p x
pureZippy SingU = const EvU
pureZippy (SingS sp') = EvSJust . pureZippy sp'
pureZippy (SingT sp') =
    let pure' = pureZippy sp'
    in \x -> EvT x (pure' x)

apZippy :: Ev p (a -> b) -> Ev p a -> Ev p b
apZippy EvU _ = EvU
apZippy EvSNothing _ = EvSNothing
apZippy _ EvSNothing = EvSNothing
apZippy (EvSJust fx') (EvSJust fy') = EvSJust (apZippy fx' fy')
apZippy (EvT x fx') (EvT y fy') = EvT (x y) (apZippy fx' fy')


-- | Any polynomial functor /with no constant term/, @'Ev' (T p)@, can have an \"align-ey\" applicative and monad instance.
--
-- >>> type P = 'T ('S ('T 'U)) -- P(x) = x + x^2
-- >>> pure 0 :: Aligney P Int
-- Aligney {runAligney = EvT 0 EvSNothing}
-- >>> fx = Aligney $ EvT "A" (EvSJust (EvT "a" EvU)) :: Aligney P String
-- >>> fy = Aligney $ EvT "B" (EvSJust (EvT "b" EvU)) :: Aligney P String
-- >>> fz = Aligney $ EvT "C" EvSNothing :: Aligney P String
-- >>> (++) <$> fx <*> fy
-- Aligney {runAligney = EvT "AB" (EvSJust (EvT "ab" EvU))}
-- >>> (++) <$> fx <*> fz
-- Aligney {runAligney = EvT "AC" (EvSJust (EvT "aC" EvU))}
-- >>> (++) <$> fy <*> fz
-- Aligney {runAligney = EvT "BC" (EvSJust (EvT "bC" EvU))}
-- 
-- >>> fx >>= \x -> if x == "A" then fz else fy
-- Aligney {runAligney = EvT "C" (EvSJust (EvT "b" EvU))}
newtype Aligney p x = Aligney { runAligney :: Ev p x }
    deriving (Show, Functor, Foldable, Traversable)

instance SingI p => Applicative (Aligney (T p)) where
    pure = Aligney . pureAligney sing
    Aligney fx <*> Aligney fy = Aligney (apAligney fx fy)

pureAligney :: Sing p -> x -> Ev p x
pureAligney SingU _ = EvU
pureAligney (SingS _) _ = EvSNothing
pureAligney (SingT sp') x = EvT x (pureAligney sp' x)

apAligney :: Ev (T p) (a -> b) -> Ev (T p) a -> Ev (T p) b
apAligney (EvT x fx') (EvT y fy') = EvT (x y) (apAlignAux x y fx' fy')

apAlignAux :: (a -> b) -> a -> Ev p (a -> b) -> Ev p a -> Ev p b
apAlignAux x y fx fy = case (fx, fy) of
    (EvU, EvU) -> EvU
    (EvSNothing, EvSNothing) -> EvSNothing
    (EvSNothing, EvSJust fy') -> EvSJust (x <$> fy')
    (EvSJust fx', EvSNothing) -> EvSJust (($ y) <$> fx')
    (EvSJust fx', EvSJust fy') -> EvSJust (apAlignAux x y fx' fy')
    (EvT x' fx', EvT y' fy') -> EvT (x' y') (apAlignAux x' y' fx' fy')

instance SingI p => Monad (Aligney (T p)) where
    Aligney fx >>= k = Aligney $ bindAligney fx (runAligney . k)

headPoly :: Ev (T p) x -> x
headPoly (EvT x _) = x
tailPoly :: Ev (T p) x -> Ev p x
tailPoly (EvT _ fx) = fx

bindAligney :: Ev ('T p) a -> (a -> Ev ('T p) b) -> Ev ('T p) b
bindAligney fx k = bindAligney' fx (Right . k)

bindAligney' :: Ev ('T p) a -> (a -> Either b (Ev ('T p) b)) -> Ev ('T p) b
bindAligney' (EvT x fx) k = case fx of
    EvU -> either (\b -> EvT b EvU) id $ k x
    EvSNothing -> either (\b -> EvT b EvSNothing) id $ k x
    EvSJust fx' ->
        let EvT z fz' = bindAligney' (EvT x fx') (lowerPolyS <=< k)
        in EvT z (EvSJust fz')
    EvT{} -> EvT (either id headPoly (k x)) (bindAligney' fx (fmap tailPoly . k))

lowerPolyS :: Ev ('T ('S p)) a -> Either a (Ev ('T p) a)
lowerPolyS (EvT x EvSNothing) = Left x
lowerPolyS (EvT x (EvSJust fx)) = Right (EvT x fx)

-- | Generic Deriving
newtype ViaPolynomial (e :: Poly -> Type -> Type) (f :: Type -> Type) a = ViaPolynomial { unwrapViaPolynomial :: f a }
    deriving Functor

instance PolynomialFunctor f => PolynomialFunctor (ViaPolynomial e f) where
    type PolyRep (ViaPolynomial _ f) = PolyRep f
    sPolyRep = sPolyRep @f
    toPoly = toPoly . unwrapViaPolynomial
    fromPoly = ViaPolynomial . fromPoly

instance (PolynomialFunctor f, p ~ PolyRep f, Coercible e Ev, Applicative (e p)) => Applicative (ViaPolynomial e f) where
    pure :: forall a. a -> ViaPolynomial e f a
    pure = fromPoly . coerce @(e p a) @(Ev p a) . pure

    (<*>) :: forall a b. ViaPolynomial e f (a -> b) -> ViaPolynomial e f a -> ViaPolynomial e f b
    fx <*> fy = fromPoly $ coerceBwd $ coerceFwd (toPoly fx) <*> coerceFwd (toPoly fy)
      where
        coerceFwd :: forall c. Ev p c -> e p c
        coerceFwd = coerce
        coerceBwd :: forall c. e p c -> Ev p c
        coerceBwd = coerce

instance (PolynomialFunctor f, p ~ PolyRep f, Coercible e Ev, Monad (e p)) => Monad (ViaPolynomial e f) where
    (>>=) :: forall a b. ViaPolynomial e f a -> (a -> ViaPolynomial e f b) -> ViaPolynomial e f b
    fx >>= k = ViaPolynomial $ fromPoly @f $ coerceBwd $ coerceFwd (toPoly fx) >>= coerceFwd . toPoly . k
      where
        coerceFwd :: forall c. Ev p c -> e p c
        coerceFwd = coerce
        coerceBwd :: forall c. e p c -> Ev p c
        coerceBwd = coerce

--- Example

data Example a = Example (Maybe a) (Maybe a) (Maybe a)
   deriving (Show, Functor, Foldable, Traversable, Generic1)
   deriving PolynomialFunctor via (Generically1 Example)
   deriving Applicative via (ViaPolynomial Zippy Example)

data Example' a = Example1' a | Example2' a a | Example3' a a | Example4' a a a a
   deriving (Show, Functor, Foldable, Traversable, Generic1)
   deriving PolynomialFunctor via (Generically1 Example')
   deriving (Applicative, Monad) via (ViaPolynomial Aligney Example')