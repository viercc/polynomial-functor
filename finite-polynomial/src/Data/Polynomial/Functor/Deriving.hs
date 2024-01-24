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

import Data.Singletons
import Data.Polynomial
import Control.Monad ((<=<))

import Data.Coerce

import Data.Polynomial.Functor

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




-- | Any polynomial functor @'Ev' p@ can have a "zippy" applicative instance.
--
-- == Example
-- 
-- >>> type P = 'S ('T ('S ('T 'U))) -- P(x) = 1 + x + x^2
-- >>> pure 0 :: Zippy P Int
-- Zippy {runZippy = Go (0 ::: Go (0 ::: End))}
-- >>> fx = Zippy $ Go ("A" ::: Go ("a" ::: End)) :: Zippy P String
-- >>> fy = Zippy $ Go ("B" ::: Stop) :: Zippy P String
-- >>> fz = Zippy $ Stop :: Zippy P String
-- >>> (++) <$> fx <*> fy
-- Zippy {runZippy = Go ("AB" ::: Stop)}
-- >>> (++) <$> fx <*> fz
-- Zippy {runZippy = Stop}
-- >>> (++) <$> fy <*> fz
-- Zippy {runZippy = Stop}
newtype Zippy p x = Zippy { runZippy :: Ev p x }
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance SingI p => Applicative (Zippy p) where
    pure = Zippy . pureZippy sing

    Zippy fx <*> Zippy fy = Zippy $ apZippy fx fy

pureZippy :: Sing p -> x -> Ev p x
pureZippy SingU = const End
pureZippy (SingS sp') = Go . pureZippy sp'
pureZippy (SingT sp') =
    let pure' = pureZippy sp'
    in \x -> x ::: pure' x

apZippy :: Ev p (a -> b) -> Ev p a -> Ev p b
apZippy End _ = End
apZippy Stop _ = Stop
apZippy _ Stop = Stop
apZippy (Go fx') (Go fy') = Go (apZippy fx' fy')
apZippy (x ::: fx') (y ::: fy') = x y ::: apZippy fx' fy'

-- | Any polynomial functor /with no constant term/, @'Ev' (T p)@, can have an \"aligney\" applicative and monad instance.
-- 
-- == Example
-- 
-- >>> type Q = 'T ('S ('T 'U)) -- Q(x) = x + x^2
-- >>> pure 0 :: Aligney Q Int
-- Aligney {runAligney = 0 ::: Stop}
-- >>> fx = Aligney $ "A" ::: Go ("a" ::: End) :: Aligney Q String
-- >>> fy = Aligney $ "B" ::: Go ("b" ::: End) :: Aligney Q String
-- >>> fz = Aligney $ "C" ::: Stop :: Aligney Q String
-- >>> (++) <$> fx <*> fy
-- Aligney {runAligney = "AB" ::: Go ("ab" ::: End)}
-- >>> (++) <$> fx <*> fz
-- Aligney {runAligney = "AC" ::: Go ("aC" ::: End)}
-- >>> (++) <$> fy <*> fz
-- Aligney {runAligney = "BC" ::: Go ("bC" ::: End)}
-- >>> fx >>= \x -> if x == "A" then fz else fy
-- Aligney {runAligney = "C" ::: Go ("b" ::: End)}
newtype Aligney p x = Aligney { runAligney :: Ev p x }
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance SingI p => Applicative (Aligney (T p)) where
    pure = Aligney . pureAligney sing
    Aligney fx <*> Aligney fy = Aligney (apAligney fx fy)

pureAligney :: Sing p -> x -> Ev p x
pureAligney SingU _ = End
pureAligney (SingS _) _ = Stop
pureAligney (SingT sp') x = x ::: pureAligney sp' x

apAligney :: Ev (T p) (a -> b) -> Ev (T p) a -> Ev (T p) b
apAligney (x ::: fx') (y ::: fy') = x y ::: apAlignAux x y fx' fy'

apAlignAux :: (a -> b) -> a -> Ev p (a -> b) -> Ev p a -> Ev p b
apAlignAux x y fx fy = case (fx, fy) of
    (End, End) -> End
    (Stop, Stop) -> Stop
    (Stop, Go fy') -> Go (x <$> fy')
    (Go fx', Stop) -> Go (($ y) <$> fx')
    (Go fx', Go fy') -> Go (apAlignAux x y fx' fy')
    (x' ::: fx', y' ::: fy') -> x' y' ::: apAlignAux x' y' fx' fy'

instance SingI p => Monad (Aligney (T p)) where
    Aligney fx >>= k = Aligney $ bindAligney fx (runAligney . k)

headPoly :: Ev (T p) x -> x
headPoly (x ::: _) = x
tailPoly :: Ev (T p) x -> Ev p x
tailPoly (_ ::: fx) = fx

bindAligney :: Ev ('T p) a -> (a -> Ev ('T p) b) -> Ev ('T p) b
bindAligney fx k = bindAligney' fx (Right . k)

bindAligney' :: Ev ('T p) a -> (a -> Either b (Ev ('T p) b)) -> Ev ('T p) b
bindAligney' ((:::) x fx) k = case fx of
    End -> either (::: End) id $ k x
    Stop -> either (::: Stop) id $ k x
    Go fx' ->
        let z ::: fz' = bindAligney' (x ::: fx') (lowerPolyS <=< k)
        in z ::: Go fz'
    x' ::: fx' ->
        let z = either id headPoly (k x)
            fz = bindAligney' (x' ::: fx') (fmap tailPoly . k)
        in z ::: fz

lowerPolyS :: Ev ('T ('S p)) a -> Either a (Ev ('T p) a)
lowerPolyS (x ::: Stop) = Left x
lowerPolyS (x ::: Go fx) = Right (x ::: fx)
