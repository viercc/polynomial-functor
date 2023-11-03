{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
module Data.Additive where

import Data.Void
import Data.Monoid (Alt (..))
import Control.Applicative (Alternative (..))
import Data.Functor.Contravariant (Predicate (..), Op (..))
import Data.Bifunctor (Bifunctor(..))

import Data.Finite
import Data.Finite.Extra
import GHC.TypeNats.Compat
import GHC.TypeLits.Witnesses ((%+))

-- | Additive is a \"weaker\" version of Alternative or Decidable.
-- 
-- > (Applicative f, Additive f) === Alternative
-- > (Divisible f, Additive f) === Decidable
class Additive f where
    zeroA :: f Void
    sumA :: f a -> f b -> f (Either a b)

instance Alternative f => Additive (Alt f) where
    zeroA = mempty
    sumA fa fb = (Left <$> fa) <> (Right <$> fb)

deriving via (Alt []) instance Additive []

instance Additive (Op b) where
    zeroA = Op absurd
    sumA (Op f) (Op g) = Op (either f g)

deriving via (Op Bool) instance Additive Predicate

data FinitaryIso x where
    FinitaryIso :: KnownNat n => (Finite n -> x) -> (x -> Finite n) -> FinitaryIso x

instance Additive FinitaryIso where
    zeroA = FinitaryIso absurdFinite absurd
    sumA (FinitaryIso @n toA fromA) (FinitaryIso @m toB fromB) = withKnownNat (natSing @n %+ natSing @m) $
        FinitaryIso @(n + m) (bimap toA toB . separateSum) (combineSum . bimap fromA fromB)

data Decision a where
  IsEmpty :: (forall r. a -> r) -> Decision a
  IsNonEmpty :: a -> Decision a

instance Additive Decision where
  zeroA = IsEmpty absurd
  sumA (IsEmpty notA) (IsEmpty notB) = IsEmpty (either notA notB)
  sumA (IsEmpty _) (IsNonEmpty b) = IsNonEmpty (Right b)
  sumA (IsNonEmpty a) _ = IsNonEmpty (Left a)

newtype TraverseFn f x = TraverseFn { runTraverseFn :: forall r. (x -> f r) -> f (x -> r) }

instance Applicative f => Additive (TraverseFn f) where
    zeroA = TraverseFn (\_ -> pure absurd)
    sumA (TraverseFn tx) (TraverseFn ty) = TraverseFn (\f -> either <$> tx (f . Left) <*> ty (f . Right))