{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Data.Functor.Polynomial(
  Poly(..)
) where

import Data.Functor.Classes ( Eq1(..), eq1, Ord1(..), compare1 )
import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..))
import GHC.TypeNats

import Data.Finite
import GHC.TypeLits.Witnesses
import qualified Data.Vector.Sized as SV

import Data.GADT.HasSNat ( HasSNat(..) )
import Data.GADT.Compare

-- | Uniformly represented polynomial functor.
--
--   Given a @'HasSNat' tag@ instance, @Poly tag@ is a polynomial functor.
--   When @tag@ is the inverse images of @α :: U -> Nat@, @Poly@ is isomorphic to:
--
--   > Poly tag x
--   >  = ∑{n :: Nat} (tag n, x^n)
--   >  = ∑{n :: Nat} ∑{u :: U, α(u) == n} x^n
--   >  = ∑{u :: U} x^(α(u))
type Poly :: (Nat -> Type) -> Type -> Type
data Poly tag x where
  P :: tag n -> (Finite n -> x) -> Poly tag x

deriving instance Functor (Poly tag)

instance HasSNat tag => Foldable (Poly tag) where
  null (P tag _) = case toSNat tag of
    Zero -> True
    _    -> False
  length (P tag _) = fromIntegral (fromSNat (toSNat tag))

  foldMap f (P tag rep) = foldMap (f . rep) (withKnownNat (toSNat tag) finites)

instance HasSNat tag => Traversable (Poly tag) where
  traverse f (P tag rep) = P tag <$> traverseFiniteFn (toSNat tag) f rep

traverseFiniteFn :: (Applicative g) => SNat n -> (a -> g b) -> (Finite n -> a) -> g (Finite n -> b)
traverseFiniteFn sn f fromN = withKnownNat sn $ SV.index <$> traverse f (SV.generate fromN)

instance (Eq x, GEq tag, HasSNat tag) => Eq (Poly tag x) where
  (==) = eq1

instance (GEq tag, HasSNat tag) => Eq1 (Poly tag) where
  liftEq eq = eqP
    where
      eqP (P tag rep) (P tag' rep') = case geq tag tag' of
        Nothing -> False
        Just Refl -> all (\i -> rep i `eq` rep' i) (withKnownNat (toSNat tag) finites)

-- | **Does not preserve** the order through 'toPoly' and 'fromPoly'
instance (Ord x, GCompare tag, HasSNat tag) => Ord (Poly tag x) where
  compare = compare1

-- | **Does not preserve** the order through 'toPoly' and 'fromPoly'
instance (GCompare tag, HasSNat tag) => Ord1 (Poly tag) where
  liftCompare cmpX = cmpP
    where
      cmpP (P tag rep) (P tag' rep') = case gcompare tag tag' of
        GLT -> LT
        GEQ -> foldr (\i r -> rep i `cmpX` rep' i <> r) EQ $ withKnownNat (toSNat tag) finites
        GGT -> GT
