{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE RankNTypes #-}
module Data.Functor.Polynomial(
  Poly(..)
) where

import Data.Functor.Classes ( Eq1(..), eq1, Ord1(..), compare1 )
import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..))

import GHC.TypeNats hiding (SNat)
import GHC.TypeNats.Extra
import Data.Finite
import qualified Data.Vector.Sized as SV

import Data.GADT.Compare
import Data.Finitary
import Data.GADT.HasFinitary

-- | Uniformly represented polynomial functor.
--
--   Given a @'HasFinitary' tag@ instance, @Poly tag@ is a polynomial functor.
--   When @tag@ is the inverse images of @α :: U -> Type@, @Poly@ is isomorphic to:
--
--   > Poly tag x
--   >  = ∑{n :: Type} (tag n, x^n)
--   >  = ∑{n :: Type} ∑{u :: U, α(u) == n} x^n
--   >  = ∑{u :: U} x^(α(u))
type Poly :: (Type -> Type) -> Type -> Type
data Poly tag x where
  P :: tag n -> (n -> x) -> Poly tag x

deriving instance Functor (Poly tag)

instance HasFinitary tag => Foldable (Poly tag) where
  null (P tag _) = case toSNat tag of 
    Zero -> True
    _    -> False
  length (P tag _) = fromIntegral (fromSNat (toSNat tag))

  foldMap f (P tag rep) = withFinitary' tag $ \sn ->
    foldMap (f . rep . fromFinite) (withKnownNat sn finites)

instance HasFinitary tag => Traversable (Poly tag) where
  traverse f (P tag rep) = P tag <$> withFinitary tag (traverseFiniteFn f rep)

traverseFiniteFn :: (Finitary n, Applicative g) => (a -> g b) -> (n -> a) -> g (n -> b)
traverseFiniteFn f fromN = indexByN <$> traverse f (SV.generate (fromN . fromFinite))
  where
    indexByN xs k = SV.index xs (toFinite k)

instance (Eq x, GEq tag, HasFinitary tag) => Eq (Poly tag x) where
  (==) = eq1

instance (GEq tag, HasFinitary tag) => Eq1 (Poly tag) where
  liftEq eq = eqP
    where
      eqP (P tag rep) (P tag' rep') = case geq tag tag' of
        Nothing -> False
        Just Refl -> all (\i -> rep i `eq` rep' i) (toInhabitants tag)

-- | **Does not preserve** the order through 'toPoly' and 'fromPoly'
instance (Ord x, GCompare tag, HasFinitary tag) => Ord (Poly tag x) where
  compare = compare1

-- | **Does not preserve** the order through 'toPoly' and 'fromPoly'
instance (GCompare tag, HasFinitary tag) => Ord1 (Poly tag) where
  liftCompare cmpX = cmpP
    where
      cmpP (P tag rep) (P tag' rep') = case gcompare tag tag' of
        GLT -> LT
        GEQ -> foldr (\i r -> rep i `cmpX` rep' i <> r) EQ $ toInhabitants tag
        GGT -> GT
