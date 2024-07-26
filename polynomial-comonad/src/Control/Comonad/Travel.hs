
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |

Implementation of
"Directed Containers as Categories," D. Ahman and T. Uustalu, EPTCS 207, 2016, pp. 89-98

https://arxiv.org/abs/1604.01187

-}
module Control.Comonad.Travel
  (
    -- * Travel: Comonad from a Category
    Travel (..),
    TravelTag (..),

  )
where

import Control.Category ( Category(..) )
import Control.Comonad
import Data.Kind (Type)
import Data.Singletons
import Data.Singletons.Sigma
import Prelude hiding (id, (.))

import Data.Functor.Polynomial
import Data.Functor.Polynomial.Class
import Data.Singletons.Decide
import Data.Type.Equality
import Data.GADT.Compare (GEq (..))

-- | Make 'Polynomial' 'Comonad' from 'Category'.
--
-- @Travel cat@ is a polynomial functor for any type constructor
-- @cat@.
--
-- @
-- Travel cat r ~ ∑a. ((∑b. cat a b) -> r)
-- @
--
-- @Travel cat@ is a @Comonad@ if @cat@ is a @Category@.
type Travel :: (k -> k -> Type) -> Type -> Type
data Travel (cat :: k -> k -> Type) r where
  MkTravel ::
    forall k (cat :: k -> k -> Type) (r :: Type) (a :: k).
    Sing a ->
    (Sigma k (TyCon (cat a)) -> r) ->
    Travel cat r

instance Functor (Travel cat) where
  fmap f (MkTravel sa k) = MkTravel sa (f . k)

instance (Category cat) => Comonad (Travel (cat :: k -> k -> Type)) where
  extract :: forall r. Travel cat r -> r
  extract (MkTravel sa g) = g (sa :&: id)

  duplicate :: forall r. Travel cat r -> Travel cat (Travel cat r)
  duplicate (MkTravel sa k) = MkTravel sa \(sb :&: ab) -> MkTravel sb \(sc :&: bc) -> k (sc :&: (bc . ab))

type TravelTag :: (k -> k -> Type) -> Type -> Type
data TravelTag cat x where
  TravelFrom
    :: forall k (cat :: k -> k -> Type) (a :: k).
       Sing a -> TravelTag cat (Sigma k (TyCon (cat a)))

instance SDecide k => TestEquality (TravelTag (cat :: k -> k -> Type)) where
  testEquality (TravelFrom sa) (TravelFrom sb) = case sa %~ sb of
    Proved Refl -> Just Refl
    Disproved _ -> Nothing

instance SDecide k => GEq (TravelTag (cat :: k -> k -> Type)) where
  geq = testEquality

instance Polynomial (Travel cat) where
  type Tag (Travel cat) = TravelTag cat

  toPoly (MkTravel sa f) = P (TravelFrom sa) f
  fromPoly (P (TravelFrom sa) f) = MkTravel sa f
