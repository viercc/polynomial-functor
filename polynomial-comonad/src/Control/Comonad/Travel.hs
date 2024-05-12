
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE MonoLocalBinds #-}
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

    -- * Chart: Monad from a Category
    Flow (..),
    truncateFlow,
    Chart (..),
    truncateChart,

    toCoTravel,
    fromCoTravel
  )
where

import Control.Category ( Category(..) )
import Control.Comonad
import Control.Monad (ap)
import Control.Monad.Co
import Data.Kind (Type)
import Data.Singletons
import Data.Singletons.Sigma
import Prelude hiding (id, (.))
import Control.Monad.Trans.State (State, state)

import Data.Functor.Polynomial
import Data.Functor.Polynomial.Class
import Data.Singletons.Decide
import Data.Type.Equality
import Data.GADT.Compare (GEq (..))

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

-- * Flows and Charts

-- | > Flow cat = Π(a :: k). ∑(b :: k). cat a b
--
--  In words, @fl :: Flow cat@ is a collection of
--  arrows in @cat@ such that for each object @a@, there's exactly one
--  arrow starting from @a@ in it.
newtype Flow (cat :: k -> k -> Type) = MkFlow
  {runFlow :: forall (a :: k). Sing a -> Sigma k (TyCon (cat a))}

instance (Category cat) => Semigroup (Flow cat) where
  MkFlow f1 <> MkFlow f2 = MkFlow \sa ->
    case f2 sa of
      sb :&: ab -> case f1 sb of
        sc :&: bc -> sc :&: (bc . ab)

instance (Category cat) => Monoid (Flow cat) where
  mempty = MkFlow \sa -> sa :&: id

-- | Forgets underlying category from a flow, treating it as a
--   simple function on objects of @cat@.
--
--   Objects of @cat@ are type-level things of kind @k@,
--   so it demotes @k@ to value-level @Val k@.
truncateFlow :: (SingKind k) => Flow (cat :: k -> k -> Type) -> Demote k -> Demote k
truncateFlow (MkFlow f) valA = case toSing valA of
  SomeSing singA -> fstSigma (f singA)

-- | @'Chart' cat@ is @'Flow' cat@ plus values for each objects in the category.
--
--   @Chart@ can be thought of as a generalization of the @'State'@ Monad.
--
--   A value of @State s x@ describes:
--
--   - For each state @s1 :: s@, a next state @s2 :: s@
--   - For each state @s1 :: s@, a value @x1 :: x@
--
--   A value of @Chart cat@ describes:
--
--   - For each object @s1 :: k@, an arrow @f :: cat s1 s2@ starting from @s1@
--     and going to a next object @s2@
--   - For each object @s1 :: k@, a value @x1 :: x@
data Chart (cat :: k -> k -> Type) x = Chart {_flow :: Flow cat, _values :: Demote k -> x}
  deriving (Functor)

instance (Category (cat :: k -> k -> Type), SingKind k) => Applicative (Chart cat) where
  pure x = Chart mempty (const x)
  (<*>) = ap

instance (Category (cat :: k -> k -> Type), SingKind k) => Monad (Chart cat) where
  Chart f1 vx >>= cont = Chart f' vy'
    where
      f' = MkFlow \sa ->
        let x = vx (fromSing sa)
            f2 = _flow (cont x)
         in runFlow (f1 <> f2) sa
      vy' v =
        let x = vx v
            vy = _values (cont x)
         in vy $ truncateFlow f1 v

-- | Forgets the underlying category from @Chart cat@, converting it to a simple @State@ monad.
truncateChart ::
  forall k (cat :: k -> k -> Type) x.
  (SingKind k) =>
  Chart cat x ->
  State (Demote k) x
truncateChart (Chart f vx) = state \v -> (vx v, truncateFlow f v)

-- | @'Co' ('Travel' cat)@ is isomorphic to @'Chart' cat@
fromCoTravel ::
  forall k (cat :: k -> k -> Type) x.
  (Category cat, SingKind k) =>
  Co (Travel cat) x ->
  Chart cat x
fromCoTravel coTravel = Chart f vx
  where
    f :: Flow cat
    f = MkFlow $ \sa ->
      runCo coTravel $ MkTravel sa const

    vx :: Demote k -> x
    vx valA = case toSing valA of
      SomeSing singA -> runCo coTravel $ MkTravel singA \_ x -> x

-- | @'Co' ('Travel' cat)@ is isomorphic to @Chart cat@
toCoTravel ::
  forall k (cat :: k -> k -> Type) x.
  (Category cat, SingKind k) =>
  Chart cat x ->
  Co (Travel cat) x
toCoTravel (Chart f vx) = co \(MkTravel sa body) ->
  case runFlow f sa of
    ab -> body ab (vx (fromSing sa))