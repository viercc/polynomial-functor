{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Control.Monad.Flow(
    -- * Flow: Monad from a Category
    Flow,
    mkFlow,
    truncateFlow,

    toCoTravel,
    fromCoTravel,

    -- * Transformer version
    FlowT (..),
    truncateFlowT,
) where

import Control.Category ( Category(..), (>>>) )
import Control.Comonad
import Control.Monad (ap)
import Control.Monad.Co
import Data.Kind (Type)
import Data.Singletons
import Data.Singletons.Sigma
import Prelude hiding (id, (.))
import Control.Monad.Trans.State (State, StateT (..))

import Data.Functor.Identity
import Data.Functor ((<&>))
import Control.Monad.Trans.Class (MonadTrans (..))

import Control.Comonad.Travel

-- | @Flow@ can be thought of as a generalization of the @'State'@ Monad.
--
--   A value of @State s x@ describes:
--
--   - For each state @s1 :: s@, a next state @s2 :: s@
--   - For each state @s1 :: s@, a value @x1 :: x@
--
--   A value of @Flow cat@ describes:
--
--   - For each object @s1 :: k@, an arrow @f :: cat s1 s2@ starting from @s1@
--     and going to a next object @s2@
--   - For each object @s1 :: k@, a value @x1 :: x@
type Flow cat = FlowT cat Identity

mkFlow :: forall k (cat :: k -> k -> Type) x.
  (forall (a :: k). Sing a -> (x, Sigma k (TyCon (cat a))))
  -> Flow cat x
mkFlow f = MkFlowT (Identity . f)

runFlow :: forall k (cat :: k -> k -> Type) x (a :: k).
  Flow cat x -> Sing a -> (x, Sigma k (TyCon (cat a)))
runFlow mx sa = runIdentity $ runFlowT mx sa

-- | Forgets arrows of the underlying category from @Flow cat@,
--   converting it to a simple @State@ monad on objects of @cat@.
truncateFlow ::
  forall k (cat :: k -> k -> Type) x.
  (SingKind k) =>
  Flow cat x ->
  State (Demote k) x
truncateFlow mx = StateT \a -> case toSing a of
  SomeSing sa -> runFlowT mx sa <&> \(x, sb :&: _) -> (x, fromSing sb)

-- | @'Co' ('Travel' cat)@ is isomorphic to @'Flow' cat@
fromCoTravel ::
  forall k (cat :: k -> k -> Type) x.
  (Category cat) =>
  Co (Travel cat) x ->
  Flow cat x
fromCoTravel coTravel = MkFlowT $ \sa ->
    runCo coTravel $ MkTravel sa (\key x -> Identity (x, key))

-- | @'Co' ('Travel' cat)@ is isomorphic to @'Flow' cat@
toCoTravel ::
  forall k (cat :: k -> k -> Type) x.
  (Category cat) =>
  Flow cat x ->
  Co (Travel cat) x
toCoTravel mx = co \(MkTravel sa body) ->
  case runFlow mx sa of
    (x, key) -> body key x

---- FlowT ----

-- | Transformer version of @Flow@.
newtype FlowT (cat :: k -> k -> Type) m x = MkFlowT {
    runFlowT :: forall (a :: k). Sing a -> m (x, Sigma k (TyCon (cat a)))
  }
  deriving (Functor)

instance (Category cat, Monad m) => Applicative (FlowT cat m) where
  pure x = MkFlowT $ \sa -> pure (x, sa :&: id)
  (<*>) = ap

instance (Category cat, Monad m) => Monad (FlowT cat m) where
  mx >>= k = MkFlowT $ \sa ->
    do (y, sb :&: f) <- runFlowT mx sa
       (z, sc :&: g) <- runFlowT (k y) sb
       pure (z, sc :&: (f >>> g))

instance (Category cat) => MonadTrans (FlowT cat) where
  lift mx = MkFlowT $ \sa -> mx <&> \x -> (x, sa :&: id)

-- | Forgets arrows of the underlying category from @FlowT cat m@,
--   converting it to a simple @StateT@ on objects of @cat@.
truncateFlowT ::
  forall k (cat :: k -> k -> Type) m x.
  (SingKind k, Monad m) =>
  FlowT cat m x ->
  StateT (Demote k) m x
truncateFlowT mx = StateT \a -> case toSing a of
  SomeSing sa -> runFlowT mx sa <&> \(x, sb :&: _) -> (x, fromSing sb)
