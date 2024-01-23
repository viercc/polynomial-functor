{-# LANGUAGE BlockArguments #-}

module Flow where

import Control.Category
import Control.Monad (ap)
import Control.Monad.Co
import Data.Kind (Type)
import Prelude hiding (id, (.))

import Data.Singletons
import Data.Singletons.Sigma
import PolyComonad

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
valMove :: (SingKind k) => Flow (cat :: k -> k -> Type) -> Demote k -> Demote k
valMove (MkFlow f) valA = case toSing valA of
  SomeSing singA -> fstSigma (f singA)

data Ship (cat :: k -> k -> Type) x = Ship {_transition :: Flow cat, _values :: Demote k -> x}
  deriving (Functor)

instance (Category (cat :: k -> k -> Type), SingKind k) => Applicative (Ship cat) where
  pure x = Ship mempty (const x)
  (<*>) = ap

instance (Category (cat :: k -> k -> Type), SingKind k) => Monad (Ship cat) where
  Ship f1 vx >>= cont = Ship f' vy'
    where
      f' = MkFlow \sa ->
        let x = vx (fromSing sa)
            f2 = _transition (cont x)
         in runFlow (f1 <> f2) sa
      vy' v =
        let x = vx v
            vy = _values (cont x)
         in vy $ valMove f1 v

-- | Forgets the underlying category from @Ship cat@, turning it a simple @State (Val k)@.
forgetCategory ::
  forall k (cat :: k -> k -> Type) x.
  (SingKind k) =>
  Ship cat x ->
  Demote k -> (x, Demote k)
forgetCategory (Ship f vx) v = (vx v, valMove f v)

-- | @'Co' ('Poly' cat)@ is isomorphic to @Ship cat@
fromCoPoly ::
  forall k (cat :: k -> k -> Type) x.
  (Category cat, SingKind k) =>
  Co (Poly cat) x ->
  Ship cat x
fromCoPoly copoly = Ship f vx
  where
    f :: Flow cat
    f = MkFlow $ \sa ->
      runCo copoly $ MkPoly sa const

    vx :: Demote k -> x
    vx valA = case toSing valA of
      SomeSing singA -> runCo copoly $ MkPoly singA \_ x -> x

toCoPoly ::
  forall k (cat :: k -> k -> Type) x.
  (Category cat, SingKind k) =>
  Ship cat x ->
  Co (Poly cat) x
toCoPoly (Ship f vx) = co \(MkPoly sa body) ->
  case runFlow f sa of
    ab -> body ab (vx (fromSing sa))