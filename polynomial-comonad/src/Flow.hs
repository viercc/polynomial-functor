{-# LANGUAGE BlockArguments #-}
module Flow where

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Type)
import Control.Monad (ap)

import BabySingleton
import PolyComonad
import Control.Monad.Co

-- | Conceptually:
-- 
--  > Flow (cat :: k -> k -> Type) = Π(a :: k). ∑(b :: k). cat a b
--
--  In words, a flow on a category @fl :: Flow cat@ is a family of
--  arrows in @cat@ such that for each object @a@, there's exactly one
--  arrow starting from @a@ in it.
newtype Flow (cat :: k -> k -> Type) = MkFlow
    { runFlow :: forall a r. Sing k a -> (forall b. Sing k b -> cat a b -> r) -> r }

instance Category cat => Semigroup (Flow cat) where
    MkFlow f1 <> MkFlow f2 = MkFlow \sa k -> f2 sa \sb ab -> f1 sb \sc bc -> k sc (bc . ab)

instance Category cat => Monoid (Flow cat) where
    mempty = MkFlow \sa k -> k sa id

-- | Forgets underlying category from a flow, treating it as a
--   simple function on objects of @cat@.
--
--   Objects of @cat@ are type-level things of kind @k@,
--   so it demotes @k@ to value-level @Val k@.
valMove :: Demote k => Flow (cat :: k -> k -> Type) -> Val k -> Val k
valMove (MkFlow f) valA = toSing valA \singA -> f singA (\singB _catAB -> fromSing singB)

data Ship (cat :: k -> k -> Type) x = Ship { _transition :: Flow cat, _values :: Val k -> x }
    deriving Functor

instance (Category (cat :: k -> k -> Type), Demote k) => Applicative (Ship cat) where
    pure x = Ship mempty (const x)
    (<*>) = ap

instance (Category (cat :: k -> k -> Type), Demote k) => Monad (Ship cat) where
    Ship f1 vx >>= cont = Ship f' vy'
      where
        f' = MkFlow \sa ret ->
                let x = vx (fromSing sa)
                    f2 = _transition (cont x)
                in runFlow (f1 <> f2) sa ret
        vy' v =
            let x = vx v
                vy = _values (cont x)
            in vy $ valMove f1 v

-- | Forgets the underlying category from @Ship cat@, turning it a simple @State (Val k)@.
forgetCategory :: forall k (cat :: k -> k -> Type) x.
    Demote k => Ship cat x -> Val k -> (x, Val k)
forgetCategory (Ship f vx) v = (vx v, valMove f v)

-- | @'Co' ('Poly' cat)@ is isomorphic to @Ship cat@
fromCoPoly :: forall k (cat :: k -> k -> Type) x.
    (Category cat, Demote k) => Co (Poly cat) x -> Ship cat x
fromCoPoly copoly = Ship f vx
  where
    f :: Flow cat
    f = MkFlow $ \sa ret ->
        runCo copoly $ MkPoly sa \sb ab _ -> ret sb ab

    vx :: Val k -> x
    vx valA = toSing valA \singA ->
        runCo copoly $ MkPoly singA \_ _ x -> x

toCoPoly :: forall k (cat :: k -> k -> Type) x.
    (Category cat, Demote k) => Ship cat x -> Co (Poly cat) x
toCoPoly (Ship f vx) = co \(MkPoly sa body) ->
    runFlow f sa \sb ab -> body sb ab (vx (fromSing sa))