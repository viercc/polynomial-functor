{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE BlockArguments #-}

module DistAct where

import Data.Functor ((<&>))
import Control.Comonad
import Control.Comonad.Store (Store)
import qualified Control.Comonad.Store as Store

import Data.Semigroup.Action
import Control.Comonad.Act

(//) :: (Torsor m x) => x -> x -> m
(//) = difference

infixl 6 //

-- | Data to define distributive law (?)
class Action m x => Q m x where
  -- | Laws:
  --
  -- > (Q1) q x0 x1 mempty = mempty
  -- > (Q2) q x0 x0 m = m
  -- > (Q3) q x0 x1 (n <> m) = q (act m x0) (act m' x1) n <> m'
  --      where m' = q x0 x1 m
  -- > (Q4) q x1 x2 (q x0 x1 m) = q x0 x2 m
  q :: x -> x -> m -> m

-- Comonad-Comonad distributive law natural in w must be (?) of this form
theta :: (Comonad w, Q m x) => w (Act m x r) -> Act m x (w r)
theta wa = Act x0 \m -> wa <&> \(Act x1 h) -> h (q x0 x1 m) 
  where x0 = locate (extract wa)

{-

[Reasons]

We want to represent distributive law

    theta :: forall w r. (Comonad w) => w (Act m x r) -> Act m x (w r)

natural in Comonad w. Firstly, any such natural transformation
without "distributive law" condition is represented by two functions

    t :: x -> x
    p :: x -> x -> m -> Either m m

that is

    theta wa = Act (t x0) \m -> wa <&> \(Act x1 h1) -> either h0 h1 (p x0 x1 m)
      where Act x0 h = extract wa

. (Proof omitted; uses parametricity argument etc.)

The compatibility condition of Comonad-Comonad distributive law

    (DW1) extract . theta = fmap extract :: w (Act m x r) -> w r
    (DW2) fmap extract . theta = extract :: w (Act m x r) -> Act m x r
    (DW3) duplicate . theta = fmap theta . theta . fmap duplicate
            :: w (Act m x r) -> Act m x (Act m x (w r))
    (DW4) fmap duplicate . theta = theta . fmap theta . duplicate
            :: w (Act m x r) -> Act m x (w (w r))

narrows (t,p) down.

Start with the most easiest (DW2).

  DW2LHS
    = fmap extract (theta wa)
    = fmap extract $ Act (t x0) \m -> wa <&> \(Act x1 h1) -> either h0 h1 (p x0 x1 m)
        where Act x0 h0 = extract wa
    = Act (t x0) \m -> extract $ wa <&> \(Act x1 h1) -> either h0 h1 (p x0 x1 m)
    = Act (t x0) \m -> extract wa & \(Act x1 h1) -> either h0 h1 (p x0 x1 m)
    = Act (t x0) \m -> either h0 h0 (p x0 x0 m)

  DW2RHS
    = extract wa
    = Act x0 h0

  Therefore

  - (DW2-pos): t = id
  - (DW2-dir): p x0 x0 m = m

  (x0, h0 can be set arbitrarily.)

Using (DW2-pos), the definition of theta can be simplified.

  (**)
  theta wa = Act x0 \m -> (\(Act x1 h1) -> ) 
    where Act x0 h0 = extract wa

(DW4) is the next easy target.

  DW4LHS
    = fmap duplicate (theta wa)
    = fmap duplicate $ Act x0 \m -> wa <&> \(Act x1 h1) -> either h0 h1 (p x0 x1 m)
        where Act x0 h0 = extract wa
    = Act x0 \m -> duplicate $ wa <&> \(Act x1 h1) -> either h0 h1 (p x0 x1 m)
    = Act x0 \m -> duplicate wa <<&>> \(Act x2 h2) -> either h0 h2 (p x0 x2 m)

  DW4RHS
    = theta (fmap theta (duplicate wa))
    = theta (fmap theta wwa)
        where wwa = duplicate wa
    = Act x0' \m -> fmap theta wwa <&> \(Act x1' h1') ->
        either h0' h1' (p x0' x1' m)
        where
          Act x0' h0'
            = extract (fmap theta wwa)
            = theta (extract wwa)
            = theta wa
            = Act x0 \m -> wa <&> \(Act x1 h1) -> either h0 h1 (p x0 x1 m)
          
          Act x0 h0 = extract wa
    
    = Act x0 \m -> wwa <&> \wa' ->
        let Act x1 h1' = theta wa' 
        in either h0' h1' (p x0 x1 m)

  Comparing both sides,

    duplicate wa <&> \wa' -> wa' <&> \(Act x2 h2) -> ...
      =
    duplicate wa <&> \wa' ->
      let Act x1 h1' = theta wa'
      in either (wa <&> ...) h1' (p x0 x1 m)

  Must hold. Since one can choose a Comonad such that the shape of
  wa and wa' is different (for example Store Bool,), and x0, x1, m is arbitrary,
  (p x0 x1 m) can never be Left. therefore, one can assume

    p x0 x1 m = Right (q x0 x1 m)

  with some (q :: x -> x -> m -> m). It simplifies theta further:

    (***)
    theta wa = Act x0 \m -> wa <&> \(Act x1 h) -> h (q x0 x1 m)
      where x0 = pos (extract wa)

  . By using (***) for the DW4LHS = DW4RHS,

    duplicate wa <&> \wa' -> wa' <&> \(Act x2 h2) -> h2 (q x0 x2 m)
    =
    duplicate wa <&> \wa' ->
      let Act x1 h1' = theta wa'
          x1 = pos (extract wa')
          h1' = wa' <&> \(Act x2 h2) -> h2 (q x1 x2 m)
      in h1' (q x0 x1 m)

  Which can be reduced to

    (DW4-dir) q x0 x2 m = q x1 x2 (q x0 x1 m)

  .

Using simplified theta definition given as (***),
(DW1) is transformed as below.

  DW1LHS
    = extract (theta wa)
    = extract $ Act x0 \m -> wa <&> \(Act x1 h) -> h (q x0 x1 m)
        where x0 = pos (extract wa)
    = wa <&> \(Act x1 h) -> h (q x0 x1 mempty)
    
  DW1RHS
    = fmap extract wa
    = wa <&> \(Act x1 h) -> h mempty

  Therefore

    (DW1-dir) q x0 x1 mempty = mempty

  .

Finally, (DW3).

  DW3LHS
    = duplicate (theta wa)
    = duplicate $ Act x0 \m -> wa <&> \(Act x1 h) -> h (q x0 x1 m)
        where x0 = pos (extract wa)
    = Act x0 \m -> Act (act m x0) \n -> <&> \(Act x1 h) ->
        h (q x0 x1 (n <> m))

  DW3RHS
    = fmap theta (theta (fmap duplicate wa))
    = fmap theta $ theta waa
        where waa = fmap duplicate wa
    = fmap theta $ Act x0' \m -> waa <&> \(Act x1' h') ->
        h' (q x0' x1' m)
        where x0' = pos (extract waa)
                  = pos (extract (fmap duplicate wa))
                  = pos (duplicate (extract wa))
                  = ... = x0
    = fmap theta $ Act x0 \m -> wa <&> \(Act x1 h) ->
        let Act x1' h' = duplicate (Act x1 h)
        in h' (q x0 x1' m)
    = fmap theta $ Act x0 \m -> wa <&> \(Act x1 h) ->
        let m' = q x0 x1 m
        in Act (act m' x1) \n -> h (n <> m')
    = Act x0 \m ->
        let shifter (Act x1 h) =
              let m' = q x0 x1 m
              in Act (act m' x1) \n -> h (n <> m')
        in theta $ wa <&> shifter
    = Act x0 \m ->
        let shifter (Act x1 h) =
              let m' = q x0 x1 m
              in Act (act m' x1) \n -> h (n <> m')
            x1' = pos (extract (wa <&> shifter))
                = pos (shifter (extract wa))
                = pos $ shifter (Act x0 _)
                = let m' = q x0 x0 m
                  in act m' x0
                = act m x0
        in Act x1' \n -> wa <&> shifter <&> \(Act x2' h2) ->
            h2 (q x1' x2' n)
    = Act x0 \m ->
        let x1' = act m x0
        in Act x1' \n -> wa <&> \(Act x1 h) ->
              let m' = q x0 x1 m
                  x2' = act m' x1
                  h2 n = h (n <> m')
              in h2 (q x1' x2' n)
    = Act x0 \m ->
        Act (act m x0) \n -> wa <&> \(Act x1 h) ->
          let m' = q x0 x1 m
          in h (q (act m x0) (act m' x1) n <> m')

  Comparing both sides

    (DW3-dir)
    q x0 x1 (n <> m) = q (act m x0) (act m' x1) n <> m'
      where m' = q x0 x1 m

-}

-- Utility

(<<&>>) :: Functor f => f (f a) -> (a -> b) -> f (f b)
ffa <<&>> g = fmap (fmap g) ffa


{-

When (Action m x) is actually a torsor
(m is group and its action is regular (= free and transitive)),
(Act m x) is isomorphic to the Store comonad over the state type x.

-}

-- | When the action is @'Torsor' g x@, there is a comonad isomorphism to @Store x@
toStore :: Torsor g x => Act g x a -> Store x a
toStore (Act x0 f) = Store.store (\x1 -> f (x1 // x0)) x0

-- | Comonad morphism from @Store x@. It is the inverse of 'toStore' if the action on @x@ is
-- @Torsor@.
fromStore :: Action g x => Store x a -> Act g x a
fromStore sa = Act x0 (\g' -> f (act g' x0))
  where
    x0 = Store.pos sa
    f x1 = Store.peek x1 sa

{-

For such case, q can alternatively be represented using

  q' :: x -> x -> x -> x

where two representations are bijectively related:

  q' x x0 x1 = q x0 x1 (x // x0) `act` x1
  q x0 x1 m = q' (act m x0) x0 x1 // x1

(this being bijection follows from Torsor properties).

Translating (Q1)-(Q4) in terms of q' gets us (Q1')-(Q4')

(Q1') q' x0 x0 x1 = x1
(Q2') q' x x0 x0 = x
(Q3') q' y x0 x1 = q' y x (q' x x0 x1)
(Q4') q' (q' x x0 x1) x1 x2 = q' x x0 x2

[proof]

  (Q1')
    q x0 x1 mempty
    = q' (act mempty x0) x0 x1 // x1
    = q' x0 x0 x1 // x1
    = mempty

    ∴ q' x0 x0 x1 = x1

  (Q2')
    q x0 x0 m
    = q' (act m x0) x0 x0 // x0
    = m
    
    ∴ q' x x0 x0 = x

  (Q3')

    Let x = act m x0
        y = act n x
    
    -- m = x // x0
    -- n = y // x

    let m' = q x0 x1 m
          = q' x x0 x1 // x1
    let q' x x0 x1 = x'
    
    -- m' = x' // x1

    q x0 x1 (n <> m)
    = q' (act (n <> m) x0) x0 x1 // x1
    = q' (act n (act m x0)) x0 x1 // x1
    = q' y x0 x1 // x1
    
    q (act m x0) (act m' x1) n <> m'
    = q (act (x // x0) x0) (act (x' // x1) x1) (y // x) <> (x' // x1)
    = q x x' (y // x) <> (x' // x1)
    = (q' (act (y // x) x) x x' // x') <> (x' // x1)
    = q' y x x' // x1
    = q' y x (q' x x0 x1) // x1
    
    ∴ q' y x0 x1 = q' y x (q' x x0 x1)

  (Q4')

    Let x = act m x0
    -- m = x // x0

    q x1 x2 (q x0 x1 m)
    = q x1 x2 (q' x x0 x1 // x1)
    = q' ((q' x x0 x1 // x1) `act` x1) x1 x2 // x2
    = q' (q' x x0 x1) x1 x2 // x2
    q x0 x2 m
    = q' x x0 x2 // x2

    ∴ q' (q' x x0 x1) x1 x2 = q' x x0 x2

(Q1')-(Q4') makes (X,q') an algebraic structure called heap, and it is
known that heap is a Torsor minus the "identity of group acting it".
(note that this heap **need not be** the Torsor which gave the Act comonad structure,
but another, unrelated Torsor which shares the set acted upon.)

This is the classifying data of "Store comonad distributive law natural in w."

-}
