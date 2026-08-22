{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}

module DistPoly where

import Prelude hiding (id, (.))

import Data.Functor ((<&>))
import Control.Comonad
import Control.Comonad.Store (Store)
import qualified Control.Comonad.Store as Store

import Control.Comonad.Travel
import Data.Bool (bool)
import Data.Kind
import Control.Category (Category(..))
import Data.Singletons
import Data.Singletons.Sigma
import Data.Type.Equality (type (:~:) (..))
import Data.Singletons.Decide (SDecide(..), Decision (..))
import Data.Semigroup.Action
import Control.Comonad.Act

type Dist w v = forall r. w (v r) -> v (w r)

type Dir (cat :: k -> k -> Type) (a :: k) = Sigma k (TyCon (cat a))

-- | Data to define right natural distributive law
class Category cat => Q (cat :: k -> k -> Type) where
  -- | Laws:
  --
  -- > (Q1) q x y (x :&: id) = y :&: id
  -- > (Q2) q x x dir = dir
  -- > (Q3) q x y (x'' :&: (g . f)) = (y'' :&: (qg . qf))
  --      forall
  --        f :: cat x x'
  --        g :: cat x' x''
  --      where
  --        (y' :&: qf) = q x y (x' :&: f)
  --        (y'' :&: qg) = q x' y' (x'' :&: g)
  -- > (Q4) q y z (q x y dir) = q x z dir
  q :: Sing a -> Sing b -> Dir cat a -> Dir cat b


{-

Q represents "translation of morphism by their origin"

   x   y
   | q |
f  | ↦ | qf
   v   v
   x'  y'

Laws, schematically

(Q1)

   x   y
   | q |
id | ↦ | id
   v   v
   x   y

(Q2)

   x   x
   | q |
 f | ↦ | f
   v   v
   x'  x'

(Q3)

   x   y
   | q |
 f | ↦ |
   v   v
  x'  y'
   | q | 
 g | ↦ | 
   v   v 
  x'' y''

  ===

     x   y
     | q |
 g.f | ↦ |
     |   | 
     v   v 
    x'' y''

(Q4)

   x   y   z
   | q | q |
 f | ↦ | ↦ | 
   v   v   v
   x'  y'  z'

   ===

   x   z
   | q |
f  | ↦ |
   v   v
   x'  z'

-}

theta :: (Comonad w, Q cat) => Dist w (Travel cat)
theta wa = case extract wa of
  MkTravel x0 _ ->
    MkTravel x0 \m -> wa <&> \(MkTravel x1 h) -> h (q x0 x1 m) 

extractQ :: forall k (cat :: k -> k -> Type).
     (Category cat, SDecide k)
  => (forall w. (Comonad w) => Dist w (Travel cat))
  -> (forall a b. Sing a -> Sing b -> Dir cat a -> Dir cat b)
extractQ dist @_ @b x0 x1 dir = case dist sv of
  MkTravel x0' f -> case x0 %~ x0' of
    Proved Refl -> case Store.peek True (f dir) of
      Just dir' -> dir'
      Nothing -> error "Unlawful distributive law"
    Disproved _ -> error "Unlawful distributive law"
  where
    a0 :: Travel cat (Maybe (Dir cat b))
    a0 = MkTravel x0 (const Nothing)

    a1 :: Travel cat (Maybe (Dir cat b))
    a1 = MkTravel x1 Just

    sv :: Store Bool (Travel cat (Maybe (Dir cat b)))
    sv = Store.store (bool a0 a1) False

{-

We want to represent distributive law

    theta :: forall w. Comonad w => Dist w (Travel cat)
    theta :: forall w r. (Comonad w) => w (Travel cat r) -> Travel cat (w r)

natural in Comonad w. Firstly, any such natural transformation
without "distributive law" condition is represented by two functions

    T :: k -> k
    (singT :: Sing a -> Sing (T a))
    p :: Sing a -> Sing b -> Dir cat (T a) -> Either (Dir cat a) (Dir cat b)

that is

    theta wa = case extract wa of
      MkTravel x0 h0 -> MkTravel (singT x0) $
        \dir -> wa <&> \(MkTravel x1 h1) -> either h0 h1 (p x0 x1 dir)

. (Proof omitted; uses parametricity argument etc.)

The compatibility condition of Comonad-Comonad distributive law

    (DW1) extract . theta = fmap extract :: w (Travel cat r) -> w r
    (DW2) fmap extract . theta = extract :: w (Travel cat r) -> Travel cat r
    (DW3) duplicate . theta = fmap theta . theta . fmap duplicate
            :: w (Travel cat r) -> Travel cat (Travel cat (w r))
    (DW4) fmap duplicate . theta = theta . fmap theta . duplicate
            :: w (Travel cat r) -> Travel cat (w (w r))

narrows (t,p) down.

Start with the most easiest (DW2).

  DW2LHS
    = fmap extract (theta wa)
    = fmap extract $ MkTravel (singT x) \dir ->
          wa <&> \(MkTravel y h1) -> either h0 h1 (p x y dir)
        where MkTravel x h0 = extract wa
    = MkTravel (singT x) \dir -> extract $ wa <&> \(MkTravel y h1) -> either h0 h1 (p x y dir)
    = MkTravel (singT x) \dir -> extract wa & \(MkTravel y h1) -> either h0 h1 (p x y dir)
    = MkTravel (singT x) \dir -> either h0 h0 (p x x dir)

  DW2RHS
    = extract wa
    = MkTravel x h0

  Therefore

  - (DW2-pos): singT x = x; T = id
  - (DW2-dir): p x x dir = dir

  (x, h0 are arbitrary.)

  The type of p simplifies too.

  p :: Sing a -> Sing b -> Dir cat a -> Either (Dir cat a) (Dir cat b)

Using (DW2-pos), the definition of theta can be simplified.

  (**)
  theta wa = case extract wa of
    MkTravel x h0 -> MkTravel x $
      \dir -> wa <&> \(MkTravel y h1) -> either h0 h1 (p x y dir)

(DW4) is the next easy target.

  DW4LHS
    = fmap duplicate (theta wa)
    = fmap duplicate $ MkTravel x \dir -> wa <&> \(MkTravel y h1) -> either h0 h1 (p x y dir)
        where MkTravel x h0 = extract wa
    = MkTravel x \dir -> duplicate $ wa <&> \(MkTravel y h1) -> either h0 h1 (p x y dir)
    = MkTravel x \dir -> duplicate wa <<&>> \(MkTravel z h2) -> either h0 h2 (p x z dir)

  DW4RHS
    = theta (fmap theta (duplicate wa))
    = theta (fmap theta wwa)
        where wwa = duplicate wa
    = MkTravel x' \dir -> fmap theta wwa <&> \(MkTravel y' h1') ->
        either h0' h1' (p x' y' dir)
        where
          MkTravel x' h0'
            = extract (fmap theta wwa)
            = theta (extract wwa)
            = theta wa
            = MkTravel x \dir -> wa <&> \(MkTravel y h1) -> either h0 h1 (p x y dir)
          
          MkTravel x h0 = extract wa
    = MkTravel x \dir -> fmap theta wwa <&> \(MkTravel y' h1') ->
        either h0' h1' (p x y' dir)
        where
          MkTravel x h0 = extract wa
          h0' = \dir -> wa <&> \(MkTravel y h1) -> either h0 h1 (p x y dir)
    
    = MkTravel x \dir -> wwa <&> \wa' ->
        let MkTravel y h1' = theta wa' 
        in either h0' h1' (p x y dir)

  Comparing both sides,

    duplicate wa <&> \wa' -> wa' <&> \(MkTravel z h2) -> ...
      =
    duplicate wa <&> \wa' ->
      let MkTravel y h1' = theta wa'
      in either h0' h1' (p x y dir)
      =
    duplicate wa <&> \wa' ->
      let MkTravel y h1' = theta wa'
      in either (\dir' -> wa <&> ...) h1' (p x y dir)

  Must hold. Since one can choose a Comonad such that the shape of
  wa and wa' is different (for example Store Bool,), and (x, y, dir)
  is arbitrary,
  (p x y dir) can never be Left. therefore, one can assume

    p x y dir = Right (q x y dir)

  with some (q :: Sing a -> Sing b -> Dir cat a -> Dir cat b).
  It simplifies theta further:

    (***)
    theta wa = MkTravel x \dir -> wa <&> \(MkTravel y h) -> h (q x y dir)
      where MkTravel x _ = extract wa

  . By using (***) for the DW4LHS = DW4RHS,

    duplicate wa <&> \wa' -> wa' <&> \(MkTravel z h2) -> h2 (q x z dir)
    =
    duplicate wa <&> \wa' ->
      let MkTravel y h1' = theta wa'
            = let MkTravel y _ = extract wa'
              in MkTravel y \dir' -> wa' <&> \(MkTravel z h2)
                -> h2 (q y z dir')
      in h1' (q x y dir)=
    duplicate wa <&> \wa' ->
      let MkTravel y _ = extract wa'
              in MkTravel y \dir' -> wa' <&> \(MkTravel z h2)
                -> h2 (q y z dir')
      in wa' <&> \(MkTravel z h2) -> h2 (q y z (q x y dir))

  Which can be reduced to

    (DW4-dir) q x z dir = q y z (q x y dir)

  .

Using simplified theta definition given as (***),
(DW1) is transformed as below.

  DW1LHS
    = extract (theta wa)
    = extract $ MkTravel x \dir -> wa <&> \(MkTravel y h) -> h (q x y dir)
        where MkTravle x _ = extract wa
    = wa <&> \(MkTravel y h) -> h (q x y (x :&: id))
    
  DW1RHS
    = fmap extract wa
    = wa <&> \(MkTravel y h) -> h (y :&: id)

  Therefore

    (DW1-dir) q x y (x :&: id) = y :&: id

  .

Finally, (DW3).

  DW3LHS
    = duplicate (theta wa)
    = duplicate $ MkTravel x \dir -> wa <&> \(MkTravel y h) -> h (q x y dir)
        where MkTravle x _ = extract wa
    = MkTravel x \(x' :&: f) ->
        MkTravel x' \(x'' :&: g) ->
          wa <&> \(MkTravel y h) ->
            h (q x y (x'' :&: (g . f)))

  DW3RHS
    = fmap theta (theta (fmap duplicate wa))
    = fmap theta $ theta waa
        where waa = fmap duplicate wa
    = fmap theta $ MkTravel xx \dir -> waa <&> \(MkTravel yy h') ->
        h' (q xx yy dir)
        where MKTravel xx _ = extract waa
                 = extract (fmap duplicate wa)
                 = duplicate (extract wa)
                 = ...
                 = MkTravel x _
              MkTravel x _ = extract wa
    
    = fmap theta $ MkTravel x \dir -> wa <&> \(MkTravel y h) ->
        let MkTravel yy h' = duplicate (MkTravel y h)
        in h' (q x yy dir)
    
    = fmap theta $ MkTravel x \dir -> wa <&> \(MkTravel y h) ->
        let MkTravel yy h' = MkTravel y \(y' :&: qf) -> MkTravel y' \(y'' :&: qg) ->
              h (y'' :&: (qg . qf))
        in h' (q x yy dir)
    = fmap theta $ MkTravel x \dir -> wa <&> \(MkTravel y h) ->
        let (y' :&: qf) = q x y dir
        in MkTravel y' \(y'' :&: qg) -> h (y'' :&: (qg . qf))
    = fmap theta $ MkTravel x \dir ->
        let shifter (MkTravel y h) =
              let (y' :&: qf) = q x y dir
              in MkTravel y' \(y'' :&: qg) -> h (y'' :&: (qg . qf))
        in wa <&> shifter
    
    = MkTravel x \dir -> theta (wa <&> shifter)
    = MkTravel x \dir ->
        let MkTravel x_sh _ = extract (wa <&> shifter)
             = shifter (extract wa)
             = shifter (MkTravel x _)
             = let (y' :&: qf) = q x x dir
               in MkTravel y' _
             = let (x' :&: f) = dir
               in MkTravel x' _
        in MkTravel x_sh \dir' -> wa <&> \(MkTravel y h) ->
            let MkTravel y_sh h_sh = shifter (MkTravel y h)
            in h_sh (q x_sh y_sh dir')
    
    = MkTravel x \(x' :&: f) ->
        MkTravel x' \dir' -> wa <&> \(MkTravel y h) ->
          let MkTravel y_sh h_sh = shifter (MkTravel y h)
                = let (y' :&: qf) = q x y (x' :&: f)
                  in MkTravel y' \(y'' :&: qg) -> h (y'' :&: qg . qf)
          in h_sh (q x' y_sh dir')
  
    = MkTravel x \(x' :&: f) ->
        MkTravel x' \dir' -> wa <&> \(MkTravel y h) ->
          let (y' :&: qf) = q x y (x' :&: f)
              (y'' :&: qg) = q x' y' dir'
                  in MkTravel y' \(y'' :&: qg) -> h (y'' :&: qg . qf)
          in h (y'' :&: qg . qf)

  Comparing both sides,

    (DW3-dir)
    q x y (x'' :&: g . f) = y'' :&: qg . qf
      where (y' :&: qf) = q x y (x' :&: f)
            (y'' :&: qg) = q x' y' (x'' :&: g)

-}

-- Utility

(<<&>>) :: Functor f => f (f a) -> (a -> b) -> f (f b)
ffa <<&>> g = fmap (fmap g) ffa

-- * @Q cat@ implies cat is isomorphic to action category

data Mor cat where
  Mor :: Sing x -> Sing x' -> cat x x' -> Mor cat
  MorId :: Mor cat

  {-
  `MorId` represent equivalence class of
  identity element of the monoid (which should exist if `k` is
  inhabited). This is needed because "`k` is inhabited" is somewhat
  tricky to represent as constraint, especially without making arbitrary choice
  for `x0 :: k`.

  This monoid does not depend on the chocie of `x0`, thus it is more natural
  to avoid arbitrary choice to begin with.
  -}

-- | Externally, @Mor cat@ must be abstract type which can only be
--   accessed through @mor@, @morAt@
mor :: Sing x -> Sing x' -> cat x x' -> Mor cat
mor = Mor

morAt :: Q cat => Mor cat -> Sing x -> Dir cat x
morAt MorId x = q x x (x :&: id)
morAt (Mor y y' f) x = q y x (y' :&: f)

instance (Q cat, SDecide k, forall z z'. Eq (cat z z')) => Eq (Mor (cat :: k -> k -> Type)) where
  MorId == MorId = True
  MorId == Mor x x' f = Mor x x id == Mor x x' f
  Mor x x' f == MorId = Mor x x' f == Mor x x id
  Mor x x' f == Mor y y' g =
    case q x y (x' :&: f) of
      (qx' :&: qf) -> case qx' %~ y' of
        Proved Refl -> qf == g
        Disproved _ -> False

{-

(==) is an (indicator function of an) equivalence relation. Note that

  (Mor x x' f == Mor y y' g) = True

iff

  q x y (x' :&: f) = (y' :&: g)

.

[Reflexivity]:

  (Mor x x' f == Mor x x' f) = True) ⇔ q x x (x' :&: f) = (x' :&: f)
  and it is immediate by (Q2).

[Symmetry]

  Suppose (Mor x x' f == Mor y y' g) i.e.

    q x y (x' :&: f) = (y' :&: g)
  
  . Then

    q y x (y' :&: g) = q y x (q x y (x' :&: f)) = q x x (x' :&: f) = (x' :&: f)
  
  .

[Transitivity]

  Suppose (Mor x x' f == Mor y y' g) && (Mor y y' g == Mor z z' h).
  Then

  q x z (x' :&: f)
     -- (Q4)
   = q y z (q x y (x' :&: f))
     -- (assumption)
   = q y z (y' :&: g)
     -- (assumption)
   = (z' :&: h)

-}

instance (Q cat) => Semigroup (Mor cat) where
  --  x -- [ g <> f ] --> qy
  --
  --   ===
  --
  --  x --[f]--> x' --[qg]--> qy'
  --                   ↑
  --                   ↑ q
  --                   ↑
  --              y --[g]--> y'
  MorId <> m = m
  m <> MorId = m
  Mor y y' g <> Mor x x' f =
    case q y x' (y' :&: g) of
      (qy :&: qg) -> Mor x qy (qg . f)


  -- Associativity is evident from diagrams

instance (Q cat) => Monoid (Mor cat) where
  mempty = MorId

{-

Monoid instance is well-defined w.r.t. (==).

Suppose

(Mor x1 x1' f1 == Mor x2 x2' f2)
(Mor y1 y1' g1 == Mor y2 y2' g2)

Then

Mor z1 z1' h1 = Mor y1 y1' g1 <> Mor x1 x1' f1
 = Mor x1 qy1 (qg1 . f1) where (qy1 :&: qg1) = q y1 x1' (y1' :&: g1)

Mor z2 z2' h2 = Mor y2 y2' g2 <> Mor x2 x2' f2
 = Mor x2 qy2 (qg2 . f2) where (qy2 :&: qg2) = q y2 x2' (y2' :&: g2)

(Mor z1 z1' h1 == Mor z2 z2' h2)
 ⇔ q z1 z2 (z1' :&: h1) = (z2' :&: h2)

q z1 z2 (z1' :&: h1)
 = q x1 x2 (qy1 :&: (qg1 . f1))
 -- (Q3)
 = let (qx1' :&: qf1)
          = q x1 x2 (x1' :&: f1)
          = (x2' :&: f2) -- By property of (==)
       (qqy1 :&: qqg1) = q x1' qx1' (qy1 :&: qg1)
          = q x1' qx1' (q y1 x1' (y1' :&: g1))
            -- (Q4)
          = q y1 qx1' (y1' :&: g1)
   in (qqy1 :&: (qqg1 . qf1))
 = let (qqy1 :&: qqg1) = q y1 x2' (y1' :&: g1)
          = q y2 x2' (q y1 y2 (y1' :&: g1))
            -- By property of (==)
          = q y2 x2' (y2' :&: g2)
   in (qqy1 :&: (qqg1 . qf1))
 = (z2' :&: h2)

-}

data X (cat :: k -> k -> Type) where
  X :: Sing (a :: k) -> X (cat :: k -> k -> Type)

instance (Q cat) => Action (Mor cat) (X cat) where
  act MorId x = x
  act (Mor y y' f) (X x) = case q y x (y' :&: f) of
    (x' :&: _) -> X x'

  {-
  
  y --[f]-> y'
      ↓ q
  x ------> act (Mor y y' f) x
  
  -}

{-

Laws check:

           z  --[g]---> z'
                 ↓q
y --[f]--> y' --[qg]--> qz'
           ↓∘
y --------------------> qz'
           ↓q
x --------------------> act (Mor z z' g <> Mor y y' f) x

========================================

let x' = Act (Mor y y' f) x
    x'' = Act (Mor z z' g) x'

           z  --[g]---> z'
                 ↓q
y --[f]--> y' --[qg]--> qz'
    ↓q          ↓q
x -------> x' --------> x''

-}

travelToAct :: Q cat => Travel cat r -> Act (Mor cat) (X cat) r
travelToAct (MkTravel x k) = Act (X x) (\m -> k $ morAt m x)