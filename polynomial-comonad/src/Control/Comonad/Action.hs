{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DerivingStrategies #-}
module Control.Comonad.Action where

import Control.Comonad

data Acted m a b = Acted a (m -> b)
    deriving stock Functor

instance (Monoid m, RightAction m a) => Comonad (Acted m a) where
    extract (Acted _ f) = f mempty
    duplicate (Acted a f) = Acted a $ \m1 -> Acted (a `act` m1) (f `act` m1)

    {-
    duplicate (duplicate (Acted a f))
     = duplicate $ Acted a $ \m2 -> Acted (a `act` m2) (f `act` m2)
     = Acted a $ \m1 ->
         Acted (a `act` m1) $ (\m2 -> Acted (a `act` m2) (f `act` m2)) `act` m1
     = Acted a $ \m1 ->
         Acted (a `act` m1) $ (\m2 -> Acted (a `act` m2) (f `act` m2)) . (m1 <>)
     = Acted a $ \m1 ->
         Acted (a `act` m1) $ \m2 ->
           Acted (a `act` (m1 <> m2)) (f `act` (m1 <> m2))
    fmap duplicate (duplicate (Acted a f))
     = fmap duplicate $ Acted a $ \m1 -> Acted (a `act` m1) (f `act` m1)
     = Acted a $ \m1 -> duplicate $ Acted (a `act` m1) (f `act` m1)
     = Acted a $ \m1 ->
         Acted (a `act` m1) $ \m2 ->
           Acted ((a `act` m1) `act` m2) ((f `act` m1) `act` m2)
     = Acted a $ \m1 ->
         Acted (a `act` m1) $ \m2 ->
           Acted (a `act` (m1 <> m2)) (f `act` (m1 <> m2))
    -}

-- * RightAction

-- | Right @Semigroup@, @Monoid@, and @Group@ actions.
--   
--   > (x `act` s1) `act` s2 == x `act` (s1 <> s2)
--   
--   If @s@ is @Monoid@ too, additionalty it must satisfy:
--
--   > x `act` mempty == x
--   
--   (Then, if @s@ is @Group@ too, it is automatically a group homomorphism.)
class Semigroup s => RightAction s x where
    act :: x -> s -> x

-- | Free right action
instance Semigroup s => RightAction s (x, s) where
    act (x, s) t = (x, s <> t)

-- | Right action on functions
instance Semigroup s => RightAction s (s -> x) where
    act f s = f . (s <>)

    {-
    
    (f `act` s1) `act` s2
     = f . (s1 <>) . (s2 <>)
     = \s -> f (s1 <> (s2 <> s))
     = \s -> f ((s1 <> s2) <> s)
     = f . ((s1 <> s2) <>)
     = f `act` (s1 <> s2)

    -}

newtype Trivial x = Trivial { getTrivial :: x }
    deriving (Show, Eq)

instance Semigroup s => RightAction s (Trivial x) where
    act x _ = x

newtype Self s = Self { getSelf :: s }
    deriving stock (Show, Eq)
    deriving newtype (Semigroup, Monoid)

instance Semigroup s => RightAction s (Self s) where
    act (Self x) s = Self $ x <> s
