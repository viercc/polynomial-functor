{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
module Control.Category.OneObject where

import Prelude hiding (id, (.))
import Control.Category

newtype OneObject m (a :: ()) (b :: ()) = OneObject m
    deriving stock (Show)
    deriving newtype (Eq, Ord, Semigroup, Monoid)

instance Monoid m => Category (OneObject m) where
    id = OneObject mempty
    OneObject m1 . OneObject m2 = OneObject (m1 <> m2)
