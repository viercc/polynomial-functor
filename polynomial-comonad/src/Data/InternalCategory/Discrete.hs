{-# LANGUAGE DerivingStrategies #-}
module Data.InternalCategory.Discrete where

import Data.InternalQuiver
import Data.InternalCategory

newtype IDiscrete a = IDiscrete a
    deriving stock (Show, Read)
    deriving newtype (Eq, Ord, Enum, Bounded)

instance IQuiver a (IDiscrete a) where
  src (IDiscrete x) = x
  tgt (IDiscrete x) = x

instance ICategory a (IDiscrete a) where
  foldPath (Path x _ _) = IDiscrete x
