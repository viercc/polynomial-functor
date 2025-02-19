{-# LANGUAGE DerivingStrategies #-}
module Data.InternalCategory.Discrete where

import Data.InternalCategory
    ( IQuiver(..), ICategory(..), Path(Path) )

newtype IDiscrete a = IDiscrete a
    deriving stock (Show, Read)
    deriving newtype (Eq, Ord, Enum, Bounded)

instance IQuiver a (IDiscrete a) where
  src (IDiscrete x) = x
  tgt (IDiscrete x) = x

instance Eq a => ICategory a (IDiscrete a) where
  foldPath (Path x _ _) = IDiscrete x
