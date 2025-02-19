{-# LANGUAGE DerivingStrategies #-}
module Data.InternalCategory.Indiscrete where

import Data.InternalCategory
    ( IQuiver(..), ICategory(..), Path(Path) )

data IIndiscrete a = IIndiscrete a a
    deriving stock (Eq, Ord, Show, Read)

instance IQuiver a (IIndiscrete a) where
  src (IIndiscrete x _) = x
  tgt (IIndiscrete _ y) = y

instance Eq a => ICategory a (IIndiscrete a) where
  foldPath (Path x _ y) = IIndiscrete x y
