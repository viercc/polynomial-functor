{-# LANGUAGE DerivingStrategies #-}
module Data.InternalCategory.Clique where

import Data.InternalQuiver
import Data.InternalCategory

data IClique a = IClique a a
    deriving stock (Eq, Ord, Show, Read)

instance IQuiver a (IClique a) where
  src (IClique x _) = x
  tgt (IClique _ y) = y

instance ICategory a (IClique a) where
  foldPath (Path x _ y) = IClique x y
