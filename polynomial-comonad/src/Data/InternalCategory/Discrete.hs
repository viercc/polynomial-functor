{-# LANGUAGE DerivingStrategies #-}
module Data.InternalCategory.Discrete where

import Data.InternalCategory
    ( IQuiver(..), ICategory(..), Path(Path) )

newtype Disc a = Disc a
    deriving stock (Show, Read)
    deriving newtype (Eq, Ord, Enum, Bounded)

instance IQuiver a (Disc a) where
  src (Disc x) = x
  tgt (Disc x) = x

instance Eq a => ICategory a (Disc a) where
  foldPath (Path x _ _) = Disc x
