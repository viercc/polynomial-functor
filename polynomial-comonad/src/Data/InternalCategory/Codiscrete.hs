{-# LANGUAGE DerivingStrategies #-}
module Data.InternalCategory.Codiscrete where

import Data.InternalCategory
    ( IQuiver(..), ICategory(..), Path(Path) )

data Codisc a = Codisc a a
    deriving stock (Eq, Ord, Show, Read)

instance IQuiver a (Codisc a) where
  src (Codisc x _) = x
  tgt (Codisc _ y) = y

instance Eq a => ICategory a (Codisc a) where
  foldPath (Path x _ y) = Codisc x y
