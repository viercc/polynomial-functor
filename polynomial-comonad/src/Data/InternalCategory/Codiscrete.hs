{-# LANGUAGE DerivingStrategies #-}

module Data.InternalCategory.Codiscrete where

import Data.InternalCategory
  ( ICategory (..),
    IQuiver (..),
    Path (Path),
  )

data Codisc a = Codisc a a
  deriving stock (Eq, Ord, Show, Read)

instance IQuiver a (Codisc a) where
  src (Codisc x _) = x
  tgt (Codisc _ y) = y

instance (Eq a) => ICategory a (Codisc a) where
  identity x = Codisc x x
  compose (Codisc x y) (Codisc y' z)
    | y == y'   = Just $ Codisc x z
    | otherwise = Nothing
  foldPath (Path x _ y) = Codisc x y
