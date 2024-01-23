{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module Control.Category.Indiscrete where

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Type)

type Indiscrete :: k -> k -> Type
data Indiscrete (a :: k) (b :: k) = Indiscrete
    deriving (Show, Eq)

instance Category Indiscrete where
    id = Indiscrete
    _ . _ = Indiscrete
