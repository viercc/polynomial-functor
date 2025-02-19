{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.InternalQuiver(
  IQuiver(..),
) where

import Data.Void
import Data.Bifunctor (Bifunctor(..))

-- | Class for Quiver represented by types of edges and vertices
class IQuiver v e | e -> v where
  src :: e -> v
  tgt :: e -> v

-- * Instances

-- | Empty graph
instance IQuiver Void Void where
  src = absurd
  tgt = absurd

-- | A graph with one vertex and one loop on it
instance IQuiver () () where
  src = id
  tgt = id

instance (IQuiver v e, IQuiver w f) => IQuiver (Either v w) (Either e f) where
  src = bimap src src
  tgt = bimap src src

instance (IQuiver v e, IQuiver w f) => IQuiver (v,w) (e,f) where
  src = bimap src src
  tgt = bimap tgt tgt
