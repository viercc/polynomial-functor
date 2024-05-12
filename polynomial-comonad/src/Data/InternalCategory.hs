{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.InternalCategory(
  -- * Internal categories
  ICategory(..),
  dom, cod,
  identity, compose,

  -- * Reexport
  IQuiver(..),
  Path(..),
) where

import Data.InternalQuiver
import Data.Void

class IQuiver ob mor => ICategory ob mor | mor -> ob where
  foldPath :: Path ob mor -> mor

dom, cod :: ICategory ob mor => mor -> ob
dom = src
cod = tgt

identity :: ICategory ob mor => ob -> mor
identity = foldPath . emptyPath

compose :: (Eq ob, ICategory ob mor) => mor -> mor -> Maybe mor
compose f g = foldPath <$> (singlePath f >?> singlePath g)

-- * Instances

-- | @Path@ is the free category
instance ICategory ob (Path ob mor) where
  foldPath = concatPath

-- | Empty graph
instance ICategory Void Void where
  foldPath (Path v _ _) = absurd v

-- | A graph with one vertex and one loop on it
instance ICategory () () where
  foldPath _ = ()

instance (ICategory v e, ICategory w f) => ICategory (Either v w) (Either e f) where
  foldPath p = case separateSumPath p of
    Left leftP   -> Left (foldPath leftP)
    Right rightP -> Right (foldPath rightP)

instance (ICategory v e, ICategory w f) => ICategory (v,w) (e,f) where
  foldPath p = (foldPath (fstPath p), foldPath (sndPath p))