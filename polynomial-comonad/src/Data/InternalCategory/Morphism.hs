{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.InternalCategory.Morphism(
  Mor(..),
) where

import Prelude hiding ((.), id)
import Control.Category ( Category(..) )

import Data.Singletons
import Data.Singletons.Decide
import Data.InternalCategory
    ( IQuiver(..), ICategory(..) )
import Data.Kind (Type)
import Data.Singletons.ShowSing ( ShowSing )

-- | Sum of all morphisms in @cat@.
data Mor k (cat :: k -> k -> Type) where
  Morphism :: Sing a -> Sing b -> cat a b -> Mor k cat

-- | Objects in @cat@.
data Ob k where
  Ob :: !(Sing (a :: k)) -> Ob k

deriving instance ShowSing k => Show (Ob k)
instance SDecide k => Eq (Ob k) where
  Ob x == Ob y = case x %~ y of
    Proved _ -> True
    Disproved _ -> False

instance IQuiver (Ob k) (Mor k cat) where
  src (Morphism sa _ _) = Ob sa
  tgt (Morphism _ sb _) = Ob sb

instance (Category cat, SDecide k) => ICategory (Ob k) (Mor k cat) where
  identity (Ob sa) = Morphism sa sa id
  compose (Morphism sa sb f) (Morphism sb' sc g) = case sb %~ sb' of
    Proved Refl -> Just $ Morphism sa sc (g . f)
    Disproved _ -> Nothing