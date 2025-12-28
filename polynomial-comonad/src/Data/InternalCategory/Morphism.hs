{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Data.InternalCategory.Morphism(
  Mor(..), identityMorphism, composeMorphism
) where

import Prelude hiding ((.), id)
import qualified Data.List
import Data.Maybe (fromMaybe)
import Control.Category

import Data.Singletons
import Data.Singletons.Decide
import Data.InternalCategory
    ( IQuiver(..), ICategory(..), Path(Path) )
import Data.Kind (Type)

-- | Sum of all morphisms in @cat@.
data Mor k (cat :: k -> k -> Type) where
  Morphism :: Sing a -> Sing b -> cat a b -> Mor k cat

data SOb k where
  SOb :: Sing (a :: k) -> SOb k

instance SDecide k => Eq (SOb k) where
  SOb sa == SOb sb = case sa %~ sb of
    Proved _ -> True
    Disproved _ -> False

instance IQuiver (SOb k) (Mor k cat) where
  src (Morphism sa _ _) = SOb sa
  tgt (Morphism _ sb _) = SOb sb

identityMorphism :: (Category cat) => SOb k -> Mor k cat
identityMorphism (SOb sa) = Morphism sa sa id

composeMorphism :: (Category cat, SDecide k) => Mor k cat -> Mor k cat -> Maybe (Mor k cat)
composeMorphism (Morphism sa sb f) (Morphism sb' sc g) = case sb %~ sb' of
  Proved Refl -> Just $ Morphism sa sc (g . f)
  Disproved _ -> Nothing

composeMorphism' :: (Category cat, SDecide k) => Mor k cat -> Mor k cat -> Mor k cat
composeMorphism' f g = fromMaybe (error "Invalid Path") $ composeMorphism f g

instance (Category cat, SDecide k) => ICategory (SOb k) (Mor k cat) where
  foldPath (Path s0 mors _) = Data.List.foldl' composeMorphism' (identityMorphism s0) mors 