{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Data.InternalCategory.PolyComonad(
  Pos(..), Dir(..), identityDir, composeDir,
) where

import Data.Maybe (isJust)

import Control.Comonad

import Data.Type.Equality ((:~:)(..))
import Data.GADT.Compare (GEq(..))
import Data.Functor.Polynomial
import Data.Functor.Polynomial.Class

import Data.InternalCategory (IQuiver(..), ICategory(..))

data Pos f where
  Position :: Tag f a -> Pos f

instance GEq (Tag f) => Eq (Pos f) where
  Position tag == Position tag' = isJust $ geq tag tag'

data Dir f where
  Direction :: Tag f a -> a -> Dir f

domTag :: Dir f -> Pos f
domTag (Direction tag _) = Position tag

codTag :: (Comonad f, Polynomial f, GEq (Tag f)) => Dir f -> Pos f
codTag dir = case toPoly (extendDirection dir) of
  P tag'' _ -> Position tag''

identityDir :: forall f. (Comonad f, Polynomial f) => Pos f -> Dir f
identityDir pos = extract (unfoldPosition pos)

composeDir :: (Comonad f, Polynomial f, GEq (Tag f)) => Dir f -> Dir f -> Maybe (Dir f)
composeDir dir1 (Direction tag2 a2) =
  case toPoly (extendDirection dir1) of
    P tag2' rep -> case geq tag2 tag2' of
      -- Case: cod dir1 == dom dir2
      Just Refl -> Just (rep a2)
      -- Case: cod dir1 /= dom dir2
      Nothing -> Nothing

unfoldPosition :: (Polynomial f) => Pos f -> f (Dir f)
unfoldPosition (Position tag) = fromPoly $ P tag (Direction tag)

extendDirection :: forall f. (Comonad f, Polynomial f, GEq (Tag f)) => Dir f -> f (Dir f)
extendDirection (Direction tag a) = case toPoly (duplicate (unfoldPosition @f (Position tag))) of
  P tag' rep -> case geq tag tag' of
    Nothing -> error "unreachable; duplicate shouldn't change the outer shape"
    Just Refl -> rep a

instance (Comonad f, Polynomial f, GEq (Tag f)) => IQuiver (Pos f) (Dir f) where
  src = domTag
  tgt = codTag

instance (Comonad f, Polynomial f, GEq (Tag f)) => ICategory (Pos f) (Dir f) where
  identity = identityDir
  compose = composeDir