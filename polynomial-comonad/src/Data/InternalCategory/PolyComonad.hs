{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Data.InternalCategory.PolyComonad(
  Direction(..)
) where

import Data.List (foldl')
import Data.Maybe (isJust)

import Control.Comonad

import Data.Type.Equality ((:~:)(..))
import Data.GADT.Compare (GEq(..))
import Data.Functor.Polynomial
import Data.Functor.Polynomial.Class

import Data.InternalCategory

data Position f where
  Pos :: Tag f a -> Position f

instance GEq (Tag f) => Eq (Position f) where
  Pos tag == Pos tag' = isJust $ geq tag tag'

data Direction f where
  Dir :: Tag f a -> a -> Direction f

domTag :: Direction f -> Position f
domTag (Dir tag _) = Pos tag

codTag :: (Comonad f, Polynomial f, GEq (Tag f)) => Direction f -> Position f
codTag dir = case toPoly (extendDir dir) of
  P tag'' _ -> Pos tag''

identityDir :: forall f. (Comonad f, Polynomial f) => Position f -> Direction f
identityDir pos = extract (unfoldPos pos)

composeDir :: (Comonad f, Polynomial f, GEq (Tag f)) => Direction f -> Direction f -> Maybe (Direction f)
composeDir dir1 (Dir tag2 a2) =
  case toPoly (extendDir dir1) of
    P tag2' rep -> case geq tag2 tag2' of
      -- Case: cod dir1 == dom dir2
      Just Refl -> Just (rep a2)
      -- Case: cod dir1 /= dom dir2
      Nothing -> Nothing

unfoldPos :: (Polynomial f) => Position f -> f (Direction f)
unfoldPos (Pos tag) = fromPoly $ P tag (Dir tag)

extendDir :: forall f. (Comonad f, Polynomial f, GEq (Tag f)) => Direction f -> f (Direction f)
extendDir (Dir tag a) = case toPoly (duplicate (unfoldPos @f (Pos tag))) of
  P tag' rep -> case geq tag tag' of
    Nothing -> error "unreachable; duplicate shouldn't change the outer shape"
    Just Refl -> rep a

instance (Comonad f, Polynomial f, GEq (Tag f)) => IQuiver (Position f) (Direction f) where
  src = domTag
  tgt = codTag

instance (Comonad f, Polynomial f, GEq (Tag f)) => ICategory (Position f) (Direction f) where
  foldPath (Path fstTag directions _) = foldl' step (identityDir fstTag) directions
    where
      step dir1 dir2 = case composeDir dir1 dir2 of
        Nothing -> error "unreachable; invalid path"
        Just dir -> dir