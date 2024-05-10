{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}

-- | A small but non-trivial example of category <-> comonad correspondence
module Control.Comonad.Travel.Boolean where

import Control.Category
import Control.Comonad
import Control.Comonad.Travel
import Data.Bool.Singletons
import Data.Kind (Type)
import Data.Singletons.Sigma
import Prelude hiding (id, (.))

data H r = H1 r | H2 r r
  deriving (Functor)

instance Comonad H where
  extract (H1 r) = r
  extract (H2 r _) = r

  duplicate (H1 r0) = H1 (H1 r0)
  duplicate (H2 r1 r0) = H2 (H2 r1 r0) (H1 r0)

-- | Boolean algebra {False, True} can be seen as a category:
--
--   > False ---> True
--   >   ↺         ↺
--
-- Note: Roughly speaking, there are only three values in
-- types @Implies b1 b2@, where @b1, b2@ are chosen from either @False@ or @True@.
--
-- @
-- ImpId :: Implies False False
-- ImpId :: Implies True True
-- ImpFT :: Implies False True
-- @
type Implies :: Bool -> Bool -> Type
data Implies x y where
  ImpId :: Implies x x
  ImpFT :: Implies False True

instance Category Implies where
  id = ImpId
  ImpId . g = g
  ImpFT . ImpId = ImpFT

-- | 'Travel' 'Implies' is isomorphic to 'H', including its 'Comonad' instance.
toH :: Travel Implies r -> H r
toH (MkTravel STrue k) = H1 (k (STrue :&: ImpId))
toH (MkTravel SFalse k) = H2 (k (SFalse :&: ImpId)) (k (STrue :&: ImpFT))

fromH :: H r -> Travel Implies r
fromH (H1 r0) = MkTravel STrue \(_ :&: tt) -> case tt of
  ImpId -> r0
fromH (H2 r1 r0) = MkTravel SFalse \(_ :&: fz) -> case fz of
  ImpId -> r1
  ImpFT -> r0
