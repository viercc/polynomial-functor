{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
-- | A small but non-trivial example of category <-> comonad correspondence
module PolyComonad.Boolean where

import Prelude hiding (id, (.))
import Control.Category
import Control.Comonad
import Data.Kind (Type)

import Data.Bool.Singletons
import Data.Singletons.Sigma

import PolyComonad

data H r = H1 r | H2 r r
    deriving Functor

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

-- | 'Poly' 'Implies' is isomorphic to 'H', including its 'Comonad' instance.
toH :: Poly Implies r -> H r
toH (MkPoly STrue k) = H1 (k (STrue :&: ImpId))
toH (MkPoly SFalse k) = H2 (k (SFalse :&: ImpId)) (k (STrue :&: ImpFT))

fromH :: H r -> Poly Implies r
fromH (H1 r0) = MkPoly STrue \(_ :&: tt) -> case tt of
    ImpId -> r0
fromH (H2 r1 r0) = MkPoly SFalse \(_ :&: fz) -> case fz of
    ImpId -> r1
    ImpFT -> r0
