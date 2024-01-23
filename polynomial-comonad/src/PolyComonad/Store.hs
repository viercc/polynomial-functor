{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
-- | Indiscrete category <-> 'Store' comonad
module PolyComonad.Store where

import Control.Comonad.Store

import BabySingleton
import PolyComonad
import Control.Category.Indiscrete

fromStore :: Demote k => Store (Val k) r -> Poly (Indiscrete @k) r
fromStore w = toSing (pos w) \sPos -> MkPoly sPos \sPos' _ -> peek (fromSing sPos') w

toStore :: Demote k => Poly (Indiscrete @k) r -> Store (Val k) r
toStore (MkPoly sp body) = store (\v -> toSing v \sv -> body sv Indiscrete) (fromSing sp)
