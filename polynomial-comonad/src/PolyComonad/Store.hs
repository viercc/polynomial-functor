{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
-- | Indiscrete category <-> 'Store' comonad
module PolyComonad.Store where

import Control.Comonad.Store

import Data.Singletons
import PolyComonad
import Control.Category.Indiscrete
import Data.Singletons.Sigma (Sigma(..))

fromStore :: SingKind k => Store (Demote k) r -> Poly (Indiscrete @k) r
fromStore w = case toSing (pos w) of
  SomeSing sPos -> MkPoly sPos \(sPos' :&: _) -> peek (fromSing sPos') w

toStore :: SingKind k => Poly (Indiscrete @k) r -> Store (Demote k) r
toStore (MkPoly sp body) =
  let f v = case toSing v of
        SomeSing sv -> body (sv :&: Indiscrete)
  in store f (fromSing sp)
