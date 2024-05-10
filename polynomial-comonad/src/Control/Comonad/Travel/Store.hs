{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}

-- | Indiscrete category <-> 'Store' comonad
module Control.Comonad.Travel.Store where

import Control.Category.Indiscrete
import Control.Comonad.Store
import Control.Comonad.Travel
import Data.Singletons
import Data.Singletons.Sigma (Sigma (..))

fromStore :: (SingKind k) => Store (Demote k) r -> Travel (Indiscrete @k) r
fromStore w = case toSing (pos w) of
  SomeSing sPos -> MkTravel sPos \(sPos' :&: _) -> peek (fromSing sPos') w

toStore :: (SingKind k) => Travel (Indiscrete @k) r -> Store (Demote k) r
toStore (MkTravel sp body) =
  let f v = case toSing v of
        SomeSing sv -> body (sv :&: Indiscrete)
   in store f (fromSing sp)
