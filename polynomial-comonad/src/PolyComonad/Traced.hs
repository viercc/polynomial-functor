{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
-- | Monoid <-> One-object category <-> 'Traced' comonad
module PolyComonad.Traced where

import Control.Comonad.Traced

import BabySingleton
import PolyComonad
import Control.Category.OneObject

-- | @Poly (OneObject m) r ~ (m -> r) ~ Traced m r@
fromTraced :: Traced m r -> Poly (OneObject m) r
fromTraced w = MkPoly SU \SU (OneObject m) -> runTraced w m

toTraced :: Poly (OneObject m) r -> Traced m r
toTraced (MkPoly _ f) = traced (f SU . OneObject)
