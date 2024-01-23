{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
-- | Monoid <-> One-object category <-> 'Traced' comonad
module PolyComonad.Traced where

import Control.Comonad.Traced
import Data.Unit.Singletons

import PolyComonad
import Control.Category.OneObject
import Data.Singletons.Sigma (Sigma(..))

-- | @Poly (OneObject m) r ~ (m -> r) ~ Traced m r@
fromTraced :: Traced m r -> Poly (OneObject m) r
fromTraced w = MkPoly SU \(SU :&: OneObject m) -> runTraced w m

toTraced :: Poly (OneObject m) r -> Traced m r
toTraced (MkPoly _ f) = traced (\m -> f (SU :&: OneObject m))
