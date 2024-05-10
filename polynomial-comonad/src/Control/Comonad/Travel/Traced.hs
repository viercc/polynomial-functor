{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}

-- | Monoid <-> One-object category <-> 'Traced' comonad
module Control.Comonad.Travel.Traced where

import Control.Category.OneObject
import Control.Comonad.Traced
import Control.Comonad.Travel
import Data.Singletons.Sigma (Sigma (..))
import Data.Unit.Singletons

-- | @Travel (OneObject m) r ~ (m -> r) ~ Traced m r@
fromTraced :: Traced m r -> Travel (OneObject m) r
fromTraced w = MkTravel SU \(SU :&: OneObject m) -> runTraced w m

toTraced :: Travel (OneObject m) r -> Traced m r
toTraced (MkTravel _ f) = traced (\m -> f (SU :&: OneObject m))
