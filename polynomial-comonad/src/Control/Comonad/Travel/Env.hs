{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

-- | Discrete category <-> 'Env' comonad
module Control.Comonad.Travel.Env where

import Control.Comonad.Env
import Control.Comonad.Travel
import Data.Kind (Type)
import Data.Singletons
import Data.Singletons.Sigma (Sigma (..))
import Data.Type.Equality
import Prelude hiding (id, (.))

-- | @(':~:')@ is a discrete category on kind @k@.
type Discrete :: forall k. k -> k -> Type
type Discrete = (:~:)

-- | @Travel (Discrete @k) r ~ (k, r) ~ Env k r@
fromEnv :: (SingKind k) => Env (Demote k) r -> Travel (Discrete @k) r
fromEnv (runEnv -> (x, r)) = case toSing x of
  SomeSing sx -> MkTravel sx \(_ :&: Refl) -> r

toEnv :: (SingKind k) => Travel (Discrete @k) r -> Env (Demote k) r
toEnv (MkTravel sx k) = env (fromSing sx) (k (sx :&: Refl))
