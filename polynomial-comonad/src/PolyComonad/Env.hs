{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
-- | Discrete category <-> 'Env' comonad
module PolyComonad.Env where

import Prelude hiding (id, (.))
import Control.Comonad.Env
import Data.Kind (Type)
import Data.Type.Equality

import Data.Singletons
import PolyComonad
import Data.Singletons.Sigma (Sigma(..))

-- | @(':~:')@ is a discrete category on kind @k@.
type Discrete :: forall k. k -> k -> Type
type Discrete = (:~:)

-- | @Poly (Discrete @k) r ~ (k, r) ~ Env k r@
fromEnv :: SingKind k => Env (Demote k) r -> Poly (Discrete @k) r
fromEnv (runEnv -> (x, r)) = case toSing x of
  SomeSing sx -> MkPoly sx \(_ :&: Refl) -> r

toEnv :: SingKind k => Poly (Discrete @k) r -> Env (Demote k) r
toEnv (MkPoly sx k) = env (fromSing sx) (k (sx :&: Refl))
