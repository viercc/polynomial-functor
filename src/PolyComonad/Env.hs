{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
-- | Discrete category <-> 'Env' comonad
module PolyComonad.Env where

import Prelude hiding (id, (.))
import Control.Comonad.Env
import Data.Kind (Type)
import Data.Type.Equality

import BabySingleton
import PolyComonad

-- | @(':~:')@ is a discrete category on kind @k@.
type Discrete :: forall k. k -> k -> Type
type Discrete = (:~:)

-- | @Poly (Discrete @k) r ~ (k, r) ~ Env k r@
fromEnv :: Demote k => Env (Val k) r -> Poly (Discrete @k) r
fromEnv (runEnv -> (x, r)) = toSing x \sx -> MkPoly sx \_ Refl -> r

toEnv :: Demote k => Poly (Discrete @k) r -> Env (Val k) r
toEnv (MkPoly sx k) = env (fromSing sx) (k sx Refl)
