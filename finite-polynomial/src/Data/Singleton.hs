{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
module Data.Singleton(
    Sing, SomeSing(..), withSing,
    SingKind(..),

    -- * Re-export
    TestEquality(..)
) where

import Data.Kind (Type)
import Data.Type.Equality (TestEquality(..))

data family Sing k (a :: k) :: Type

data SomeSing k where
    SomeSing :: Sing k a -> SomeSing k

class SingKind (k :: Type) where
    fromSing :: Sing k a -> k
    toSing :: k -> SomeSing k

withSing :: SingKind k => k -> (forall a. Sing k a -> r) -> r
withSing k ret = case toSing k of
    SomeSing a -> ret a
