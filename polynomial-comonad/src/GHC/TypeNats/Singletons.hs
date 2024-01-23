{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module GHC.TypeNats.Singletons where

import GHC.TypeNats.Compat (KnownNat, Nat)
import GHC.TypeLits.Witnesses

import Data.Singletons

type instance Sing = SNat

instance KnownNat n => SingI n where sing = SNat

instance SingKind Nat where
  type Demote Nat = Natural

  toSing n = withSomeSNat n SomeSing
  fromSing = fromSNat