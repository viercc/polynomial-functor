{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
module Data.GADT.HasSNat where

import GHC.TypeNats (KnownNat())
import GHC.TypeNats.Extra (SNat(SNat))
import Data.Type.Equality ((:~:)(..) )
import GHC.Generics ((:+:)(..))

class HasSNat t where
  toSNat :: t n -> SNat n

-- | Represents @(Nat, id :: Nat -> Nat)
instance HasSNat SNat where
  toSNat = id

instance KnownNat n => HasSNat ((:~:) n) where
  toSNat Refl = SNat

instance (HasSNat t1, HasSNat t2) => HasSNat ((:+:) t1 t2) where
  toSNat (L1 t1) = toSNat t1
  toSNat (R1 t2) = toSNat t2
