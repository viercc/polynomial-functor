{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Data.GADT.HasFinitary where

import Data.Finitary
import GHC.TypeNats.Extra (SNat(SNat))
import GHC.Generics
import Data.Type.Equality ((:~:) (..))

class HasFinitary tag where
  withFinitary :: tag n -> (Finitary n => r) -> r

toSNat :: HasFinitary tag => tag a -> SNat (Cardinality a)
toSNat ta = withFinitary ta SNat

toInhabitants :: HasFinitary tag => tag a -> [a]
toInhabitants ta = withFinitary ta inhabitants

instance Finitary n => HasFinitary ((:~:) n) where
  withFinitary Refl body = body

instance (HasFinitary t1, HasFinitary t2) => HasFinitary ((:+:) t1 t2) where
  withFinitary tag body = case tag of
    L1 t1 -> withFinitary t1 body
    R1 t2 -> withFinitary t2 body
