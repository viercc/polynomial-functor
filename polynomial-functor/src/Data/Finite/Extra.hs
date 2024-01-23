{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Data.Finite.Extra
  ( -- * Finite
    absurdFinite, boringFinite,
    combineSumS,
    separateSumS
  )
where

import Data.Finite
import GHC.TypeLits.Witnesses
import GHC.TypeNats

-- | @'Finite' 0@ is morally an uninhabited type like @Void@.
absurdFinite :: Finite 0 -> a
absurdFinite x = error ("absurdFinite: x = " ++ show x)

-- | @'Finite' 1@ is a singleton type
boringFinite :: Finite 1
boringFinite = minBound

-- | 'combineSum' but uses 'SNat' instead of 'KnownNat'
combineSumS :: SNat l -> SNat r -> Either (Finite l) (Finite r) -> Finite (l + r)
combineSumS SNat _ = combineSum

-- | 'separateSum' but uses 'SNat' instead of 'KnownNat'
separateSumS :: SNat l -> SNat r -> Finite (l + r) -> Either (Finite l) (Finite r)
separateSumS SNat _ = separateSum
