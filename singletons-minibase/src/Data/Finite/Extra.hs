{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Data.Finite.Extra
  ( -- * Finite
    absurdFinite, boringFinite,
    combineSumS,
    separateSumS,
    combineProductS,
    separateProductS
  )
where

import Data.Finite
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

-- | 'separateProduct' but uses 'SNat' instead of 'KnownNat'
separateProductS :: SNat n -> SNat m -> Finite (n * m) -> (Finite n, Finite m)
separateProductS sn _ = withKnownNat sn separateProduct

-- | 'combineProduct' but uses 'SNat' instead of 'KnownNat'
combineProductS :: SNat n -> SNat m -> (Finite n, Finite m) -> Finite (n * m)
combineProductS sn _ = withKnownNat sn combineProduct
