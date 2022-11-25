{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Finite.Extra
  ( -- * SNat
    SNat (Zero, Succ),
    sPred,
    sSucc,

    -- * Finite
    absurdFinite,
    combineSumS,
    separateSumS
  )
where

import Data.Finite
import Data.Type.Equality ((:~:) (..))
import GHC.TypeLits.Compare hiding ((%<=?))
import GHC.TypeLits.Witnesses
import GHC.TypeNats
import Unsafe.Coerce (unsafeCoerce)

sZero :: SNat 0
sZero = SNat

sOne :: SNat 1
sOne = SNat

sPred :: SNat (n + 1) -> SNat n
sPred n = n %- sOne

sSucc :: SNat n -> SNat (n + 1)
sSucc n = n %+ sOne

data SNatView n where
  ViewZero :: SNatView 0
  ViewSucc :: SNat n -> SNatView (n + 1)

viewSNat :: SNat n -> SNatView n
viewSNat n = case sOne %<=? n of
  LE Refl -> ViewSucc (n %- sOne)
  NLE ltWit _ -> case lessThan1is0 n ltWit of Refl -> ViewZero

lessThan1is0 :: p n -> ((1 <=? n) :~: 'False) -> n :~: 0
lessThan1is0 _ _ = unsafeCoerce (Refl :: 0 :~: 0)

pattern Zero :: () => (n ~ 0) => SNat n
pattern Zero <- (viewSNat -> ViewZero)
  where
    Zero = sZero

pattern Succ :: () => (n ~ m + 1) => SNat m -> SNat n
pattern Succ m <- (viewSNat -> ViewSucc m)
  where
    Succ m = sSucc m

{-# COMPLETE Zero, Succ #-}

-- | @'Finite' 0@ is morally an uninhabited type like @Void@.
absurdFinite :: Finite 0 -> a
absurdFinite x = error ("absurdFinite: x = " ++ show x)

-- | 'combineSum' but uses 'SNat' instead of 'KnownNat'
combineSumS :: SNat l -> SNat r -> Either (Finite l) (Finite r) -> Finite (l + r)
combineSumS SNat _ = combineSum

-- | 'separateSum' but uses 'SNat' instead of 'KnownNat'
separateSumS :: SNat l -> SNat r -> Finite (l + r) -> Either (Finite l) (Finite r)
separateSumS SNat _ = separateSum
