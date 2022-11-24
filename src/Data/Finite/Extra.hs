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
    weakenS,
    shiftS,
    shiftSRight,
    strengthenWithS,
  )
where

import Data.Finite
import Data.Finite.Internal
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
lessThan1is0 = unsafeCoerce

pattern Zero :: () => (n ~ 0) => SNat n
pattern Zero <- (viewSNat -> ViewZero)
  where
    Zero = sZero

pattern Succ :: () => (n ~ m + 1) => SNat m -> SNat n
pattern Succ m <- (viewSNat -> ViewSucc m)
  where
    Succ m = sSucc m

{-# COMPLETE Zero, Succ #-}

absurdFinite :: Finite 0 -> a
absurdFinite x = x `seq` error ("absurdFinite: x = " ++ show x)

weakenS :: SNat n -> SNat k -> Finite n -> Finite (n + k)
weakenS _ _ (Finite n) = Finite n

shiftS :: SNat n -> SNat k -> Finite n -> Finite (n + k)
shiftS _ k@SNat i = shiftProxy k i

shiftSRight :: SNat n -> proxy k -> Finite k -> Finite (n + k)
shiftSRight n _ i = case n of SNat -> shiftProxy n i

strengthenWithS :: forall n. SNat (n + 1) -> Finite (n + 1) -> Maybe (SNat n, Finite n)
strengthenWithS n i = case sPred n of
  n'@SNat -> case strengthen i of
    Nothing -> Nothing
    Just i' -> Just (n', i')
