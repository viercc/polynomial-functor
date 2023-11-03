{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
module Data.Functor.Pow (Pow(..), functionToPow, powToFunction) where

import GHC.TypeNats.Compat
import Data.Finite
import GHC.TypeLits.Witnesses


-- | @Pow n f = f :*: f :*: ...(n)... :*: f@
data Pow n f x where
  Pow0 :: Pow 0 f x
  PowSnoc :: Pow n f x -> f x -> Pow (n + 1) f x

deriving instance Functor f => Functor (Pow n f)

functionToPow :: SNat n -> (Finite n -> f x) -> Pow n f x
functionToPow sn f = case sn of
  Zero -> Pow0
  Succ sn' -> PowSnoc (functionToPow sn' (f . weaken)) (withKnownNat sn (f maxBound))

powToFunction :: Pow n f x -> Finite n -> f x
powToFunction fs = powToFunction' fs . getFinite

powToFunction' :: Pow n f x -> Integer -> f x
powToFunction' Pow0 k = error $ "Out of bounds:" ++ show k
powToFunction' (PowSnoc fs f) k = case k of
  0 -> f
  _ -> powToFunction' fs (pred k)
