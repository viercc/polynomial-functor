{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, PatternSynonyms, DataKinds, ViewPatterns, NoStarIsType, ExplicitForAll #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
module GHC.TypeNats.Extra(
  SNatView(..), viewSNat,
  SNat (GHC.TypeNats.Extra.SNat, Zero, Succ),

  (%+), (%-), (%*), (%^)
) where

import GHC.TypeNats hiding (pattern SNat)
import qualified GHC.TypeNats

import qualified Unsafe.Coerce

-- | Wrapper for GHC.TypeNats.'GHC.TypeNats.SNat'
pattern SNat :: forall n. () => KnownNat n => SNat n 
pattern SNat = GHC.TypeNats.SNat

{-# COMPLETE SNat #-}

-- | A view of 'SNat' as if it is defined inductively.
data SNatView n where
  ViewZero :: SNatView 0
  ViewSucc :: SNat n -> SNatView (n + 1)

-- | Perform case analysis on 'SNat'.
viewSNat :: SNat n -> SNatView n
viewSNat sn = case fromSNat sn of
  0 -> unsafeCoerceSNatView $ ViewZero
  n -> withSomeSNat (n - 1) $ \sn' -> unsafeCoerceSNatView $ ViewSucc sn'

-- | Pattern synonym 'Zero' and 'Succ' treats @SNat@ as if
--   it was inductively defined type.
--
--   @
--   -- Virtual definition of SNat
--   data SNat n where
--      Zero :: SNat 0
--      Succ :: SNat n -> SNat (n + 1)
pattern Zero :: () => (n ~ 0) => SNat n
pattern Zero <- (viewSNat -> ViewZero)
  where
    Zero = (SNat :: SNat 0)

pattern Succ :: () => (n ~ m + 1) => SNat m -> SNat n
pattern Succ m <- (viewSNat -> ViewSucc m)
  where
    Succ m = m %+ (SNat :: SNat 1)

{-# COMPLETE Zero, Succ #-}

unsafeBinOp :: (Natural -> Natural -> Natural) -> SNat n -> SNat m -> SNat r
unsafeBinOp op sn sm = 
  let r = op (fromSNat sn) (fromSNat sm)
  in r `seq` withSomeSNat r unsafeCoerceSNat

(%+) :: SNat n -> SNat m -> SNat (n + m)
(%+) = unsafeBinOp (+)

(%-) :: SNat n -> SNat m -> SNat (n - m)
(%-) = unsafeBinOp (-)

(%*) :: SNat n -> SNat m -> SNat (n * m)
(%*) = unsafeBinOp (*)

(%^) :: SNat n -> SNat m -> SNat (n ^ m)
(%^) = unsafeBinOp (^)

---

unsafeCoerceSNatView :: SNatView n -> SNatView m
unsafeCoerceSNatView = Unsafe.Coerce.unsafeCoerce

unsafeCoerceSNat :: SNat n -> SNat m
unsafeCoerceSNat = Unsafe.Coerce.unsafeCoerce