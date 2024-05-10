{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Control.Comonad.Travel.NonEmpty where

import Control.Category.Dual (Dual (..))
import Control.Category.NatOrd
-- import orphans

import Control.Comonad.Travel
import Data.Foldable (Foldable (..))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Singletons.Sigma (Sigma (..))
import GHC.TypeNats
import GHC.TypeNats.Extra (SNat (Succ, Zero), (%-))
import GHC.TypeNats.Singletons ()
import Prelude hiding (id, (.))

type Vec :: Nat -> Type -> Type
data Vec n a where
  Nil :: Vec 0 a
  Cons :: a -> Vec n a -> Vec (1 + n) a

deriving instance Functor (Vec n)

deriving instance Foldable (Vec n)

vecLen :: Vec n a -> SNat n
vecLen Nil = Zero
vecLen (Cons _ as) = Succ (vecLen as)

index :: (KnownNat n, KnownNat m) => Vec (1 + n) a -> m :<=: n -> a
index Nil _ = error "impossible!"
index (Cons a as) mn = case mn of
  ReflLE -> a
  SuccLE mn' -> index as mn'

indices :: SNat n -> Vec n (Finite' n)
indices Zero = Nil
indices (Succ n) = Cons (withKnownNat n (Finite' ReflLE)) (shift' <$> indices n)

data NonEmptyVec a where
  NonEmptyVec :: Vec (1 + n) a -> NonEmptyVec a

fromNonEmpty :: NonEmpty a -> NonEmptyVec a
fromNonEmpty as = viewNonEmpty as NonEmptyVec
  where
    viewNonEmpty :: NonEmpty a -> (forall n. Vec (1 + n) a -> r) -> r
    viewNonEmpty xs body = case NE.uncons xs of
      (x, Nothing) -> body (Cons x Nil)
      (x, Just xs') -> viewNonEmpty xs' (\vec -> body (Cons x vec))

toNonEmpty :: NonEmptyVec a -> NonEmpty a
toNonEmpty (NonEmptyVec as) = case as of
  Nil -> error "impossible!"
  Cons a as' -> a :| toList as'

fromNonEmptyVec :: NonEmptyVec a -> Travel (:>=:) a
fromNonEmptyVec (NonEmptyVec as) =
  let n = vecLen as %- natSing @1
   in MkTravel n (\(m :&: Dual mn) -> withKnownNat n $ withKnownNat m $ index as mn)

toNonEmptyVec :: Travel (:>=:) a -> NonEmptyVec a
toNonEmptyVec (MkTravel n f) = NonEmptyVec ((\(Finite' mn) -> f (natSing :&: Dual mn)) <$> indices (Succ n))
