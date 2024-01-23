{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module PolyComonad.NonEmpty where

import Prelude hiding (id, (.))
import Data.Kind (Type)
import Data.Foldable (Foldable(..))

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import GHC.TypeNats
import GHC.TypeLits.Witnesses (pattern Succ, pattern Zero, (%-))

import PolyComonad

import Control.Category.NatOrd
import Control.Category.Dual (Dual(..))

import GHC.TypeNats.Singletons() -- import orphans
import Data.Singletons.Sigma (Sigma(..))

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

fromNonEmptyVec :: NonEmptyVec a -> Poly (:>=:) a
fromNonEmptyVec (NonEmptyVec as) =
    let n = vecLen as %- natSing @1
    in MkPoly n (\(m :&: Dual mn) -> withKnownNat n $ withKnownNat m $ index as mn)

toNonEmptyVec :: Poly (:>=:) a -> NonEmptyVec a
toNonEmptyVec (MkPoly n f) = NonEmptyVec ((\(Finite' mn) -> f (natSing :&: Dual mn)) <$> indices (Succ n))
