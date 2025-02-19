{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Control.Comonad.Travel.NonEmpty(
  fromNonEmpty, toNonEmpty
) where

import Control.Category ((.))
import Control.Category.Dual (Dual (..))
import Control.Category.NatOrd
import Control.Comonad.Travel
import Data.Foldable (Foldable (..))
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Singletons (TyCon)
import Data.Singletons.Sigma (Sigma (..))
import GHC.TypeNats
import GHC.TypeNats.Extra (SNat (Succ, Zero))
import GHC.TypeNats.Singletons ()
import Prelude hiding (id, (.))
import Data.Some

viewNE :: NonEmpty a -> (forall n. SNat n -> (forall m. (m :<=: n) -> a) -> r) -> r
viewNE as body = case NE.uncons as of
  (a, Nothing) -> body Zero (singletonFn a)
  (a, Just as') -> viewNE as' (\n f -> body (Succ n) (consFn a f))

singletonFn :: a -> (forall m. (m :<=: 0) -> a)
singletonFn a ReflLE = a
singletonFn _ (SuccLE mn) = zero_neq_succ mn

consFn :: a -> (forall m. (m :<=: n) -> a) -> (forall m. (m :<=: 1 + n) -> a)
consFn a f mn = case mn of
  ReflLE -> a
  SuccLE mn' -> f mn'

indices :: SNat n -> NonEmpty (Some ((:>=:) n))
indices Zero = Some (Dual ReflLE) :| []
indices (Succ n) = Some (Dual ReflLE) :| fmap (mapSome succGE) (toList (indices n))

succGE :: (n :>=: m) -> (1 + n :>=: m)
succGE (Dual mn) = Dual (SuccLE mn)

fromNonEmpty :: NonEmpty a -> Travel (:>=:) a
fromNonEmpty as = viewNE as $ \n f -> MkTravel n (\(_ :&: Dual mn) -> f mn)

toNonEmpty :: Travel (:>=:) a -> NonEmpty a
toNonEmpty (MkTravel n f) = (f . makeKey n) <$> indices n

makeKey :: SNat n -> Some ((:>=:) n) -> Sigma Nat (TyCon ((:>=:) n))
makeKey sn (Some (Dual mn)) = getLower sn mn :&: Dual mn

getLower :: SNat n -> (m :<=: n) -> SNat m
getLower Zero mn = case mn of
  ReflLE -> Zero
  SuccLE mn' -> zero_neq_succ mn'
getLower sn@(Succ sn') mn = case mn of
  ReflLE -> sn
  SuccLE mn' -> getLower sn' mn'

zero_neq_succ :: forall p n a. (0 ~ (1 + n)) => p n -> a
zero_neq_succ _ = error "impossible!"