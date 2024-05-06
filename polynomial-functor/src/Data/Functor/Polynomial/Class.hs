{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Data.Functor.Polynomial.Class where

import Data.Functor.Identity(Identity(..))
import Data.Functor.Const
import Data.Proxy
import Data.Functor.Sum
import Data.Functor.Product
import Data.Functor.Compose
import Data.Functor.Day

import GHC.Generics
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..))
import GHC.TypeNats (Nat, withKnownNat)

import Data.Finitary
import Data.Finite
import Data.Finite.Extra
import qualified Data.Vector.Sized as SV

import Data.Functor.Pow
import Data.Functor.Polynomial.Tag
import Data.Functor.Polynomial

-- | A class for 'Functor' which can be represented as 'Poly'.
--   
--   'toPoly' and 'fromPoly' are isomorphisms.
--   
--   > toPoly . fromPoly = id
--   > fromPoly . toPoly = id
class (Functor f, HasSNat (Tag f)) => Polynomial f where
  type Tag f :: Nat -> Type

  toPoly :: f x -> Poly (Tag f) x
  fromPoly :: Poly (Tag f) x -> f x

instance Finitary r => Polynomial ((->) r) where
  type Tag ((->) r) = (:~:) (Cardinality r)

  toPoly f = P Refl (f . fromFinite)
  fromPoly (P Refl f) r = f (toFinite r)

---- Instances ----
instance Polynomial Maybe where
  type Tag Maybe = TagMaybe

  toPoly mx = case mx of
    Nothing -> P TagNothing absurdFinite
    Just x  -> P TagJust (const x)
  fromPoly (P tag rep) = case tag of
    TagNothing -> Nothing
    TagJust -> Just (rep boringFinite)

instance Polynomial [] where
  type Tag [] = SNat

  toPoly :: forall x. [x] -> Poly SNat x
  toPoly xs = SV.withSizedList xs $ \v -> P SNat (SV.index v)

  fromPoly :: forall x. Poly SNat x -> [x]
  fromPoly (P sn f) = f <$> withKnownNat sn finites

instance Polynomial V1 where
  type Tag V1 = TagV
  toPoly v = case v of { }
  fromPoly (P v _) = case v of { }

instance Polynomial U1 where
  type Tag U1 = TagFn 0

  toPoly _ = P Refl absurdFinite
  fromPoly _ = U1

instance Polynomial Proxy where
  type Tag Proxy = TagFn 0

  toPoly _ = P Refl absurdFinite
  fromPoly _ = Proxy

instance Polynomial (K1 i c) where
  type Tag (K1 i c) = TagK c

  toPoly (K1 c) = P (TagK c) absurdFinite
  fromPoly (P (TagK c) _) = K1 c

instance Polynomial (Const c) where
  type Tag (Const c) = TagK c

  toPoly (Const c) = P (TagK c) absurdFinite
  fromPoly (P (TagK c) _) = Const c

instance Polynomial f => Polynomial (M1 i c f) where
  type Tag (M1 i c f) = Tag f
  fromPoly = M1 . fromPoly
  toPoly = toPoly . unM1

instance Polynomial f => Polynomial (Rec1 f) where
  type Tag (Rec1 f) = Tag f
  fromPoly = Rec1 . fromPoly
  toPoly = toPoly . unRec1

instance Polynomial Par1 where
  type Tag Par1 = TagFn 1

  toPoly (Par1 x) = P Refl (const x)
  fromPoly (P Refl x') = Par1 (x' boringFinite)

instance Polynomial Identity where
  type Tag Identity = TagFn 1

  toPoly (Identity x) = P Refl (const x)
  fromPoly (P Refl e) = Identity (e boringFinite)

instance (Polynomial f, Polynomial g) => Polynomial (f :+: g) where
  type Tag (f :+: g) = TagSum (Tag f) (Tag g)

  toPoly (L1 fx) = case toPoly fx of
    P tag rep -> P (L1 tag) rep
  toPoly (R1 gx) = case toPoly gx of
    P tag rep -> P (R1 tag) rep

  fromPoly (P (L1 tag) rep) = L1 (fromPoly (P tag rep))
  fromPoly (P (R1 tag) rep) = R1 (fromPoly (P tag rep))

instance (Polynomial f, Polynomial g) => Polynomial (Sum f g) where
  type Tag (Sum f g) = TagSum (Tag f) (Tag g)

  toPoly = toPoly . toGenerics
    where
      toGenerics (InL fx) = L1 fx
      toGenerics (InR gx) = R1 gx

  fromPoly = fromGenerics . fromPoly
    where
      fromGenerics (L1 fx) = InL fx
      fromGenerics (R1 gx) = InR gx

instance (Polynomial f, Polynomial g) => Polynomial (f :*: g) where
  type Tag (f :*: g) = TagMul (Tag f) (Tag g)

  toPoly (fx :*: gx) =
    case (toPoly fx, toPoly gx) of
      (P tagF repF, P tagG repG) ->
        P (TagMul tagF tagG) (either repF repG . separateSumS (toSNat tagF) (toSNat tagG))

  fromPoly (P (TagMul tagF tagG) rep) =
    let combine = combineSumS (toSNat tagF) (toSNat tagG)
        pf = P tagF (rep . combine . Left)
        pg = P tagG (rep . combine . Right)
     in fromPoly pf :*: fromPoly pg

instance (Polynomial f, Polynomial g) => Polynomial (Product f g) where
  type Tag (Product f g) = TagMul (Tag f) (Tag g)

  toPoly = toPoly . toGenerics
    where
      toGenerics (Pair fx gx) = fx :*: gx

  fromPoly = fromGenerics . fromPoly
    where
      fromGenerics (fx :*: gx) = Pair fx gx

instance (Polynomial f) => Polynomial (Pow n f) where
  type Tag (Pow n f) = TagPow n (Tag f)

  toPoly :: forall x. Pow n f x -> Poly (TagPow n (Tag f)) x
  toPoly Pow0 = P ZeroTag absurdFinite
  toPoly (PowSnoc fs f) = case (toPoly fs, toPoly f) of
      (P tagFs repFs, P tagF repF) ->
        P (tagFs :+| tagF) (either repFs repF . separateSumS (toSNat tagFs) (toSNat tagF))

  fromPoly :: forall x. Poly (TagPow n (Tag f)) x -> Pow n f x
  fromPoly (P tag rep) = case tag of
    ZeroTag -> Pow0
    tagFs :+| tagF ->
        let combine = combineSumS (toSNat tagFs) (toSNat tagF)
            fs = fromPoly (P tagFs (rep . combine . Left))
            f  = fromPoly (P tagF  (rep . combine . Right))
        in PowSnoc fs f

instance (Polynomial f, Polynomial g) => Polynomial (f :.: g) where
  type Tag (f :.: g) = TagComp (Tag f) (Tag g)

  toPoly :: forall x. (f :.: g) x -> Poly (TagComp (Tag f) (Tag g)) x
  toPoly (Comp1 fgy) = case toPoly fgy of
    P tagF repF ->
      case toPoly (functionToPow (toSNat tagF) repF) of
        P tagPowG repPow -> P (TagComp tagF tagPowG) repPow

  fromPoly :: forall x. Poly (TagComp (Tag f) (Tag g)) x -> (f :.: g) x
  fromPoly (P (TagComp tagF tagPowG) rep) =
    let repF = powToFunction $ fromPoly (P tagPowG rep)
    in  Comp1 $ fromPoly (P tagF repF)


instance (Polynomial f, Polynomial g) => Polynomial (Compose f g) where
  type Tag (Compose f g) = TagComp (Tag f) (Tag g)

  toPoly = toPoly . toGenerics
    where
      toGenerics :: forall x. Compose f g x -> (f :.: g) x 
      toGenerics = coerce

  fromPoly = fromGenerics . fromPoly
    where
      fromGenerics :: forall x. (f :.: g) x -> Compose f g x
      fromGenerics = coerce


instance (Polynomial f, Polynomial g) => Polynomial (Day f g) where
    type Tag (Day f g) = TagDay (Tag f) (Tag g)

    toPoly (Day fa gb op) = case (toPoly fa, toPoly gb) of
        (P tagF repF, P tagG repG) ->
            let repFG (n,m) = op (repF n) (repG m) 
            in P (TagDay tagF tagG) (repFG . separateProductS (toSNat tagF) (toSNat tagG))

    fromPoly (P (TagDay tagF tagG) repFG) =
        let op n m = repFG $ combineProductS (toSNat tagF) (toSNat tagG) (n,m)
        in Day (fromPoly (P tagF id)) (fromPoly (P tagG id)) op

-- | @fromPoly = toPoly = id@
instance HasSNat tag => Polynomial (Poly tag) where
  type Tag (Poly tag) = tag

  fromPoly = id
  toPoly = id

---- Generic definitions ----
instance (Generic1 f, HasSNat (Tag (Rep1 f)), Polynomial (Rep1 f)) => Polynomial (Generically1 f) where
  type Tag (Generically1 f) = Tag (Rep1 f)

  toPoly (Generically1 fx) = toPoly (from1 fx)
  fromPoly p = Generically1 $ to1 (fromPoly p)

deriving via (Generically1 (Either a))
  instance Polynomial (Either a)

deriving via (Generically1 ((,) a))
  instance Polynomial ((,) a)