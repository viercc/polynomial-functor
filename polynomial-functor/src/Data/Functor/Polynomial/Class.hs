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
module Data.Functor.Polynomial.Class(
  Polynomial(..),
) where

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

import Data.Finitary
import qualified Data.Vector.Sized as SV

import Data.Functor.Pow
import Data.Functor.Polynomial.Tag
import Data.Functor.Polynomial
import Data.Void
import Data.GADT.HasFinitary (toInhabitants)
import GHC.TypeNats.Extra (SNat(SNat))

-- | A class for 'Functor' which can be represented as 'Poly'.
--   
--   'toPoly' and 'fromPoly' are isomorphisms.
--   
--   > toPoly . fromPoly = id
--   > fromPoly . toPoly = id
class (Functor f) => Polynomial f where
  type Tag f :: Type -> Type

  toPoly :: f x -> Poly (Tag f) x
  fromPoly :: Poly (Tag f) x -> f x

instance Polynomial ((->) r) where
  type Tag ((->) r) = (:~:) r

  toPoly = P Refl
  fromPoly (P Refl f) = f

---- Instances ----
instance Polynomial Maybe where
  type Tag Maybe = TagMaybe

  toPoly mx = case mx of
    Nothing -> P TagNothing absurd
    Just x  -> P TagJust (const x)
  fromPoly (P tag rep) = case tag of
    TagNothing -> Nothing
    TagJust -> Just (rep ())

instance Polynomial [] where
  type Tag [] = TagList

  toPoly :: forall x. [x] -> Poly TagList x
  toPoly xs = SV.withSizedList xs $ \v -> P TagList (SV.index v)

  fromPoly :: forall x. Poly TagList x -> [x]
  fromPoly (P sn f) = f <$> toInhabitants sn

instance Polynomial V1 where
  type Tag V1 = TagV
  toPoly v = case v of { }
  fromPoly (P v _) = case v of { }

instance Polynomial U1 where
  type Tag U1 = TagFn Void

  toPoly _ = P Refl absurd
  fromPoly _ = U1

instance Polynomial Proxy where
  type Tag Proxy = TagFn Void

  toPoly _ = P Refl absurd
  fromPoly _ = Proxy

instance Polynomial (K1 i c) where
  type Tag (K1 i c) = TagK c

  toPoly (K1 c) = P (TagK c) absurd
  fromPoly (P (TagK c) _) = K1 c

instance Polynomial (Const c) where
  type Tag (Const c) = TagK c

  toPoly (Const c) = P (TagK c) absurd
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
  type Tag Par1 = TagFn ()

  toPoly (Par1 x) = P Refl (const x)
  fromPoly (P Refl x') = Par1 (x' ())

instance Polynomial Identity where
  type Tag Identity = TagFn ()

  toPoly (Identity x) = P Refl (const x)
  fromPoly (P Refl e) = Identity (e ())

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
        P (TagMul tagF tagG) (either repF repG)

  fromPoly (P (TagMul tagF tagG) rep) =
    let pf = P tagF (rep . Left)
        pg = P tagG (rep . Right)
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
  toPoly Pow0 = P TagPow0 absurd
  toPoly (PowNZ fs) = case toPoly fs of
      (P tagF repF) -> P (TagPowNZ tagF) repF

  fromPoly :: forall x. Poly (TagPow n (Tag f)) x -> Pow n f x
  fromPoly (P tag rep) = case tag of
    TagPow0 -> Pow0
    TagPowNZ tagFs -> PowNZ (fromPoly (P tagFs rep))

instance (Polynomial f) => Polynomial (Pow' n f) where
  type Tag (Pow' n f) = TagPow' n (Tag f)

  toPoly :: forall x. Pow' n f x -> Poly (TagPow' n (Tag f)) x
  toPoly (Pow1 fx) = case toPoly fx of
    P tag rep -> P (TagPow1 tag) rep
  toPoly (PowEven fs1 fs2) = case (toPoly fs1, toPoly fs2) of
    (P tag1 rep1, P tag2 rep2) -> P (TagPowEven tag1 tag2) (either rep1 rep2)
  toPoly (PowOdd fx fs1 fs2) = case (toPoly fx, toPoly fs1, toPoly fs2) of
    (P tag rep, P tag1 rep1, P tag2 rep2) -> P (TagPowOdd tag tag1 tag2) (either rep (either rep1 rep2))

  fromPoly :: forall x. Poly (TagPow' n (Tag f)) x -> Pow' n f x
  fromPoly (P tag rep) = case tag of
    TagPow1 tag' -> Pow1 (fromPoly (P tag' rep))
    TagPowEven tag1 tag2 -> PowEven (fromPoly (P tag1 (rep . Left))) (fromPoly (P tag2 (rep . Right)))
    TagPowOdd tag' tag1 tag2 ->
      let rep' = rep . Left
          rep1 = rep . Right . Left
          rep2 = rep . Right . Right
      in PowOdd (fromPoly (P tag' rep')) (fromPoly (P tag1 rep1)) (fromPoly (P tag2 rep2))

instance (Polynomial f, HasFinitary (Tag f), Polynomial g) => Polynomial (f :.: g) where
  type Tag (f :.: g) = TagComp (Tag f) (Tag g)

  toPoly :: forall x. (f :.: g) x -> Poly (TagComp (Tag f) (Tag g)) x
  toPoly (Comp1 fgy) = case toPoly fgy of
    P tagF repF ->
      case withFinitary tagF (toPoly (functionToPow SNat (repF . fromFinite))) of
        P tagPowG repPow -> P (TagComp tagF tagPowG) repPow

  fromPoly :: forall x. Poly (TagComp (Tag f) (Tag g)) x -> (f :.: g) x
  fromPoly (P (TagComp tagF tagPowG) rep) =
    let repF = powToFunction $ fromPoly (P tagPowG rep)
    in  withFinitary tagF $ Comp1 $ fromPoly (P tagF (repF . toFinite))

instance (Polynomial f, HasFinitary (Tag f), Polynomial g) => Polynomial (Compose f g) where
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
            in P (TagDay tagF tagG) repFG

    fromPoly (P (TagDay tagF tagG) repFG) =
        let op n m = repFG (n,m)
        in Day (fromPoly (P tagF id)) (fromPoly (P tagG id)) op

-- | @fromPoly = toPoly = id@
instance Polynomial (Poly tag) where
  type Tag (Poly tag) = tag

  fromPoly = id
  toPoly = id

---- Generic definitions ----
instance (Generic1 f, Polynomial (Rep1 f)) => Polynomial (Generically1 f) where
  type Tag (Generically1 f) = Tag (Rep1 f)

  toPoly (Generically1 fx) = toPoly (from1 fx)
  fromPoly p = Generically1 $ to1 (fromPoly p)

deriving via (Generically1 (Either a))
  instance Polynomial (Either a)

deriving via (Generically1 ((,) a))
  instance Polynomial ((,) a)