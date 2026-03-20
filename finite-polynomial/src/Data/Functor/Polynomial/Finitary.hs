{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
module Data.Functor.Polynomial.Finitary(
    Ev(..), Ev₀(..),
    toSum, fromSum, toProduct, fromProduct,
    toComp, fromComp
) where

import Data.Kind (Type)

import Data.Void (absurd)
import GHC.Generics hiding (S,C,D)

import Data.Singletons

import Data.Polynomial
import Data.Functor.Polynomial.Class (Polynomial(..))
import Data.Functor.Polynomial.Finitary.Tag ( FinPolyTag(..) )
import qualified Data.Functor.Polynomial as FP

data Ev₀ (p :: P₀) (x :: Type) where
    MakeEv₀ :: Ev p x -> Ev₀ (NZ p) x

deriving instance Eq x => Eq (Ev₀ p x)
deriving instance Ord x => Ord (Ev₀ p x)
deriving instance Show x => Show (Ev₀ p x)
deriving instance Functor (Ev₀ p)

data Ev (p :: P) (x :: Type) where
    End :: Ev 'U x
    Stop :: Ev ('S p) x
    Go :: Ev p x -> Ev ('S p) x
    (:::) :: x -> Ev p x -> Ev ('T p) x

infixr 7 :::

deriving instance Eq x => Eq (Ev p x)
deriving instance Ord x => Ord (Ev p x)
deriving instance Show x => Show (Ev p x)
deriving instance Functor (Ev p)
deriving instance Foldable (Ev p)
deriving instance Traversable (Ev p)

toSum :: Sing p -> Sing q -> Ev (p + q) x -> (Ev p :+: Ev q) x
toSum sp sq hx = case sp of
    SingU -> case hx of
        Stop -> L1 End
        Go gx -> R1 gx
    SingS sp' -> case hx of
        Stop -> L1 Stop
        Go hx' -> case toSum sp' sq hx' of
            L1 fx -> L1 (Go fx)
            R1 gx -> R1 gx
    SingT sp' -> case sq of
        SingU -> case hx of
            Stop -> R1 End
            Go fx -> L1 fx
        SingS sq' -> case hx of
            Stop -> R1 Stop
            Go hx' -> case toSum sp sq' hx' of
                L1 fx -> L1 fx
                R1 gx -> R1 (Go gx)
        SingT sq' -> case hx of
            x ::: hx' -> case toSum sp' sq' hx' of
                L1 fx -> L1 (x ::: fx)
                R1 gx -> R1 (x ::: gx)

fromSum :: Sing p -> Sing q -> (Ev p :+: Ev q) x -> Ev (p + q) x
fromSum sp sq fgx = case sp of
    SingU -> case fgx of
        L1 End -> Stop
        R1 gx -> Go gx
    SingS sp' -> case fgx of
        L1 Stop -> Stop
        L1 (Go fx) -> Go (fromSum sp' sq (L1 fx))
        R1 gx -> Go (fromSum sp' sq (R1 gx))
    SingT sp' -> case sq of
        SingU -> case fgx of
            L1 fx -> Go fx
            R1 End -> Stop
        SingS sq' -> case fgx of
            L1 fx -> Go (fromSum sp sq' (L1 fx))
            R1 Stop -> Stop
            R1 (Go gx) -> Go (fromSum sp sq' (R1 gx))
        SingT sq' -> case fgx of
            L1 (x ::: fx) -> x ::: fromSum sp' sq' (L1 fx)
            R1 (x ::: gx) -> x ::: fromSum sp' sq' (R1 gx)

fromProduct :: Sing p -> Sing q -> (Ev p :*: Ev q) x -> Ev (p * q) x
fromProduct sp sq (fx :*: gx) = case sp of
    SingU -> gx
    SingS sp' -> case sq of
        SingU -> fx
        SingS sq' -> case (fx, gx) of
            (Stop,  Stop)  -> Stop
            (Go fx', Stop)  -> Go $ fromSum (sp' %+ sq') (sp' %* sq') (L1 $ fromSum sp' sq' (L1 fx'))
            (Stop,  Go gx') -> Go $ fromSum (sp' %+ sq') (sp' %* sq') (L1 $ fromSum sp' sq' (R1 gx'))
            (Go fx', Go gx') -> Go $ fromSum (sp' %+ sq') (sp' %* sq') (R1 $ fromProduct sp' sq' (fx' :*: gx'))
        SingT sq' -> case gx of
            x ::: gx' -> x ::: fromProduct sp sq' (fx :*: gx')
    SingT sp' -> case fx of
        x ::: fx' -> x ::: fromProduct sp' sq (fx' :*: gx)

toProduct :: Sing p -> Sing q -> Ev (p * q) x -> (Ev p :*: Ev q) x
toProduct sp sq hx = case sp of
    SingU -> End :*: hx
    SingS sp' -> case sq of
        SingU -> hx :*: End
        SingS sq' -> case hx of
            Stop -> Stop :*: Stop
            Go hx' -> case toSum (sp' %+ sq') (sp' %* sq') hx' of
                L1 hx'' -> case toSum sp' sq' hx'' of
                    L1 fx' -> Go fx' :*: Stop
                    R1 gx' -> Stop :*: Go gx'
                R1 hx'' ->
                    let fx' :*: gx' = toProduct sp' sq' hx''
                    in Go fx' :*: Go gx'
        SingT sq' -> case hx of
            x ::: hx' ->
                let fx :*: gx' = toProduct sp sq' hx'
                in fx :*: (x ::: gx')
    SingT sp' -> case hx of
        x ::: hx' ->
            let fx' :*: gx = toProduct sp' sq hx'
            in (x ::: fx') :*: gx

fromComp :: SingP p -> SingP q -> Ev p (Ev q x) -> Ev (p << q) x
fromComp sp sq fgx = case sp of
    SingU -> End
    SingS sp' -> case fgx of
        Stop -> Stop
        Go fgx' -> Go (fromComp sp' sq fgx')
    SingT sp' -> case fgx of
        gx ::: fgx' -> fromProduct sq (sp' %<< sq) (gx :*: fromComp sp' sq fgx')

toComp :: SingP p -> SingP q -> Ev (p << q) x -> Ev p (Ev q x)
toComp sp sq hx = case sp of
    SingU -> End
    SingS sp' -> case hx of
        Stop -> Stop
        Go hx' -> Go (toComp sp' sq hx')
    SingT sp' -> 
        let gx :*: hx' = toProduct sq (sp' %<< sq) hx
        in gx ::: toComp sp' sq hx'


---

instance Polynomial (Ev p) where
    type Tag (Ev p) = FinPolyTag p

    toPoly :: Ev p x -> FP.Poly (FinPolyTag p) x
    toPoly End        = FP.P FinPolyEnd  absurd
    toPoly Stop       = FP.P FinPolyStop absurd
    toPoly (Go ev)    = case toPoly ev of
                            FP.P t rep -> FP.P (FinPolyGo t) rep
    toPoly (x ::: ev) = case toPoly ev of
                            FP.P t rep -> FP.P (FinPolyCons t)
                                             (\case Left ()  -> x
                                                    Right i  -> rep i)

    fromPoly :: FP.Poly (FinPolyTag p) x -> Ev p x
    fromPoly (FP.P tag rep) = case tag of
        FinPolyEnd    -> End
        FinPolyStop   -> Stop
        FinPolyGo   t -> Go (fromPoly (FP.P t rep))
        FinPolyCons t -> rep (Left ()) ::: fromPoly (FP.P t (rep . Right))
