{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QualifiedDo #-}
module Main (main) where

import Control.Monad (join)
import qualified SemigroupDo

import GHC.Generics
import Data.Singletons

import Data.Polynomial
import Data.Polynomial.Functor
import Data.Polynomial.Functor.Deriving

import Property
import SemiringProp ( semisemiringProp, semiringProp )
import Enum1

main :: IO ()
main = do
  propsPoly
  propsEvCombinators
  propsPolynomialFunctorIso
  propsApplicativeZippy
  propsMonadAligney

-- * Polynomial data

propsPoly :: IO ()
propsPoly = do
  putStrLn "CommutativeSemiSemiring Prop"
  property $ semisemiringProp ([0..3] >>= genPolySized)
  putStrLn "CommutativeSemiring Prop₀"
  property $ semiringProp ([0..4] >>= genPoly₀Sized)

genPolySized :: Int -> [Poly]
genPolySized n
  | n <= 0 = [U]
  | otherwise = [S, T] <*> genPolySized (pred n)

genPoly₀Sized  :: Int -> [Poly₀]
genPoly₀Sized n
  | n <= 0 = [Z]
  | otherwise = NZ <$> genPolySized (pred n)

---- * Functors

genEv :: Sing p -> Enum1 (Ev p)
genEv SingU _ = [End]
genEv (SingS sp) as = Stop : (Go <$> genEv sp as)
genEv (SingT sp) as = (:::) <$> as <*> genEv sp as

propsEvCombinators :: IO ()
propsEvCombinators = do
  let ps = [0..4] >>= genPolySized
  property $
    forAll "p" ps $ \p -> withSomeSing p $ \sp ->
      forAll "q" ps $ \q -> withSomeSing q $ \sq -> SemigroupDo.do
        evSumIsomorphism sp sq
        evProductIsomorphism sp sq
        evCompIsomorphism sp sq

evSumIsomorphism :: forall (p :: Poly) (q :: Poly). Sing p -> Sing q -> Result
evSumIsomorphism sp sq =
  label "isIsomorphism toSum fromSum" $
    isIsomorphism (genEv (sp %+ sq)) (sumEnum (genEv sp) (genEv sq)) (toSum sp sq) (fromSum sp sq)

evProductIsomorphism :: forall (p :: Poly) (q :: Poly). Sing p -> Sing q -> Result
evProductIsomorphism sp sq =
  label "isIsomorphism toProduct fromProduct" $
    isIsomorphism (genEv (sp %* sq)) (prodEnum (genEv sp) (genEv sq)) (toProduct sp sq) (fromProduct sp sq)

evCompIsomorphism :: forall (p :: Poly) (q :: Poly). Sing p -> Sing q -> Result
evCompIsomorphism sp sq =
  label "isIsomorphism toComp fromComp" $
    isIsomorphism (genEv (sp %<< sq)) (compEnum (genEv sp) (genEv sq)) (Comp1 . toComp sp sq) (fromComp sp sq . unComp1)

-- * Derived PolynomialFunctor isomorphism

data Foo a = A a (Maybe a) | B (Maybe a) a
   deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
   deriving PolynomialFunctor via (Generically1 Foo)

genMaybe :: Enum1 Maybe
genMaybe as = Nothing : (Just <$> as)

genFoo :: Enum1 Foo
genFoo as = genA ++ genB
  where
    genA = A <$> as <*> genMaybe as
    genB = B <$> genMaybe as <*> as

newtype Bar a = MkVar (Foo (Maybe (Foo a)))
   deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
   deriving PolynomialFunctor via (Generically1 Bar)

genBar :: Enum1 Bar
genBar as = MkVar <$> genFoo (genMaybe (genFoo as))

propsPolynomialFunctorIso :: IO ()
propsPolynomialFunctorIso = do
  putStrLn "PolynomialFunctor Foo"
  putStrLn $ "PolyRep Foo == " ++ show (fromSing (sPolyRep @Foo))
  putStrLn "isIsomorphism toPoly fromPoly"
  property $
    isIsomorphism genFoo (genEv (sPolyRep @Foo)) toPoly fromPoly
  putStrLn "PolynomialFunctor Bar"
  putStrLn $ "PolyRep Bar == " ++ show (fromSing (sPolyRep @Bar))
  property $
    isIsomorphism genBar (genEv (sPolyRep @Bar)) toPoly fromPoly

-- * Zippy applicative

propsApplicativeZippy :: IO ()
propsApplicativeZippy = do
  putStrLn "Applicative (Zippy p)"
  let ps = [0..4] >>= genPolySized
  property $
    forAll "p" ps $ \p -> withSomeSing p $ \sp ->
      withSingI sp $ propApplicativeLaws (fmap Zippy . genEv sp)

-- * Aligney monad

propsMonadAligney :: IO ()
propsMonadAligney = do
  putStrLn "Applicative (Aligney p)"
  let ps = [0..3] >>= genPolySized
  property $
    forAll "p" ps $ \p -> withSomeSing p $ \sp' -> do
      let sp = SingT sp'
      withSingI sp' $ propApplicativeLaws (fmap Aligney . genEv sp)
  putStrLn "Monad (Aligney p)"
  property $
    forAll "p" ps $ \p -> withSomeSing p $ \sp' -> do
      let sp = SingT sp'
      withSingI sp' $ propMonadLaws (fmap Aligney . genEv sp)

propApplicativeLaws
  :: (Applicative f)
  => (Traversable f)
  => (forall x. Show x => Show (f x))
  => (forall x. Eq x => Eq (f x))
  => Enum1 f -> Result
propApplicativeLaws genF = SemigroupDo.do
  label "LeftUnit" $
    forAll "fx" (skolem genF) $ \fx -> pure id <*> fx === fx
  label "RightUnit" $
    forAll "fx" (skolem genF) $ \fx -> const <$> fx <*> pure id === fx
  label "Assoc" $
    forAll "fx" (skolem genF) $ \fx ->
      let fx' = (,) <$> fx
      in forAll "fy" (skolem genF) $ \fy ->
          let fy' = (,) <$> fy
          in forAll "fz" (skolem genF) $ \fz ->
                fx' <*> (fy' <*> fz) === (.) <$> fx' <*> fy' <*> fz

propMonadLaws
  :: (Monad f)
  => (Traversable f)
  => (forall x. Show x => Show (f x))
  => (forall x. Eq x => Eq (f x))
  => Enum1 f -> Result
propMonadLaws genF = SemigroupDo.do
  label "LeftUnit" $
    forAll "fx" (skolem genF) $ \fx -> join (pure fx) === fx
  label "RightUnit" $
    forAll "fx" (skolem genF) $ \fx -> join (fmap pure fx) === fx
  label "Assoc" $
    forAll "fffx" (skolem (compEnum (compEnum genF genF) genF)) $ \(Comp1 (Comp1 fffx)) ->
      join (join fffx) === join (fmap join fffx)
  label "Compatible with Applicative" $
    forAll "fx" (skolem genF) $ \fx ->
      forAll "fy" (skolem genF) $ \fy ->
        (fx >>= \x -> fy >>= \y -> pure (x,y)) === (,) <$> fx <*> fy
