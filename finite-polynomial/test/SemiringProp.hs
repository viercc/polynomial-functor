{-# LANGUAGE QualifiedDo #-}
module SemiringProp where

import Data.Polynomial ( One(..), Plus(..), Times(..), Zero(..) )
import Property
import Control.Applicative (liftA3)
import qualified SemigroupDo

plusAssocProp :: (Plus a, Show a, Eq a) => [a] -> Result
plusAssocProp as =
  label "[assoc-plus] x `plus` (y `plus` z) === x `plus` (y `plus` z)" $
    forAll "(x,y,z)" (liftA3 (,,) as as as) $ \(x,y,z) ->
      x `plus` (y `plus` z) === x `plus` (y `plus` z)

plusCommProp :: (Plus a, Show a, Eq a) => [a] -> Result
plusCommProp as = do
  label "[comm-plus] x `plus` y === y `plus` x" $
    forAll "(x,y)" (liftA2 (,) as as) $ \(x,y) ->
      x `plus` y === y `plus` x

plusZeroProp :: (Plus a, Zero a, Show a, Eq a) => [a] -> Result
plusZeroProp as = do
  label "[plus-zero] x `plus` zero === x" $
    forAll "x" as $ \x -> x `plus` zero === x

timesAssocProp :: (Times a, Show a, Eq a) => [a] -> Result
timesAssocProp as = do
  label "[assoc-times] x `times` (y `times` z) === x `times` (y `times` z)" $
    forAll "(x,y,z)" (liftA3 (,,) as as as) $ \(x,y,z) ->
      x `times` (y `times` z) === x `times` (y `times` z)

timesCommProp :: (Times a, Show a, Eq a) => [a] -> Result
timesCommProp as = do
  label "[comm-times] x `times` y === y `times` x" $
    forAll "(x,y)" (liftA2 (,) as as) $ \(x,y) ->
      x `times` y === y `times` x

timesOneProp :: (One a, Times a, Show a, Eq a) => [a] -> Result
timesOneProp as = do
  label "[times-one] x `times` one === x" $
    forAll "x" as $ \x -> x `times` one === x

distrProp :: (Plus a, Times a, Show a, Eq a) => [a] -> Result
distrProp as = do
  label "[distr-times-plus] x `times` (y `plus` z) === (x `times` y) `plus` (x `times` z)" $
    forAll "(x,y,z)" (liftA3 (,,) as as as) $ \(x,y,z) ->
      x `times` (y `plus` z) === (x `times` y) `plus` (x `times` z)

distrZeroProp :: (Zero a, Times a, Show a, Eq a) => [a] -> Result
distrZeroProp as = do
  label "[distr-times-zero] x `times` zero === zero" $
    forAll "x" as $ \x -> x `times` zero === zero

-- | Commutative semi-semiring
semisemiringProp :: (Eq a, Show a) => (One a, Plus a, Times a) => [a] -> Result
semisemiringProp as = SemigroupDo.do
  plusAssocProp as
  plusCommProp as
  timesAssocProp as
  timesCommProp as
  timesOneProp as
  distrProp as

-- | Commutative semiring
semiringProp :: (Eq a, Show a) => (Zero a, One a, Plus a, Times a) => [a] -> Result
semiringProp as = SemigroupDo.do
  semisemiringProp as
  plusZeroProp as
  distrZeroProp as
