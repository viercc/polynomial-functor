{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
module Main (main) where

import Control.Monad (guard)
import Data.Functor.Polynomial
import GHC.Generics
import Data.Finitary

main :: IO ()
main = do
    putStrLn "[]"
    guard $ all (\x -> x == roundTrip x) testList

    putStrLn "Generic []"
    guard $ all (\x -> x == genericRoundTrip x) testList

    putStrLn "Generic Maybe"
    guard $ all (\x -> x == genericRoundTrip x) testMaybe

    putStrLn "[] :.: []"
    guard $ all (\x -> x == roundTrip x) testListOfList

    putStrLn "Generic Either"
    guard $ all (\x -> x == genericRoundTrip x) testEither

    putStrLn "->"
    guard $ all (\x -> x `eqFn` roundTrip x) testFn

roundTrip :: Polynomial f => f a -> f a
roundTrip = fromPoly . toPoly

genericRoundTrip :: (Generic1 f, Polynomial (Rep1 f)) => f a -> f a
genericRoundTrip = to1 . roundTrip . from1

testMaybe :: [Maybe Int]
testMaybe = [Nothing, Just 0, Just 1]

testList :: [String]
testList = ["", "foo", "baaaaaaar"]

testListOfList :: [([] :.: []) Char]
testListOfList = Comp1 <$> [testList, [], testList ++ testList]

testEither :: [Either Int Bool]
testEither = [ Left 0, Left 3, Right True ]

testFn :: [ Ordering -> Int ]
testFn = [const 0, \x -> if x == EQ then 1 else 0]

eqFn :: (Finitary x, Eq y) => (x -> y) -> (x -> y) -> Bool
eqFn f g = all (\x -> f x == g x) inhabitants