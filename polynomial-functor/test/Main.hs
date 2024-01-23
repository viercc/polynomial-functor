{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Main (main) where

import Control.Monad (guard)
import Data.Functor.Polynomial
import GHC.Generics
import Data.Finitary

main :: IO ()
main = do

    putStrLn "[]"
    guard $ all (\x -> x == roundTrip x) testList
    mapM_ (putStrLn . showPoly . toPoly) testList

    putStrLn "Maybe"
    guard $ all (\x -> x == roundTrip x) testMaybe
    mapM_ (putStrLn . showPoly . toPoly) testMaybe

    putStrLn "[] :.: []"
    guard $ all (\x -> x == roundTrip x) testListOfList
    mapM_ (putStrLn . showPoly . toPoly) testListOfList

    putStrLn "Either"
    guard $ all (\x -> x == roundTrip x) testEither
    mapM_ (putStrLn . showPoly . toPoly) testEither

    putStrLn "->"
    guard $ all (\x -> x `eqFn` roundTrip x) testFn
    mapM_ (putStrLn . showPoly . toPoly) testFn

    putStrLn "Generic F"
    guard $ all (\x -> x == genericRoundTrip x) testF
    mapM_ (putStrLn . showPoly . toPoly . from1) testF

    print $ [ x == y | x <- testF, y <- testF ]

showPoly :: (forall n. Show (tag n), HasSNat tag, Show x) => Poly tag x -> String
showPoly (P tag rep) = "P{ tag = " ++ show tag ++ ", repList=" ++ repStr ++"}"
  where
    repStr = case toSNat tag of SNat -> show (map rep inhabitants)

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

newtype F a = F (Bool -> Bool -> Maybe a)
    deriving (Generic1, Functor)

instance Eq a => Eq (F a) where
    F f == F g = and [ f x y == g x y | x <- [ False, True ], y <- [False, True]]

testF :: [F String]
testF = F <$> [f1, f2, f3, f4]
  where
    f1 _ _ = Nothing
    
    f2 True _ = Just "foo"
    f2 False _ = Nothing

    f3 _ True = Just "bar"
    f3 _ False = Nothing

    f4 x y | x == y = Just (if x then "baz" else "quux")
           | otherwise = Nothing
