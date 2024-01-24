{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
module Main where

import Data.Polynomial.Functor
import Data.Polynomial.Functor.Deriving
import GHC.Generics (Generic1, Generically1(..))
import Data.Foldable (for_)
import Data.Traversable (mapAccumL)

--- Example

data Example a = Ex (Maybe a) (Maybe a)
   deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
   deriving PolynomialFunctor via (Generically1 Example)
   deriving Applicative via (ViaPolynomial Zippy Example)

data Example' a = A a (Maybe a) | B (Maybe a) a
   deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
   deriving PolynomialFunctor via (Generically1 Example')
   deriving (Applicative, Monad) via (ViaPolynomial Aligney Example')

main :: IO ()
main = do
  mainExample
  mainExample'

mainExample :: IO ()
mainExample = do
  putStrLn "== Example =="
  putStrLn "toPoly:"
  for_ testData $ \fa -> do
    let pa = toPoly fa
    putStrLn $ "  toPoly (" ++ show fa ++ ") = " ++ show pa
  putStrLn "pure:"
  putStrLn $ "  pure 0 = " ++ show (pure @Example (0 :: Int))
  putStrLn "(<*>):"
  for_ testData $ \fa ->
    for_ testData $ \fb ->
      putStrLn $ "  g <$> (" ++ show fa ++ ") <*> (" ++ show fb ++ ") = " ++ show (g <$> fa <*> fb)
  putStrLn "    where g a b = 10 * a + b"
  where
    testData = ixes <$> genExample [()]
    g a b = 10 * a + b

genExample :: [a] -> [Example a]
genExample as = Ex <$> genMaybe <*> genMaybe
  where
    genMaybe = Nothing : (Just <$> as)

mainExample' :: IO ()
mainExample' = do
  putStrLn "== Example' =="
  putStrLn "toPoly:"
  for_ testData $ \fa -> do
    let pa = toPoly fa
    putStrLn $ "  toPoly (" ++ show fa ++ ") = " ++ show pa
  putStrLn "pure:"
  putStrLn $ "  pure 0 = " ++ show (pure @Example' (0 :: Int))
  putStrLn "(<*>):"
  for_ testData $ \fa ->
    for_ testData $ \fb ->
      putStrLn $ "  g <$> (" ++ show fa ++ ") <*> (" ++ show fb ++ ") = " ++ show (g <$> fa <*> fb)
  putStrLn "    where g a b = 10 * a + b"
  where
    testData = ixes <$> genExample' [()]
    g a b = 10 * a + b

genExample' :: [a] -> [Example' a]
genExample' as = genA ++ genB
  where
    genA = A <$> as <*> genMaybe
    genB = B <$> genMaybe <*> as
    genMaybe = Nothing : (Just <$> as)

ixes :: Traversable t => t () -> t Int
ixes = snd . mapAccumL (\s _ -> (1 + s, 1 + s)) 0
