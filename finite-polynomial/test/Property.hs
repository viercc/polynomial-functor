{-# LANGUAGE RankNTypes #-}
module Property where

import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)

import Enum1

type FailureMessage = [String]
data Result = Failure FailureMessage | Success

instance Semigroup Result where
  x@(Failure _) <> _ = x
  Success <> y = y

instance Monoid Result where
  mempty = Success

label :: String -> Result -> Result
label str res = case res of
  Failure message -> Failure (str : message)
  Success -> Success

(===) :: (Show a, Eq a) => a -> a -> Result
x === y = if x == y then Success else Failure errMsg
  where
    errMsg = ["Failure:", "  " ++ show x, "    ===", "  " ++ show y]

infix 1 ===

forAll :: (Show a) => String -> [a] -> (a -> Result) -> Result
forAll varName as prop = foldr (<>) Success
  [ label (varName ++ " = " ++ show a ++ ";") (prop a) | a <- as ]

property :: Result -> IO ()
property (Failure message) = hPutStrLn stderr (unlines message) >> exitFailure
property Success = pure () 

isIsomorphism :: (Traversable f, Traversable g, Show (f Int), Show (g Int), Eq (f Int), Eq (g Int))
  => Enum1 f -> Enum1 g
  -> (forall x. f x -> g x) -> (forall x. g x -> f x)
  -> Result
isIsomorphism genF genG fg gf =
     forAll "fx" (skolem genF) (\x -> gf (fg x) === x)
  <> forAll "gx" (skolem genG) (\y -> fg (gf y) === y)
