{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Data.InternalCategory(
  -- * Path
  Path(.., Path, EmptyPath, NonEmptyPath),
  -- ** Constructing path
  path, emptyPath, singlePath,
  composePath, (>?>),
  concatPath,

  -- ** Partial construction functions
  errPath,
  errComposePath, (>!>),

  -- ** Sum and Product of paths
  injectLeftPath, injectRightPath,
  separateSumPath,
  fstPath, sndPath,
  
  -- ** Unsafe
  unsafePath,

  -- * Internal categories
  ICategory(..),
  dom, cod,
  identity, compose,

  -- * Reexport
  IQuiver(..),
) where

import Data.InternalQuiver
import Data.Void
import GHC.Stack (HasCallStack)
import Data.Maybe (fromMaybe)
import Control.Applicative ((<|>))


-- * Path
data Path v e = UnsafePath v [e] v
    deriving (Eq, Ord)

instance IQuiver v (Path v e) where
  src (UnsafePath v0 _ _) = v0
  tgt (UnsafePath _ _ v1) = v1

-- Pattern synonyms

pattern Path :: v -> [e] -> v -> Path v e
pattern Path v0 es v1 <- UnsafePath v0 es v1

{-# COMPLETE Path #-}

pattern EmptyPath :: v -> Path v e
pattern EmptyPath v0 <- UnsafePath v0 [] _

pattern NonEmptyPath :: e -> [e] -> Path v e
pattern NonEmptyPath e es <- UnsafePath _ (e:es) _

{-# COMPLETE EmptyPath, NonEmptyPath #-}

-- Safe constructors

path :: (Eq v, IQuiver v e) => v -> [e] -> v -> Maybe (Path v e)
path v0 edges v1
  | valid     = Just $ UnsafePath v0 edges v1
  | otherwise = Nothing
  where
    valid = go v0 edges
    go v []     = v == v1
    go v (e:es) = v == src e && go (tgt e) es

emptyPath :: v -> Path v e
emptyPath v = UnsafePath v [] v

singlePath :: IQuiver v e => e -> Path v e
singlePath e = UnsafePath (src e) [e] (tgt e)

composePath, (>?>) :: Eq v => Path v e -> Path v e -> Maybe (Path v e)
composePath (UnsafePath v0 es v1) (UnsafePath v1' es' v2')
  | v1 == v1' = Just $ UnsafePath v0 (es ++ es') v2'
  | otherwise = Nothing

(>?>) = composePath

infixr 1 >?>

concatPath :: Path v (Path v e) -> Path v e
concatPath (UnsafePath v0 pathes v1) = UnsafePath v0 allEdges v1
  where
    allEdges = pathes >>= \(UnsafePath _ es _) -> es

-- Partial constructors

errPath :: HasCallStack => (Eq v, Show v, IQuiver v e) => v -> [e] -> v -> Path v e
errPath v0 edges v1 = case path v0 edges v1 of
  Nothing -> error errMsg
  Just p -> p
  where
    errMsg = "Unmatched endpoinds in path: " ++ pathTypeStr
    pathTypeStr = go v0 edges
    showExpect v v'
      | v == v'   = show v
      | otherwise = show v ++ " (!!) " ++ show v'
    go v []     = showExpect v v1
    go v (e:es) = showExpect v (src e) ++ " -> " ++ go (tgt e) es

errComposePath, (>!>) :: HasCallStack => (Show v, Eq v) => Path v e -> Path v e -> Path v e
errComposePath p1 p2 = case composePath p1 p2 of
  Nothing -> error errMsg
  Just p -> p
  where
    showType p = show (src p) ++ "->" ++ show (tgt p)
    errMsg = "Unmatched endpoints of two paths: (" ++ showType p1 ++ ") >!> (" ++ showType p2 ++ ")"

(>!>) = errComposePath

infixr 1 >!>

-- ** Sum and product

injectLeftPath :: Path v e -> Path (Either v w) (Either e f)
injectLeftPath (UnsafePath v0 es v1) = UnsafePath (Left v0) (Left <$> es) (Left v1)

injectRightPath :: Path w f -> Path (Either v w) (Either e f)
injectRightPath (UnsafePath w0 fs w1) = UnsafePath (Right w0) (Right <$> fs) (Right w1)

separateSumPath :: Path (Either v w) (Either e f) -> Either (Path v e) (Path w f)
separateSumPath (UnsafePath vw0 edges vw1) = fromMaybe err (leftPath <|> rightPath)
  where
    err = error "should not happen for a valid path"
    getLeft ab  = do { Left a <- Just ab; Just a }
    getRight ab = do { Right b <- Just ab; Just b }
    leftPath = Left <$> (UnsafePath <$> getLeft vw0 <*> traverse getLeft edges <*> getLeft vw1)
    rightPath = Right <$> (UnsafePath <$> getRight vw0 <*> traverse getRight edges <*> getRight vw1)

fstPath :: Path (v,w) (e,f) -> Path v e
fstPath (UnsafePath vw0 edges vw1) = UnsafePath (fst vw0) (fst <$> edges) (fst vw1)

sndPath :: Path (v,w) (e,f) -> Path w f
sndPath (UnsafePath vw0 edges vw1) = UnsafePath (snd vw0) (snd <$> edges) (snd vw1)

-- ** Unsafe path construction

unsafePath :: v -> [e] -> v -> Path v e
unsafePath = UnsafePath


-- * Internal Category

class IQuiver ob mor => ICategory ob mor | mor -> ob where
  foldPath :: Path ob mor -> mor

dom, cod :: ICategory ob mor => mor -> ob
dom = src
cod = tgt

identity :: ICategory ob mor => ob -> mor
identity = foldPath . emptyPath

compose :: (Eq ob, ICategory ob mor) => mor -> mor -> Maybe mor
compose f g = foldPath <$> (singlePath f >?> singlePath g)

---- Instances

-- | @Path@ is the free category
instance ICategory ob (Path ob mor) where
  foldPath = concatPath

-- | Empty graph
instance ICategory Void Void where
  foldPath (Path v _ _) = absurd v

-- | A graph with one vertex and one loop on it
instance ICategory () () where
  foldPath _ = ()

instance (ICategory v e, ICategory w f) => ICategory (Either v w) (Either e f) where
  foldPath p = case separateSumPath p of
    Left leftP   -> Left (foldPath leftP)
    Right rightP -> Right (foldPath rightP)

instance (ICategory v e, ICategory w f) => ICategory (v,w) (e,f) where
  foldPath p = (foldPath (fstPath p), foldPath (sndPath p))