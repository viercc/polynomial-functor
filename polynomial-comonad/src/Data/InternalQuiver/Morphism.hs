{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.InternalQuiver.Morphism where

import Data.InternalQuiver
import Data.Void

-- | A type which can be interpreted as a collection of
--   morphisms between quivers.
-- 
-- A morphism @f :: fun@ must preserve @src@ and @tgt@.
-- For all edge @e0 :: e@ in the source quiver, the following two equations
-- must hold.
-- 
-- @
-- vertexMap f (src e0) = src (edgeMap f e0)
-- vertexMap f (tgt e0) = tgt (edgeMap f e0)
-- @
class (IQuiver v e, IQuiver v' e') => IQuiverMorphism v e v' e' fun | fun -> e e' where
  vertexMap :: fun -> v -> v'
  edgeMap :: fun -> e -> e'

-- | Identity morphism
data IdFun e = Id
  deriving (Eq, Ord, Show, Read)

instance (IQuiver v e) => IQuiverMorphism v e v e (IdFun e) where
  vertexMap _ = id
  edgeMap _ = id

-- | Terminal morphism
data TerminalFun e = Terminal
  deriving (Eq, Ord, Show, Read)

instance (IQuiver v e) => IQuiverMorphism v e () () (TerminalFun e) where
  vertexMap _ _ = ()
  edgeMap _ _ = ()

-- | Initial morphism
data AbsurdFun e = Absurd
  deriving (Eq, Ord, Show, Read)

instance (IQuiver v e) => IQuiverMorphism Void Void v e (AbsurdFun e) where
  vertexMap _ = absurd
  edgeMap _ = absurd

-- | Injection into sum (first component)
data Inj1Fun e e' = Inj1
  deriving (Eq, Ord, Show, Read)

instance (IQuiver v e , IQuiver v' e')
  => IQuiverMorphism v e (Either v v') (Either e e') (Inj1Fun e e') where
  vertexMap _ = Left
  edgeMap _ = Left

-- | Injection into sum (second component)
data Inj2Fun e e' = Inj2
  deriving (Eq, Ord, Show, Read)

instance (IQuiver v e , IQuiver v' e')
  => IQuiverMorphism v' e' (Either v v') (Either e e') (Inj2Fun e e') where
  vertexMap _ = Right
  edgeMap _ = Right

data CopairFun fun1 fun2 = Copaired fun1 fun2
  deriving (Eq, Ord, Show, Read)

instance (IQuiverMorphism v1 e1 w f fun1, IQuiverMorphism v2 e2 w f fun2)
  => IQuiverMorphism (Either v1 v2) (Either e1 e2) w f (CopairFun fun1 fun2) where
    vertexMap (Copaired f1 f2) = either (vertexMap f1) (vertexMap f2)
    edgeMap (Copaired f1 f2) = either (edgeMap f1) (edgeMap f2)