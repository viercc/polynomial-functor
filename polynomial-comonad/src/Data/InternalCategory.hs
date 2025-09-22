{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.InternalCategory(
  -- * Internal categories
  ICategory(..),
  -- * Path
  Path(Path, EmptyPath, NonEmptyPath),
  dom, cod, (>?>),

  -- * Reexport
  IQuiver(..),
) where

import Data.InternalQuiver
import Data.Void
import Data.Bifunctor (Bifunctor(..))

import Data.InternalQuiver.Path

-- * Internal Category

{- | @ICategory ob mor@ defines a category "internal to" @Type@.

There are two ways to define @ICategory@: with 'identity' and 'compose' or with 'foldPath'.

==== Definition by @'identity', 'compose'@

This is how internal categories are usually defined: by giving identity morphisms
and composition of two morphisms, satisfying the following laws:

/Domain and codomain of @identity v@/:

    @
    dom (identity v) == cod (identity v) == v
    @

/@compose@ is defined exactly on matching morphisms/:

    @
    isJust (compose f g) == (cod f == dom g)
    @

/Domain and codomain of @compose f g@/:


    For all @f,g,h@ such that @compose f g == Just h@,
    
    @
    dom h == dom f, cod h == cod g
    @

/Left and Right Unit/:

    @
    identity (dom f) `compose` f == Just f
    @

    @
    f `compose` identity (cod f) == Just f
    @

/Associativity/:

    For all @f,g,h@,

    @
    (compose f g >>= \fg -> compose fg h)
      ==
    (compose g h >>= \gh -> compose f gh)
    @

Given @identity@ and @compose@ operation, @foldPath p@
can be defined as the composition @morAll@ of all morphisms in @p@
(and the identity at source in a case of empty path,) which
is guaranteed to be @Just morAll@ and not @Nothing@.

==== Definition by @'foldPath'@:

This is an alternative definition by giving how to collapse any path on
@IQuiver ob mor@ into @mor@, satisfying the following laws.

/folding doesn't change endpoints/:

    @
    dom (foldPath p) == dom p
    @

    @
    cod (foldPath p) == cod p
    @

/folding commutes with 'concatPath'/:

    For any @pp :: Path ob (Path ob mor)@,

    @
    foldPath (concatPath pp) = foldPath (errMapPath id foldPath pp)
    @

    Note that from /folding doesn't change endpoints/ law,
    @errMapPath id foldPath@ must be a total function.

/folding single edge does nothing/:

    @
    foldPath (singlePath f) = f
    @

Given @foldPath@, one can defined @identity@ and @compose@ satisfying
the laws above, as

@
identity :: ob -> mor
identity = foldPath . emptyPath

compose :: mor -> mor -> Maybe mor
compose f g = foldPath <$> composePath (singlePath f) (singlePath g)
@

-}
class (IQuiver ob mor, Eq ob) => ICategory ob mor | mor -> ob where
  {-# MINIMAL foldPath | identity, compose #-}

  foldPath :: Path ob mor -> mor
  foldPath p = case p of
    EmptyPath v0 -> identity v0
    NonEmptyPath e es -> loop e es
    where
      loop e [] = e
      loop e (e':rest) = case compose e e' of
        Nothing -> error "Invalid Path"
        Just e'' -> loop e'' rest

  identity :: ob -> mor
  identity = foldPath . emptyPath

  compose :: mor -> mor -> Maybe mor
  compose f g = foldPath <$> composePath (singlePath f) (singlePath g)

dom, cod :: ICategory ob mor => mor -> ob
dom = src
cod = tgt

infixr 1 >?>
(>?>) :: ICategory ob mor => mor -> mor -> Maybe mor
(>?>) = compose

---- Instances

-- | @Path@ is the free category
instance Eq ob => ICategory ob (Path ob mor) where
  foldPath = concatPath
  identity = emptyPath
  compose = composePath

-- | Empty graph
instance ICategory Void Void where
  foldPath (Path v _ _) = absurd v
  identity = absurd
  compose = absurd

-- | A graph with one vertex and one loop on it
instance ICategory () () where
  foldPath _ = ()
  identity _ = ()
  compose _ _ = Just ()

-- | Coproduct of category
instance (ICategory v e, ICategory w f) => ICategory (Either v w) (Either e f) where
  foldPath p = case separateSumPath p of
    Left leftP   -> Left (foldPath leftP)
    Right rightP -> Right (foldPath rightP)
  
  identity = bimap identity identity
  compose (Left f) (Left g) = Left <$> compose f g
  compose (Right f) (Right g) = Right <$> compose f g
  compose _ _ = Nothing

-- | Product of category
instance (ICategory v e, ICategory w f) => ICategory (v,w) (e,f) where
  foldPath p = (foldPath (fstPath p), foldPath (sndPath p))
  identity (v,w) = (identity v, identity w)
  compose (f,f') (g,g') = (,) <$> compose f g <*> compose f' g'

