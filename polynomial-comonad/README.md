# polynomial-comonad

Implements a correspondence Polynomial Comonads on Set ↔ Small Category, shown in

https://arxiv.org/abs/1604.01187

## `Control.Comonad.Travel`: Category to Polynomial Comonad

```haskell
data Travel cat a where
  MkTravel :: forall k (cat :: k -> k -> Type) (a :: k) (r :: Type).
       Sing a
    -> (Sigma k (TyCon (cat a)) -> r)
    -> Travel cat a

instance Category cat => Comonad (Travel cat)
instance Polynomial (Travel cat)
```

## `Data.InternalCategory.PolyComonad`: Polynomial Comonad to (weakly typed) Category

```haskell
-- | A /quiver/ is a pair of edge type @e@ and vertex type @v@ with
--   functions @src, tgt@ which give source and target vertices of an edge.
class IQuiver v e | e -> v where
  src :: e -> v
  tgt :: e -> v

-- | Path of zero or more edges in a quiver (v,e)
data Path v e

-- | Make a @Path v e@ value from the starting vertex,
--   edges in the path @[e1, e2, ..., en]@, and the final vertex.
--   The validity of the input is checked and only valid path is constructed.
--   @path@ returns @Nothing@ for invalid inputs.
path :: (Eq v, IQuiver v e) => v -> [e] -> v -> Maybe (Path v e)

-- | A /category/ is a quiver in which every path can be concatenated to
--   one edge (morphism) by @foldPath@
class IQuiver ob mor => ICategory ob mor | mor -> ob where
  foldPath :: Path ob mor -> mor
```