# polynomial-functor

This package provides a way to express, construct, and inspect polynomial functors in Haskell.

The first example of polynomial functor is `Maybe`.

```haskell
data Maybe a = Nothing | Just a
```

`Maybe a` can be seen as a sum of zero-tuple of `a` (`= Proxy`) and 1-tuple of `a` (`= Identity`) term.

```haskell
data Maybe' a = NothingCase (Proxy a) | JustCase (Identity a)
```

Because `Proxy a` is isomorphic to `Void -> a` and `Identity` is ismorphic to `() -> a`,
it can be written even more uniformly as below.

```haskell
data Maybe'' a = VoidCase (Void -> a) | UnitCase (() -> a)
```

For another example, the list functor `[]` is a sum of 0,1,2,... tuples of the parameter type.
In other words, using `Finite n` type which `Finite 0, Finite 1, Finite 2, ...` are the type with exactly `0, 1, 2, ...` values,
`[]` have a representation as a polynomial functor below.

```haskell
data List' a =
      List0 (Finite 0 -> a)
    | List1 (Finite 1 -> a)
    | List2 (Finite 2 -> a)
        :
        :          
```

Generally, a polynomial functor is a sum of some functors,
where each of the summed functor is isomorphic to `r -> ??` functor with some exponent `r`.

This package provides `Poly` type below, to represent general polynomial functors.

```haskell
type Poly :: (Type -> Type) -> Type -> Type
data Poly tag x where
  P :: tag a -> (a -> x) -> Poly tag x
```

`Poly` supports operations definable on a polynomial functor.

* `Poly tag` is `Foldable` and `Traversable` if every inhabited `tag a` value witnesses
  `Finitary a`.
* `Eq (Poly tag x)` instance, using equality test on tag (`GEq tag`) and on parameter (`Eq x`)
* `Ord (Poly tag x)` similarly

This package also provides `Polynomial` type class.
`Polynomial f` associates a polynomial functor `f` to its representation, `Tag f` type,
such that `f` is isomorphic to `Poly (Tag f)` as a `Functor`.
