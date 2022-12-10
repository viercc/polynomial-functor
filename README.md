# polynomia-functor

This package provides a way to express, construct, and inspect polynomial functors in Haskell.
The first example is `Maybe`.

```haskell
data Maybe a = Nothing | Just a
```

As a polynomial functor, `Maybe` is a sum of zero-parameter term (`= Proxy`) and single-parameter (`= Identity`) term.
Because `Proxy a` is isomorphic to `Void -> a` and `Identity` is ismorphic to `() -> a`.

```haskell
data Maybe' a = NothingCase (Void -> a) | JustCase (() -> a)
```

For another example, the list functor `[]` is a sum of 0,1,2,... tuples of the parameter type.
In other words, using `Finite` n type which `Finite 0, Finite 1, Finite 2, ...` are the type with exactly `0, 1, 2, ...` values,
`[]` have a representation as a polynomial functor:

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

This package provides `Poly` type.
Any polynomial functor with all finite exponent is isomorphic to `Poly tag` for some `tag :: Nat -> Type`.

```haskell
type Poly :: (Nat -> Type) -> Type -> Type
data Poly tag x where
  P :: tag n -> (Finite n -> x) -> Poly tag x
```

`Poly` supports operations definable on a polynomial functor.

* `Poly tag` is always `Foldable` and `Traversable`
* `Eq (Poly tag x)` instance, using equality test on tag (`GEq tag`) and on parameter (`Eq x`)
* `Ord (Poly tag x)` similarly

This package also provides `Polynomial` type class.
`Polynomial f` associates a polynomial functor `f` to its representation, `Tag f` type,
such that `f` is isomorphic to `Poly (Tag f)` as a `Functor`.
