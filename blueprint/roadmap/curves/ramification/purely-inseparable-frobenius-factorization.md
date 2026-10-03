---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Purely inseparable curve maps are iterated Frobenius

Let `f : X -> Y` be a finite morphism of curves over an algebraically closed
field of characteristic `p>0`. If `K(X)/K(Y)` is purely inseparable of degree
`p^r`, then `f`, after the function-field-model identification of its source,
is the composite of `r` Hartshorne-oriented `k`-linear Frobenius morphisms

`Y^(p^r) -> ... -> Y^p -> Y`.

Equivalently, `X` is isomorphic to `Y^(p^r)` as a `k`-scheme compatibly with
the maps to `Y`.

## Depends on

- [Degree of Frobenius on a curve](curve-frobenius-finite-degree.md)
- [The curve/function-field category equivalence](../../projective-models/curve-category-equivalence.md)

## Proof depends on

- If the extension degree is `p^r`, then
  `K(X)^(p^r) subset K(Y)` and comparison with `K(Y)^(1/p^r)` forces equality
  by degree.
- The complete nonsingular curve model of a one-dimensional function field is
  unique.

## Sources

- [Hartshorne IV.2, Proposition 2.5, p.302](../../../sources/hartshorne-iv-2.md#frobenius-and-purely-inseparable-maps-pp301302)
- [Stacks Project, iterated relative Frobenius, tag 0CCZ](../../../sources/hartshorne-iv-2.md#external-proof-sources)
