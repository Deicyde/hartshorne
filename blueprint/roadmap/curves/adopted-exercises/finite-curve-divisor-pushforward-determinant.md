---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Determinants and pushforward of curve divisors

Let `f : X -> Y` be a finite morphism of curves of degree `n`. Define
pushforward on divisors by

`f_*(sum_P n_P P) = sum_P n_P f(P)`.

For every divisor `D` on `X`, the finite direct image `f_*O_X(D)` is locally
free of rank `n`, and there is a natural isomorphism

`det(f_*O_X(D)) ~= det(f_*O_X) tensor O_Y(f_*D)`.

This is divisor pushforward from `X` to `Y`, not the ramification-weighted
divisor pullback in the opposite direction.

## Depends on

- [Determinant on the Grothendieck group of a curve](../../schemes/divisors/divisor-exercises/determinant-on-curve-k-group.md)
- [Finite morphisms](../../schemes/first-properties/finite-morphism.md)
- [Pullback of divisors along finite curve morphisms](../../schemes/divisors/curve-divisors/finite-curve-divisor-pullback.md)
- [Degree and flatness of a finite curve morphism](../ramification/finite-curve-morphism-flat-degree.md)

## Proof depends on

- Finite morphisms of nonsingular curves are flat, so finite pushforward of an
  invertible sheaf is finite locally free.
- Apply finite pushforward to the divisor skyscraper sequence and use
  additivity of determinant.

## Sources

- [Hartshorne IV.2, Exercise 2.6(a), p.306](../../../sources/hartshorne-iv-2.md#exercise-disposition-pp304306)
