---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Divisor pushforward descends to Picard groups

For a finite morphism `f : X -> Y` of curves of degree `n`, divisor
pushforward preserves linear equivalence. It therefore induces a norm
homomorphism

`f_* : Pic X -> Pic Y`.

Together with divisor pullback, its composite on `Pic Y` is multiplication
by `n`:

`f_* (f^* L) = L^n`.

No duality formula or branch-divisor determinant formula from Exercise
2.6(c,d) is asserted.

## Depends on

- [Determinants and pushforward of curve divisors](finite-curve-divisor-pushforward-determinant.md)
- [Pullback of divisors along finite curve morphisms](../../schemes/divisors/curve-divisors/finite-curve-divisor-pullback.md)
- [Degree of a pulled-back curve divisor](../../schemes/divisors/curve-divisors/finite-curve-pullback-degree.md)
- [Pullback of divisor sheaves](../../schemes/divisors/divisor-exercises/pullback-divisor-sheaf-compatibility.md)

## Proof depends on

- The determinant formula sends principal divisors to trivial classes.
- For a closed point of `Y`, the sum of ramification indices in its pullback
  equals `n` because all residue degrees are one.

## Sources

- [Hartshorne IV.2, Exercise 2.6(b), p.306](../../../sources/hartshorne-iv-2.md#exercise-disposition-pp304306)
