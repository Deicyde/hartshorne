---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
---

# Codimension-one classes and the point trace

Let `X` be a nonsingular projective `n`-fold over an algebraically closed
field. The cohomology class `eta(P) in H^n(X,Omega_X^n)` of a closed point
has trace one.

If `Y subset X` is a nonsingular prime divisor, its codimension-one
cohomology class is the logarithmic Picard class:

`eta(Y)=c(O_X(Y)) in H^1(X,Omega_X)`.

## Depends on

- [The dlog Picard cohomology class](dlog-picard-cohomology-class.md)
- [Top cohomology of the canonical sheaf](../../cohomology/serre-duality/duality-applications/canonical-top-cohomology-trace.md)
- [Serre symmetry for differential forms](../../cohomology/serre-duality/duality-applications/serre-hodge-symmetry.md)
- [The invertible sheaf associated to a Cartier divisor](../../schemes/divisors/cartier-picard/cartier-divisor-associated-sheaf.md)

## Proof depends on

- Construct `eta(Y)` by restricting complementary differential forms to
  `Y` and composing with the dualizing trace.
- Compare the connecting cocycle of the divisor with `dlog` of its transition
  functions; the point case fixes the trace normalization.

## Sources

- [Hartshorne III.7, Exercise 7.4(a,d), pp.249–250](../../../sources/hartshorne-iii-7.md#scope-and-exercise-dispositions)
- [Hartshorne V.1, Exercise 1.8(a), pp.367–368](../../../sources/hartshorne-v-1.md#exercise-disposition-printed-pp366368)
