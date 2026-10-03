---
declaration: theorem
origin: cited
source_units: [chapter-v-section-1]
---

# The Nakai–Moishezon criterion

A divisor `D` on a Chapter V surface is ample if and only if

`D^2>0`

and `D*C>0` for every irreducible curve `C` on the surface.

The statement and Hartshorne's algebraic proof are valid over an
algebraically closed field of arbitrary characteristic.

## Depends on

- [Necessity of the numerical conditions](nakai-necessity.md)
- [Positive square gives eventual effectivity](../surface-riemann-roch/positive-square-eventual-effectivity.md)
- [Ampleness on an effective divisor](ample-restriction-effective-divisor.md)
- [Cohomology stabilization and global generation](h1-stabilization-global-generation.md)
- [The globally generated morphism is finite](globally-generated-morphism-finite.md)
- [Simultaneous Bertini moving](../../intersection-theory/foundations/simultaneous-bertini-moving.md)
- [Finite-surjective descent of ampleness](../../../cohomology/projective-cohomology-exercises/ample-finite-surjective-descent.md)
- [Ampleness and tensor powers](../../../schemes/projective-geometry/linear-systems-ampleness/ample-power-equivalence.md)

## Proof depends on

- Represent a very ample class by an irreducible curve to obtain `D*H>0`,
  then replace `D` by an effective positive multiple using eventual effectivity.
  The restriction, global-generation, and finiteness leaves produce a finite
  morphism with `O_X(nD)` pulled back from `O(1)` on its image; finite pullback
  preserves ampleness, and ampleness descends from the positive tensor power.

## Sources

- [Hartshorne V.1, Theorem 1.10, pp.365–366](../../../../sources/hartshorne-v-1.md)
- Nakai, *A criterion of an ample sheaf on a projective scheme*.
- Moishezon, *A criterion for projectivity of complete algebraic abstract varieties*.
