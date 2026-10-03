---
declaration: theorem
origin: bridged
source_units: [chapter-v-section-1]
---

# Ampleness on an effective divisor

Let `D` be an effective, possibly singular, reducible, or nonreduced divisor
on a Chapter V surface and put `L=O_X(D)`. If

`D*C>0`

for every irreducible component `C` of `D`, then `L|_D` is ample on the
scheme `D`.

## Depends on

- [Ampleness and reduction](../../../cohomology/projective-cohomology-exercises/ample-iff-on-reduction.md)
- [Ampleness on irreducible components](../../../cohomology/projective-cohomology-exercises/ample-iff-on-irreducible-components.md)
- [Finite-surjective descent of ampleness](../../../cohomology/projective-cohomology-exercises/ample-finite-surjective-descent.md)
- [A curve divisor is ample exactly when its degree is positive](../../../curves/projective-embeddings/linear-series/curve-ample-iff-positive-degree.md)
- [Normalization](../../../schemes/normalization-and-exercises/normalization-construction.md)

## Proof depends on

- Pass from `D` to its reduction, then to irreducible components and their
  finite normalizations. The pulled-back restriction has degree `D*C>0` and
  is therefore ample on each nonsingular normalized curve.

## Sources

- [Hartshorne V.1, restriction step in Theorem 1.10, p.365](../../../../sources/hartshorne-v-1.md)
