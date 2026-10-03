---
declaration: theorem
origin: bridged
source_units: [chapter-v-section-1]
---

# The globally generated morphism is finite

Let `D` be a divisor with `D*C>0` for every irreducible curve `C`, and assume
some positive power `L^n=O_X(nD)` is globally generated. The associated
projective morphism

`phi : X -> P^N`

has finite fibres and is therefore finite onto its scheme-theoretic image.

## Depends on

- [Morphisms from generated invertible sheaves](../../../schemes/projective-geometry/linear-systems-ampleness/morphism-from-generated-line-bundle.md)
- [Projective quasi-finite morphisms are finite](../../../cohomology/formal-functions/applications/projective-quasifinite-finite.md)
- [The scheme-theoretic image](../../../schemes/subschemes-and-dimension/scheme-theoretic-image.md)

## Proof depends on

- A positive-dimensional fibre would contain an irreducible curve `C`.
  Pulling back a hyperplane missing its image point gives an effective divisor
  linearly equivalent to `nD` and disjoint from `C`, contradicting `D*C>0`.

## Sources

- [Hartshorne V.1, finite-morphism step in Theorem 1.10, p.366](../../../../sources/hartshorne-v-1.md)
