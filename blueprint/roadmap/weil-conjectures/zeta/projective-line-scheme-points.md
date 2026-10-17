---
article_id: af_7c2fc3456491984ed097eb91
declaration: equivalence
origin: bridged
source_units: [appendix-c-section-1]
---

# Scheme-valued points of the projective line

For a field extension `k → K`, the `K`-valued points of the relative
projective line over `k`, namely morphisms

`Spec K → P^1_k`

over `Spec k`, are naturally equivalent to one-dimensional quotients of
`K²`. Dualizing a quotient line gives a line in `(K²)∨`; the standard basis
identifies `(K²)∨` with `Fin 2 → K`, yielding an equivalence with
`Projectivization K (Fin 2 → K)`.

This is the representation bridge between Hartshorne's scheme-valued point
count and Mathlib's classical projectivization. Counting homogeneous
coordinate tuples without this equivalence does not prove the scheme-valued
statement.

## Depends on

- [Morphisms from generated invertible sheaves](../../schemes/projective-geometry/linear-systems-ampleness/morphism-from-generated-line-bundle.md)
- [Projective space](../../projective-varieties/projective-space.md)
- [Affine quasi-coherent equivalence](../../schemes/modules-and-quasicoherent/affine-quasicoherent-equivalence.md)

## Proof depends on

- The relative-projective-space functor of points specialized to an invertible
  sheaf with two ordered generators on `Spec K`.
- Standard-basis self-duality for `K²`, converting one-dimensional quotients
  into Mathlib's projective lines.

## Sources

- [Hartshorne Appendix C.1, scheme-valued point counts and the projective-line example (pp. 449–450)](../../../sources/hartshorne-appendix-c-1.md#point-counts-and-the-formal-zeta-series-printed-pp449450)
- [Hartshorne II.7, projective-bundle functor of points](../../../sources/hartshorne-ii-7.md#relative-proj-and-projective-bundles)
