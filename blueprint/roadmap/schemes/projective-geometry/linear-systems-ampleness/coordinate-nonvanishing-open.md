---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Coordinate nonvanishing opens

For the morphism defined by generators `s_0,...,s_n`, the inverse image of
`D_+(x_i)` is the locus `X_{s_i}` where `s_i` generates the line-bundle stalk.
After trivializing by `s_i`, the restricted morphism is induced by
`A[x_j/x_i] -> Gamma(X_{s_i}, O_X)`, sending `x_j/x_i` to `s_j/s_i`.

## Depends on

- [Morphisms from generated invertible sheaves](morphism-from-generated-line-bundle.md)
- [A standard Proj chart is affine](../../projective-spectrum/proj-basic-open.md)

## Proof depends on

- `AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen` and
  `fromOfGlobalSections_morphismRestrict`.

## Sources

- [Hartshorne II.7, proof of Theorem 7.1 (pp.150–151)](../../../../sources/hartshorne-ii-7.md#morphisms-ampleness-and-linear-systems)
