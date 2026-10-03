---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# The normalization morphism is dominant

For an integral scheme `X`, the normalization morphism `ν : X̃ → X` is
dominant.

On each affine chart the coordinate-ring map into its integral closure inside
`K(X)` is injective, so the induced map on spectra has dense image. These local
dense-image statements glue. The pinned relative-normalization API has an
`IsDominant toNormalization` instance, but the absolute orientation here still
requires the source-shaped wrapper.

## Depends on

- [Construction of the normalization](normalization-construction.md)

## Proof depends on

- Injectivity of integral-closure inclusions and density of the induced affine
  spectrum maps.

## Sources

- [Hartshorne II.3, Exercise 3.8 (p. 91)](../../../sources/hartshorne-ii-3.md#later-used-exercises)

