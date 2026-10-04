---
article_id: af_3f1a47b905324050aaee2347
declaration: lemma
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsSeparated.of_isAffineHom
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/Separated.lean
---

# Affine morphisms are separated

Every affine morphism of schemes is separated. In particular, every morphism
between affine schemes is separated, as in Proposition 4.1.

Over an affine target, identify the source and the fiber square with spectra.
The diagonal corresponds to the multiplication map
`A ⊗[B] A → A`, which is surjective, so its spectrum is a closed
immersion. Target-locality extends the result to every affine morphism.

## Depends on

- [Separated morphisms](separated-morphism.md)

## Proof depends on

- [Fiber products of affine schemes](../fiber-products/affine-fiber-product.md)
- [Closed subschemes of an affine scheme](../subschemes-and-dimension/affine-closed-subschemes.md)
- Surjectivity of the tensor-product multiplication map.

## Sources

- [Hartshorne II.4, Proposition 4.1](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)
