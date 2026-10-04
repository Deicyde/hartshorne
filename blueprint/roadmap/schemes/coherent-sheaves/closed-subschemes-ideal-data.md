---
article_id: af_2cd51eb72c8dad4f900eb463
declaration: equivalence
origin: cited
source_units: [chapter-ii-section-5]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsClosedImmersion.overEquivIdealSheafData
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean
---

# Closed subschemes and ideal data

For a scheme `X`, closed immersions into `X`, up to isomorphism over `X`, are
contravariantly equivalent to `X.IdealSheafData`. The subscheme attached to
`I` is locally `Spec(Γ(X,U)/I(U))`, and its inclusion has kernel data exactly
`I`.

Together with the module/data bridge, this gives Hartshorne's unique closed
subscheme associated to a quasi-coherent ideal sheaf. For affine `X = Spec A`
it specializes to the correspondence between ideals of `A` and closed
subschemes of `X`.

## Depends on

- [Module ideal sheaves and ideal data](module-ideal-sheaf-data.md)
- [Affine closed subschemes](../subschemes-and-dimension/affine-closed-subschemes.md)

## Sources

- [Hartshorne II.5, Proposition 5.9 and Corollary 5.10 (p.116)](../../../sources/hartshorne-ii-5.md#ideal-sheaves-and-closed-subschemes)
