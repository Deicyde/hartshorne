---
article_id: af_81e2ebb7190758fe5ee3491b
declaration: instance
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
mathlib_file: Mathlib/AlgebraicGeometry/StructureSheaf.lean
---

# Sections on a principal open

For `f : A`, the canonical map from `A` to the structure-sheaf sections on
`D(f)` exhibits those sections as the localization away from `f`:

`Γ(D(f), 𝒪_{Spec A}) ≅ A_f`.

The Mathlib instance is the exact universal-property form of Proposition
2.2(b).  Its construction follows Hartshorne's finite principal-open cover and
common-power denominator argument.

## Depends on

- [The Zariski topology on Spec](spec-zero-loci.md)
- [The structure sheaf on Spec](spec-structure-sheaf.md)

## Sources

- [Hartshorne II.2, Proposition 2.2(b) (pp. 71–72)](../../../sources/hartshorne-ii-2.md#structure-sheaf-and-proposition-22)
