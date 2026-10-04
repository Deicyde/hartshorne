---
article_id: af_137da62c2d76dfe275e505db
declaration: abbrev
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.GlueData.glued
mathlib_file: Mathlib/AlgebraicGeometry/Gluing.lean
---

# Gluing schemes

Given schemes `Xᵢ`, open subschemes `Uᵢⱼ ⊆ Xᵢ`, inverse transition
isomorphisms satisfying the triple-overlap cocycle, there is a scheme `X`
with open immersions `Xᵢ → X` that cover `X` and identify precisely along the
specified overlaps.

This is the family form of Example 2.3.5 and Exercise 2.12.  Mathlib constructs
`Scheme.GlueData.glued` as a multicoequalizer; `ι_isOpenImmersion`,
`ι_jointly_surjective`, and `vPullbackConeIsLimit` give the source clauses.

## Depends on

- [Open subschemes](open-subscheme.md)

## Sources

- [Hartshorne II.2, Example 2.3.5 and Exercise 2.12 (pp. 75, 80)](../../../sources/hartshorne-ii-2.md#schemes-and-gluing)
