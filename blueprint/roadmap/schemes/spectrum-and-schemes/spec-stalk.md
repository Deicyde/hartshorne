---
article_id: af_583dcab868656eea7ba3f8e6
declaration: abbrev
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.StructureSheaf.stalkIso
mathlib_file: Mathlib/AlgebraicGeometry/StructureSheaf.lean
---

# The stalk of Spec

For `𝔭 ∈ Spec A`, evaluation of a local section at `𝔭` induces an
`A`-algebra isomorphism

`𝒪_{Spec A,𝔭} ≅ A_𝔭`.

Surjectivity represents a fraction on a principal neighbourhood.  Injectivity
uses equality in the localization to shrink to a neighbourhood on which two
representatives agree.  This is Hartshorne Proposition 2.2(a), realized by
`StructureSheaf.stalkIso` and the instance
`StructureSheaf.IsLocalization.to_stalk`.

## Depends on

- [The structure sheaf on Spec](spec-structure-sheaf.md)

## Sources

- [Hartshorne II.2, Proposition 2.2(a) (p. 71)](../../../sources/hartshorne-ii-2.md#structure-sheaf-and-proposition-22)
