---
article_id: af_a3a60a624675778f44a80899
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
not_ready: true
---

# Sheaf cohomology and the Ext model

For an abelian sheaf `F` on a topological space `X`, define Hartshorne
cohomology by `RⁿΓ(X,F)`. Construct natural isomorphisms between this model and
Mathlib's `CategoryTheory.Sheaf.H F n`, defined as Ext from the constant
integral sheaf, and identify degree zero with global sections.

The unique main result is a natural isomorphism of graded functors between
Hartshorne's `RⁿΓ(X,-)` and Mathlib's Ext model. It must be induced from the
degree-zero natural isomorphism `Hom(Z_X,F) ≅ Γ(X,F)` and be compatible with
connecting maps. `Sheaf.H`, `Sheaf.functorH`, `Sheaf.H.map`, and `Sheaf.H.equiv₀` in
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` are exact pinned
primitives, not a definitional identification with `RΓ`. This node remains
not ready until that derived comparison is specified against Mathlib's two
constructions.

## Depends on

- [Abelian sheaves have enough injectives](abelian-sheaves-enough-injectives.md)
- [Right derived functors](../derived-functors/right-derived-functors.md)
- [Global sections are left exact](../../schemes/sheaf-functors/global-sections-left-exact.md)

## Sources

- [Hartshorne III.2, definition of sheaf cohomology, printed p. 207](../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)
