---
article_id: af_7d438e5682951dd9d44615d5
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.projectiveSpaceOverSchemeProjection_isProper
---

# Projective space is proper

For every Noetherian scheme `Y` and every `n`, the projection
`ℙⁿ_Y ⟶ Y` is proper. In fact, the pinned Mathlib proof of the `Proj`
structure morphism and stability under base change remove the unnecessary
Noetherian restriction once relative projective space has been identified with
the corresponding base change.

First identify `ℙⁿ_ℤ` with `Proj ℤ[x₀,…,xₙ]`. The polynomial ring is a
finite-type graded algebra generated in degree one, so Mathlib's
`Proj.valuativeCriterion_existence` and `Proj.toSpecZero` proper instance apply.
Base-change properness along `Y ⟶ Spec ℤ` and the defining pullback
isomorphism give the result over `Y`.

## Depends on

- [Projective space over a scheme](projective-space-over-scheme.md)
- [Proper morphisms](proper-morphism.md)

## Proof depends on

- [Proper-morphism calculus](proper-morphism-calculus.md)
- [Projective space over a ring](../projective-spectrum/projective-space-over-ring.md)
- `AlgebraicGeometry.Proj.valuativeCriterion_existence` and the proper
  `Proj.toSpecZero` instance from
  `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`.

## Sources

- [Hartshorne II.4, proof of Theorem 4.9](../../../sources/hartshorne-ii-4.md#projective-morphisms)
