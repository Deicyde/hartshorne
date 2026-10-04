---
article_id: af_faa6bf29767e5c33aab9ef74
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover
mathlib_file: Mathlib/AlgebraicGeometry/Noetherian.lean
---

# Noetherianity is local on affine opens

If `X` is locally Noetherian, every affine open `U = Spec A` has `A` Noetherian. In particular, `Spec A` is a Noetherian scheme if and only if `A` is a Noetherian ring.

Refine the given cover on `U` by finitely many principal opens `D(fᵢ)`. Their rings are Noetherian localizations, and the elements `fᵢ` generate the unit ideal. Descend stabilization of ideal chains from all `A_{fᵢ}` to `A`.

## Depends on

- [Locally Noetherian schemes](locally-noetherian.md)
- [Noetherian schemes and finite affine covers](noetherian-scheme.md)

## Proof depends on

- The localization descent lemma `isNoetherianRing_of_away`.

## Sources

- [Hartshorne II.3 (reduced-integral-and-noetherian-schemes)](../../../sources/hartshorne-ii-3.md#reduced-integral-and-noetherian-schemes)
