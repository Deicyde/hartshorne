---
declaration: theorem
origin: cited
source_units: [chapter-ii-section-5]
mathlib: true
mathlib_declaration: AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing
mathlib_file: Mathlib/AlgebraicGeometry/Modules/Tilde.lean
---

# Quasi-coherent sections on principal opens

For an `𝒪_{Spec A}`-module `F`, the canonical map
`Γ(Spec A,F)̃ ⟶ F` is an isomorphism exactly when every restriction map
`Γ(Spec A,F) ⟶ Γ(D(f),F)` exhibits the target as localization away from
`f`.  In particular, a quasi-coherent `F` satisfies Hartshorne's Lemma 5.3:

- a global section vanishing on `D(f)` is killed by some power of `f`; and
- after multiplying by a power of `f`, every section on `D(f)` extends
  globally.

The named Mathlib theorem states the localization equivalence; the two source
clauses are its elementwise consequences.

## Depends on

- [Quasi-coherence by local presentations](quasicoherent-local-presentations.md)
- [The affine tilde sheaf and localization](tilde-localization.md)

## Proof depends on

- Affine spectra are quasi-compact, so a local affine presentation cover has a
  finite refinement by principal opens.
- Sections of a sheaf glue when their restrictions agree.

## Sources

- [Hartshorne II.5, Lemma 5.3 on printed p. 112](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
