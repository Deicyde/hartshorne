---
article_id: af_777bdab39564bd4ef93338be
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.isLocalization_basicOpen_of_qcqs
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean
---

# The qcqs principal-open lemma

Let `U` be a quasi-compact, quasi-separated open of a scheme `X` and
`f ∈ Γ(U,𝒪_X)`.  Define

`U_f = {x ∈ U | f_x ∉ 𝔪_x}`,

where `f_x` is the germ and `𝔪_x` the maximal ideal of the local ring.  This
is the principal open `X.basicOpen f`.  Restriction exhibits its sections as
the localization

`Γ(U_f,𝒪_X) ≅ Γ(U,𝒪_X)_f`.

Mathlib's qcqs theorem is the exact modern packaging of Exercise 2.16(b–d).
Its injectivity clause is the power-torsion statement requiring only
quasi-compactness; surjectivity glues common-power multiples over a finite
affine cover.  The open-locus identity in part (a) is `Scheme.basicOpen`.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)
- [Open subschemes](../spectrum-and-schemes/open-subscheme.md)

## Sources

- [Hartshorne II.2, Exercise 2.16(a–d), used on p. 82 and generalized by Lemma 5.14 on p. 118](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
