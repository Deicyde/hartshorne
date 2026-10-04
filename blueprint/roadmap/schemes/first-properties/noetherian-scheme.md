---
article_id: af_3e20fae8ae51931559b4fa76
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover
mathlib_file: Mathlib/AlgebraicGeometry/Noetherian.lean
---

# Noetherian schemes and finite affine covers

A scheme is Noetherian if and only if it has a finite affine open cover whose
global section rings are Noetherian.

Here `IsNoetherian X` is Mathlib's conjunction of local Noetherianity and
quasi-compactness. A finite affine Noetherian cover supplies both conditions;
conversely quasi-compactness extracts a finite subcover.

## Depends on

- [Locally Noetherian schemes](locally-noetherian.md)

## Proof depends on

- Compactness of affine spectra and finite unions of compact opens.

## Sources

- [Hartshorne II.3 (reduced-integral-and-noetherian-schemes)](../../../sources/hartshorne-ii-3.md#reduced-integral-and-noetherian-schemes)
