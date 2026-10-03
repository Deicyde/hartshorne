---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Proj.basicOpenIsoSpec
mathlib_file: Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean
---

# A standard Proj chart is affine

If `f ∈ S_d` is homogeneous of positive degree, then
`D₊(f) = {𝔭 | f ∉ 𝔭}` is open and there is a canonical isomorphism of locally
ringed spaces

`D₊(f) ≅ Spec S_(f)`.

The proof identifies relevant primes avoiding `f` with primes of the
degree-zero away localization and checks the structure sheaves via the
same-degree fractions.  The covering statement is split into its own leaf.

## Depends on

- [The structure sheaf on Proj](proj-structure-sheaf.md)
- [Open subschemes](../spectrum-and-schemes/open-subscheme.md)

## Proof depends on

- [Sections on a principal open](../spectrum-and-schemes/spec-basic-open-sections.md)

## Sources

- [Hartshorne II.2, affine-chart isomorphism in Proposition 2.5(b) (p. 77)](../../../sources/hartshorne-ii-2.md#proj-lemma-24-and-proposition-25)
