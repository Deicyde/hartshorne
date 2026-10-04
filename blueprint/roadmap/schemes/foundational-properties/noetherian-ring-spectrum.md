---
article_id: af_57d2b354da4767c96224d3a6
declaration: instance
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: PrimeSpectrum.instNoetherianSpace
mathlib_file: Mathlib/RingTheory/Spectrum/Prime/Noetherian.lean
---

# Spectra of Noetherian rings are Noetherian

If `A` is a Noetherian commutative ring, then the topological space `Spec A`
is Noetherian.

Every ideal of `A` is finitely generated, so every closed set is cut out by
finitely many elements; equivalently ascending chains of opens stabilize.
This is precisely the forward implication in Exercise 2.13(c).  The stronger
scheme-level equivalence `isNoetherian_Spec` is upstream too, but is not the
main result of this leaf.

## Depends on

- [The Zariski topology on Spec](../spectrum-and-schemes/spec-zero-loci.md)

## Proof depends on

- [Affine schemes are quasi-compact](affine-quasi-compact.md)

## Sources

- [Hartshorne II.2, Exercise 2.13(c) (p. 80), with the local-Noetherian development in II.3 (p. 83)](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
