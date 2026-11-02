---
article_id: af_57d2b354da4767c96224d3a6
declaration: instance
origin: cited
mathlib: true
mathlib_declaration: PrimeSpectrum.instNoetherianSpace
mathlib_file: Mathlib/RingTheory/Spectrum/Prime/Noetherian.lean
---

# Spectra of Noetherian rings are Noetherian

If $A$ is a Noetherian commutative ring, then the topological space $\operatorname{Spec} A$
is Noetherian.

Every ideal of $A$ is finitely generated, so ascending chains of
open subsets of its spectrum stabilize. This is the forward
implication in Hartshorne's Exercise II.2.13(c).

## Depends on

- [The Zariski topology on Spec](../spectrum-and-schemes/spec-zero-loci.md)

## Proof depends on

- [Affine schemes are quasi-compact](affine-quasi-compact.md)

## Sources

- [Hartshorne II.2, Exercise 2.13(c) (p. 80), with the local-Noetherian development in II.3 (p. 83)](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
