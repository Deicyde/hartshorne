---
article_id: af_7f970480f09db79d7e43f026
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
mathlib_file: Mathlib/RingTheory/Spectrum/Prime/Topology.lean
---

# Dimension of an affine scheme

For every commutative ring `A`, the topological dimension of `Spec A` equals the Krull dimension of `A`.

Transport topological Krull dimension along the canonical homeomorphism from the affine scheme to `PrimeSpectrum A`, then apply the prime-spectrum dimension theorem.

## Depends on

- [Dimension of a scheme](scheme-dimension.md)
- [The Zariski topology on Spec](../spectrum-and-schemes/spec-zero-loci.md)

## Proof depends on

- `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.

## Sources

- [Hartshorne II.3 (subschemes-and-dimension)](../../../sources/hartshorne-ii-3.md#subschemes-and-dimension)
