---
declaration: instance
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: PrimeSpectrum.zariskiTopology
mathlib_file: Mathlib/RingTheory/Spectrum/Prime/Topology.lean
---

# The Zariski topology on Spec

For a commutative ring `A`, let `Spec A` be its prime ideals and
`V(𝔞) = {𝔭 | 𝔞 ≤ 𝔭}`.  The identities
`V(𝔞𝔟) = V(𝔞) ∪ V(𝔟)` and `V(⨆ i, 𝔞 i) = ⋂ i, V(𝔞 i)` make these sets the
closed sets of a topology.  Moreover,
`V(𝔞) ⊆ V(𝔟) ↔ 𝔟 ≤ radical 𝔞`, and the principal opens `D(f)` form a basis.

The pinned implementation is `PrimeSpectrum.zariskiTopology`; the source
clauses are supplied exactly by `PrimeSpectrum.zeroLocus_mul`,
`PrimeSpectrum.zeroLocus_iSup`,
`PrimeSpectrum.zeroLocus_subset_zeroLocus_iff`, and
`PrimeSpectrum.isTopologicalBasis_basic_opens`.

## Depends on

- Nothing in this roadmap.

## Sources

- [Hartshorne II.2, Lemma 2.1 and the following basis observation (p. 70)](../../../sources/hartshorne-ii-2.md#opening-and-lemma-21)
