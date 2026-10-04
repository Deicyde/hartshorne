---
article_id: af_4b16d05f05c6a0069b4f524c
declaration: instance
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: ProjectiveSpectrum.zariskiTopology
mathlib_file: Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean
---

# The topology on Proj

For an `ℕ`-graded commutative ring `S`, `Proj S` is the set of homogeneous
prime ideals not containing the irrelevant ideal `S₊`.  For homogeneous ideals
`𝔞,𝔟`,

`V(𝔞𝔟) = V(𝔞) ∪ V(𝔟)` and `V(⨆ i,𝔞 i) = ⋂ i,V(𝔞 i)`.

These zero loci define the topology of Lemma 2.4.  The exact supporting
declarations include `zeroLocus_mul_homogeneousIdeal`,
`zeroLocus_iSup_homogeneousIdeal`, and `isTopologicalBasis_basic_opens`.

## Depends on

- Nothing in this roadmap.

## Sources

- [Hartshorne II.2, definition of Proj and Lemma 2.4 (p. 76)](../../../sources/hartshorne-ii-2.md#proj-lemma-24-and-proposition-25)
