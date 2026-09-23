---
article_id: af_dc1c548ddbcb3dffbb3f947e
declaration: lemma
origin: background
source_units: [chapter-i-section-6-valuations]
mathlib: true
mathlib_declaration: LocalSubring.exists_le_valuationSubring
mathlib_file: Mathlib/RingTheory/Valuation/LocalSubring.lean
---

# Every local subring is dominated by a valuation ring

For every local subring `A` of a field `K`, there is a valuation subring `B`
which dominates it:

`∃ B : ValuationSubring K, A ≤ B.toLocalSubring`.

This is the second clause of Theorem 6.1A. The order relation includes both
subring inclusion and locality of the inclusion, so the upstream statement is
an exact match rather than merely an existence theorem for a larger subring.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Valuation rings are maximal local subrings](valuation-ring-maximal-local-subring.md)

## Sources

- [Hartshorne I.6, Theorem 6.1A (p. 40)](../../sources/hartshorne.md#i6-valuation-and-dvr-background)
