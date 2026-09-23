---
article_id: af_2676126077d19db346a29821
declaration: lemma
origin: background
source_units: [chapter-i-section-6-valuations]
mathlib: true
mathlib_declaration: LocalSubring.isMax_iff
mathlib_file: Mathlib/RingTheory/Valuation/LocalSubring.lean
---

# Valuation rings are maximal local subrings

Let `K` be a field and `A : LocalSubring K`. Then `A` is maximal among local
subrings for the domination order if and only if it is the local subring
underlying some `ValuationSubring K`:

`IsMax A ↔ ∃ B : ValuationSubring K, B.toLocalSubring = A`.

This is the first clause of Theorem 6.1A. Mathlib's order on `LocalSubring K`
is exactly Hartshorne's domination relation: `LocalSubring.le_def` expands
`A ≤ B` into inclusion of the underlying subrings together with the induced
map being local, equivalently contraction of the maximal ideal.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne I.6, definitions and Theorem 6.1A (pp. 39–40)](../../sources/hartshorne.md#i6-valuation-and-dvr-background)
