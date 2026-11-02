---
article_id: af_dc1c548ddbcb3dffbb3f947e
declaration: lemma
origin: background
mathlib: true
mathlib_declaration: LocalSubring.exists_le_valuationSubring
mathlib_file: Mathlib/RingTheory/Valuation/LocalSubring.lean
---

# Every local subring is dominated by a valuation ring

For every local subring $A$ of a field $K$, there is a valuation ring $B$ of
$K$ which dominates it:

$$A\subseteq B,\qquad \mathfrak{m}_B\cap A=\mathfrak{m}_A.$$

This is the second clause of Theorem 6.1A. The maximal-ideal condition says
that the inclusion is a local homomorphism.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Valuation rings are maximal local subrings](valuation-ring-maximal-local-subring.md)

## Sources

- [Hartshorne I.6, Theorem 6.1A (p. 40)](../../sources/hartshorne.md#i6-valuation-and-dvr-background)
