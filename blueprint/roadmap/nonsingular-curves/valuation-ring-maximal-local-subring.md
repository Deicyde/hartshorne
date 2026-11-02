---
article_id: af_2676126077d19db346a29821
declaration: lemma
origin: background
mathlib: true
mathlib_declaration: LocalSubring.isMax_iff
mathlib_file: Mathlib/RingTheory/Valuation/LocalSubring.lean
---

# Valuation rings are maximal local subrings

Let $K$ be a field and let $A$ be a local subring of $K$. Then $A$ is maximal
among local subrings under domination if and only if it is a valuation ring
of $K$.

A local subring $B$ dominates $A$ when $A\subseteq B$ and
$\mathfrak{m}_B\cap A=\mathfrak{m}_A$, where $\mathfrak{m}_A$ and
$\mathfrak{m}_B$ are their maximal ideals. Thus domination requires the
inclusion to be a local homomorphism. This is the first clause of Theorem 6.1A.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne I.6, definitions and Theorem 6.1A (pp. 39–40)](../../sources/hartshorne.md#i6-valuation-and-dvr-background)
