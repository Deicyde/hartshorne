---
article_id: af_00d868cf7f23d86aaa14cd83
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
---

# Integer-graded submodules and quotients

Let `M = ⊕ d, M_d` be an integer-graded `S`-module and let `N ⊆ M` be a
homogeneous submodule. Intersecting `N` with each `M_d` grades `N`, and mapping
each `M_d` through `M → M/N` grades the quotient. In every degree the
canonical sequence

`0 → N_d → M_d → (M/N)_d → 0`

is exact. The sole main result is planned as
`Hartshorne.gradedSubquotient_exact`, packaging both induced decompositions,
their graded scalar actions, and this componentwise exactness. The same package
applies to `N₁ ⊆ N₂ ⊆ M`, giving the grading on `N₂/N₁` used in a prime
filtration.

Mathlib defines `HomogeneousSubmodule` but does not supply these quotient
decompositions or their degreewise exact sequence. The construction should
follow the already-formalized quotient-grading argument for homogeneous ideals,
with well-definedness supplied by homogeneity of `N`.

## Depends on

- [Integer-graded module twists](graded-module-twists.md)

## Proof depends on

- [The integer grading on a polynomial ring](integer-polynomial-grading.md)

## Sources

- [Hartshorne I.7, graded subquotients in Proposition 7.4 and Theorem 7.5 (pp. 50–51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
