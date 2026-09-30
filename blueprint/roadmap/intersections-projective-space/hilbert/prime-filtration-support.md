---
article_id: af_47ddc8c1c5ad90500da8b0d7
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
---

# Minimal primes in a graded prime filtration

Fix a graded prime filtration of `M` with factor primes
`p₁,…,pₜ`. For every homogeneous prime ideal `p`,

`Ann M ⊆ p ⟺ ∃ i, pᵢ ⊆ p`.

The sole main declaration is planned as
`Hartshorne.gradedPrimeFiltration_annihilator_le_iff`. It includes the stated
consequence of Proposition 7.4(a): the minimal elements of the finite set of
factor primes are exactly the primes minimal over `Ann M`.

Each factor is supported on `V(pᵢ)`. Exactness makes the support of the middle
module the union of the supports of its submodule and quotient, so induction
over the filtration identifies the support of `M` with the finite union of
these closed sets. Pinned Mathlib supplies `Module.support_of_exact` and, for a
finite module, `Module.support_eq_zeroLocus`; the work here connects those
ungraded results to the recorded homogeneous filtration.

## Depends on

- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)
- [Graded prime filtrations](graded-prime-filtration.md)

## Sources

- [Hartshorne I.7, Proposition 7.4(a) (p. 50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
