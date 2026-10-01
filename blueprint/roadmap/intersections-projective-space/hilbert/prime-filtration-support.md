---
article_id: af_47ddc8c1c5ad90500da8b0d7
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.gradedPrimeFiltration_annihilator_le_iff
---

# Minimal primes in a graded prime filtration

Fix a graded prime filtration of `M` with factor primes
`p₁,…,pₜ`. For every prime ideal `p`,

`Ann M ⊆ p ⟺ ∃ i, pᵢ ⊆ p`.

The main declaration is
`Hartshorne.gradedPrimeFiltration_annihilator_le_iff`. Its formalized statement
is slightly stronger than the source because `p` need not be homogeneous.
The corollary `Hartshorne.gradedPrimeFiltration_minimal_factor_iff` identifies
the minimal elements of the finite set of factor primes with the primes
minimal over `Ann M`.

For one filtration step, the annihilator of the quotient factor is its
recorded prime `pᵢ`, while the product of the annihilator of the preceding term
and `pᵢ` annihilates the next term. Primality therefore turns containment of
the next annihilator into a disjunction: either the preceding annihilator or
`pᵢ` is contained in the target prime. Induction over the `RelSeries`, starting
at the zero submodule and ending at `M`, proves the equivalence.

The stable chosen-factor API consists of
`Hartshorne.GradedPrimeFiltrationFactorData`,
`Hartshorne.gradedPrimeFiltrationFactorDataAt`, and
`Hartshorne.gradedPrimeFiltrationFactorPrime`; it exposes the selected prime,
twist, and graded equivalence at every filtration index. The accompanying
specification theorem shows that these selected primes enumerate exactly the
factor-prime predicate used by the main theorem.

## Depends on

- [Homogeneous annihilators and cyclic modules](graded-annihilator.md)
- [Graded prime filtrations](graded-prime-filtration.md)

## Sources

- [Hartshorne I.7, Proposition 7.4(a) (p. 50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
