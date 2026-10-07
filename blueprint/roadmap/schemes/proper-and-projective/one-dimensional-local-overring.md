---
article_id: af_3d3843d1e6c14bc20aa440c3
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
statement: formalized
proof: formalized
lean: Hartshorne.OneDimensionalLocalOverring Hartshorne.exists_oneDimensionalLocalOverring
---

# A one-dimensional local overring

Let `(A,𝔪)` be a Noetherian local domain with nonzero maximal ideal and
fraction field `K`. There is a one-dimensional Noetherian local domain `B`
with fraction field `K` which dominates `A`.

Choose generators `x₁,…,xₙ` of `𝔪` with `x₁ ≠ 0`; this does not assert
that `𝔪` is principal. After a suitable choice of the generators, the ideal
`(x₁)` is proper in the affine blow-up chart
`A' = A[x₂/x₁,…,xₙ/x₁]`. Let `𝔭` be a prime minimal above `(x₁)`
whose contraction is `𝔪`. Then `B = A'_𝔭` dominates `A`, has the same
fraction field, and is Noetherian. The principal ideal theorem and minimality
of `𝔭` give dimension one.

This is the birational local-algebra step isolated from the later finite field
extension and integral-closure argument.

## Depends on

- No project-local statement prerequisites.

## Proof depends on

- Existence of a finite generating family for an ideal in a Noetherian ring.
- Krull's principal ideal theorem and localization at a prime.

## Sources

- [Hartshorne II.4, repaired local-overring step of Exercise 4.11(a)](../../../sources/hartshorne-ii-4.md#adopted-exercises)
