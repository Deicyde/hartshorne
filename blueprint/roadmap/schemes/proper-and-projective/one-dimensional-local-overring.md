---
article_id: af_3d3843d1e6c14bc20aa440c3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_oneDimensionalLocalOverring
---

# A one-dimensional local overring

Let $(A,\mathfrak{m} )$ be a Noetherian local domain with nonzero maximal ideal and
fraction field $K$. There is a one-dimensional Noetherian local domain $B$
with fraction field $K$ which dominates $A$.

Choose generators $x_{1},\ldots ,x_{n}$ of $\mathfrak{m}$ with $x_{1} \ne 0$; this does not assert
that $\mathfrak{m}$ is principal. After a suitable choice of the generators, the ideal
$(x_{1})$ is proper in the affine blow-up chart
$A' = A[x_{2}/x_{1},\ldots ,x_{n}/x_{1}]$. Let $\mathfrak{p}$ be a prime minimal above $(x_{1})$
whose contraction is $\mathfrak{m}$. Then $B = A'_{\mathfrak{p}}$ dominates $A$, has the same
fraction field, and is Noetherian. The principal ideal theorem and minimality
of $\mathfrak{p}$ give dimension one.

This is the birational local-algebra step isolated from the later finite field
extension and integral-closure argument.

## Depends on

- No project-local statement prerequisites.

## Proof depends on

- Existence of a finite generating family for an ideal in a Noetherian ring.
- Krull's principal ideal theorem and localization at a prime.

## Sources

- [Hartshorne II.4, repaired local-overring step of Exercise 4.11(a)](../../../sources/hartshorne-ii-4.md#adopted-exercises)
