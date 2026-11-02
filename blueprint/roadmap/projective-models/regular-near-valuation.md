---
article_id: af_e2c74229d0e5f0d585bda655
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.ValuationSpace.mem_valuationSubring_iff_exists_regular_neighborhood
---

# Regularity near a valuation

Let $K/k$ be a one-dimensional function field, let $R$ be a discrete
valuation ring of $K/k$, and let $q\in K$. Then $q\in R$ if and only if
there is an open neighbourhood of $R$ in $C_K$ on which $q$ is regular.

Thus membership in the valuation ring is exactly regularity near the
corresponding point. This is the local fact used to extend a morphism
across a missing point in Hartshorne's Proposition I.6.8.

## Depends on

- [Discrete valuation rings of a function field](../curve-normalization/function-field-dvrs.md)
- [Regular functions on the valuation space](../curve-normalization/valuation-regular-functions.md)

## Proof depends on

- [A rational function has finitely many poles](../curve-normalization/finite-poles.md)
- [The valuation-space regularity axioms](../curve-normalization/valuation-regular-functions-local.md)

## Sources

- [Hartshorne I.6, discussion on p. 42 and Proposition 6.8 (pp. 43--44)](../../sources/hartshorne.md#i6-projective-models)
