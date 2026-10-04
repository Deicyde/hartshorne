---
article_id: af_28ecac8a09c742cc75d72d60
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Formal functions for projective twists

Let `A` be a Noetherian local ring with maximal ideal `m`, let
`X = P^r_A`, and let `F` be a finite direct sum of twisting sheaves `O(q_j)`.
For every `i`, the formal-functions comparison map is an isomorphism:

`completion_m H^i(X,F) ~= lim_n H^i(P^r_(A/m^(n+1)), F_n)`.

The completion is ordinary algebraic maximal-adic completion. No cohomology
theory on a formal scheme is introduced in this leaf.

## Depends on

- [The formal-functions comparison map](formal-functions-comparison-map.md)
- [Cech complexes for projective twists](../../projective-cohomology/projective-twist-cech-complex.md)
- [Intermediate cohomology of projective-space twists](../../projective-cohomology/projective-space-intermediate-twist-vanishing.md)
- [Top cohomology of projective-space twists](../../projective-cohomology/projective-space-top-twist-cohomology.md)
- [Finite-module completion as tensor product](../../../schemes/formal-schemes/adic-completion/finite-module-completion-tensor.md)

## Proof depends on

- The explicit projective-space cohomology calculation commutes with the
  quotient maps `A -> A/m^(n+1)`.
- Completion and inverse limits commute with finite direct sums.

## Sources

- [Hartshorne III.11, projective-twist case of Theorem 11.1, p.277](../../../../sources/hartshorne-iii-11-12.md#infinitesimal-fibres-and-formal-functions-pp276279)
