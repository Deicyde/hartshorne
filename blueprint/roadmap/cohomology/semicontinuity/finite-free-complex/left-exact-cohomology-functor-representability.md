---
article_id: af_e7551dc3d493bef0e44aafab
declaration: theorem
origin: cited
---

# Left exact cohomology functors are finitely represented

Let $L$ be the finite-free model and put

$W^i = \operatorname{coker} (L^{i-1} \to L^i)$.

For a fixed $i$, the following are equivalent:

1. $T^i$ is left exact;
2. $W^i$ is a projective $A$-module;
3. there is a finitely generated $A$-module $Q$ and a natural isomorphism
   $T^i(M) \simeq \operatorname{Hom} _A(Q,M)$ for every $A$-module $M$.

The representing module $Q$ is unique up to the canonical isomorphism induced
by the two representing natural isomorphisms.

## Depends on

- [A finite-free model for projective cohomology](projective-cohomology-finite-free-model.md)

## Proof depends on

- The exact sequence $0 \to T^i(M) \to W^i \otimes M \to L^{i+1} \otimes M$.
- A finitely generated flat module is projective, and duality for finite
  projective modules identifies the displayed kernel with $\operatorname{Hom} _A(Q,M)$.

## Sources

- [Hartshorne III.12, Proposition 12.4 and Remark 12.4.1, pp.284–286](../../../../sources/hartshorne-iii-11-12.md#cohomology-after-tensor-and-finite-free-models-pp281287)
