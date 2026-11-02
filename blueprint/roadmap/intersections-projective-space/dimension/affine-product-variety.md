---
article_id: af_6ab332f43691470db2219d1f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isAffineVariety_affineProduct
---

# Affine products are varieties

Let $X\subseteq\mathbb A^m$ and $Y\subseteq\mathbb A^n$ be affine
varieties over an algebraically closed field. Their product, viewed as a
subset of $\mathbb A^{m+n}$ with the induced Zariski topology, is an
affine variety.

This is Hartshorne's Exercise I.3.15(a), used in
[Proposition I.7.1](affine-dimension-theorem.md). Each factor's equations
extend to its coordinate block, proving closedness. Irreducibility follows
from the closed-fibre argument. The topology used is the one induced from
affine space, rather than the ordinary product topology.

## Depends on

- [Algebraic sets](../../affine-varieties/algebraic-set.md)
- [Affine and quasi-affine varieties](../../affine-varieties/affine-variety.md)

## Proof depends on

- [The Zariski topology on affine space](../../affine-varieties/zariski-topology.md)

## Sources

- [Hartshorne I.3, Exercise 3.15(a), and I.7, proof of Proposition 7.1](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
