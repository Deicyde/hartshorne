---
article_id: af_cbb14bbd237a44288abce54a
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.affineDiagonalSectionHomeomorph
---

# The diagonal section of an affine product

Let $Y,Z\subseteq\mathbb A^n$. In $\mathbb A^{2n}$, with coordinate
blocks $x_1,\ldots,x_n$ and $y_1,\ldots,y_n$, the equations

$$x_i-y_i=0\qquad(1\leq i\leq n)$$

cut out the diagonal. The map $P\mapsto(P,P)$ is a canonical
homeomorphism from $Y\cap Z$ to the intersection of $Y\times Z$ with
this diagonal. Its inverse restricts to either coordinate block.

The diagonal is cut out by at most $n$ equations. The homeomorphism
preserves dimension and transports irreducible components, as needed in
[Hartshorne's Proposition I.7.1](affine-dimension-theorem.md).

## Depends on

- [Affine products are varieties](affine-product-variety.md)
- [Dimension of a topological space and of a ring](../../affine-varieties/dimension.md)

## Proof depends on

- [The Zariski topology on affine space](../../affine-varieties/zariski-topology.md)
- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne I.7, diagonal reduction in the proof of Proposition 7.1](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
