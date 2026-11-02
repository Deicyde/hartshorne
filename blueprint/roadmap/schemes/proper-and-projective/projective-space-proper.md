---
article_id: af_7d438e5682951dd9d44615d5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveSpaceOverSchemeProjection_isProper
---

# Projective space is proper

For every Noetherian scheme $Y$ and every $n$, the projection
$\mathbb{P}^n_Y\to Y$ is proper. The same conclusion holds for an
arbitrary base scheme after identifying relative projective space
with its base-change construction.

Identify projective space over $\mathbb Z$ with
$\operatorname{Proj}\mathbb Z[x_0,\ldots,x_n]$. The homogeneous
coordinate algebra is finitely generated in degree one, so the
valuative criterion proves properness. Stability under base change
then gives the projection over $Y$.

## Depends on

- [Projective space over a scheme](projective-space-over-scheme.md)
- [Proper morphisms](proper-morphism.md)

## Proof depends on

- [Proper-morphism calculus](proper-morphism-calculus.md)
- [Projective space over a ring](../projective-spectrum/projective-space-over-ring.md)
- The valuative criterion for the structure morphism of Proj.

## Sources

- [Hartshorne II.4, proof of Theorem 4.9](../../../sources/hartshorne-ii-4.md#projective-morphisms)
