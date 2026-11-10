---
article_id: af_b22063ac78ef7edd9e6fdd8c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dimension_at_closed_point
---

# Dimension at a closed point

Let $X$ be an integral scheme of finite type over a field. For every closed point $P \in X$, $\dim X=\dim\mathcal{O}_{X,P}$.

Reduce to an affine neighbourhood of $P$. Identify the local-ring dimension with the height of the maximal prime and use the finite-type domain dimension theorem to identify that height with the global dimension.

## Depends on

- [Dimension of an affine scheme](affine-scheme-dimension.md)
- [Integral schemes](../first-properties/integral-scheme.md)
- [Morphisms of finite type](../first-properties/finite-type.md)

## Proof depends on

- [A finitely generated algebra over a field has finite dimension](../../affine-varieties/dim-fg-algebra-finite.md)
- [Dimension of a finitely generated domain](../../affine-varieties/dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](../../affine-varieties/dim-formula-catenary.md)
- The dimension formula for a finite-type domain and the identification of local-ring dimension with point coheight.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)
