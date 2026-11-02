---
article_id: af_a583b15ad8a2e84459d9b21c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dim_eq_dim_closure
---

# Dimension of a quasi-affine variety

If $Y$ is a quasi-affine variety, then

$$\dim Y=\dim\overline{Y}.$$

This is Hartshorne's Proposition I.1.10. Taking closures of irreducible
closed subsets gives the inequality $\dim Y\leq\dim\overline{Y}$.
For the reverse inequality, choose a point $P\in Y$ and consider prime
chains in $A(\overline{Y})$ below its maximal ideal $\mathfrak m_P$.
The quotient $A(\overline{Y})/\mathfrak m_P$ is isomorphic to $k$, so
[the dimension formula](dim-formula-catenary.md) gives

$$\operatorname{ht}\mathfrak m_P=\dim A(\overline{Y}).$$

An irreducible closed subset of $\overline{Y}$ containing $P$ meets the
open subset $Y$ in a nonempty irreducible subset whose closure is the
original closed set. Intersecting these subsets with $Y$ therefore
preserves strict inclusions. Reversing a prime chain below $\mathfrak m_P$
and restricting it to $Y$ gives a chain in $Y$ of the same length, proving
the other inequality.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](dim-formula-catenary.md)
- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.1, Proposition 1.10 (p. 6)](../../sources/hartshorne.md#i1)
