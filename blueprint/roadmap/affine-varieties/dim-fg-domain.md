---
article_id: af_069401b5e23eaef4de57a814
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.isAlgebraic_of_isFractionRing Hartshorne.exists_ringKrullDim_eq_trdeg
---

# Dimension of a finitely generated domain

Let $k$ be a field and let $B$ be a finitely generated $k$-algebra that is
an integral domain. Then

$$\dim B=\operatorname{trdeg}_k K(B),$$

where $K(B)$ is the fraction field of $B$. Both sides are finite
nonnegative integers.

This is Hartshorne's Theorem I.1.8A(a), quoted from Matsumura and
Atiyah–Macdonald. Together with [the dimension formula](dim-formula-catenary.md),
it supports the dimension calculations throughout Chapter I.

Choose a Noether normalization $k[y_1,\ldots,y_s]\hookrightarrow B$.
The extension is integral, so both rings have dimension $s$.
Their fraction fields form an algebraic extension, so $K(B)$ also has
transcendence degree $s$ over $k$.

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)
- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)
- [A finitely generated algebra over a field has finite dimension](dim-fg-algebra-finite.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
