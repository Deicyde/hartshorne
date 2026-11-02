---
article_id: af_6fcb9ec05f4b4d2a25418790
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dim
---

# Dimension of a topological space and of a ring

The *dimension* of a topological space $X$ is the supremum of the integers
$n$ for which there is a chain

$$Z_0\subsetneq Z_1\subsetneq\cdots\subsetneq Z_n$$

of irreducible closed subsets. The dimension of a variety is its dimension
as a topological space.

The *height* of a prime ideal $\mathfrak p$ is the supremum of the lengths
of chains of prime ideals ending at $\mathfrak p$. The *Krull dimension*
of a ring is the supremum of the heights of its prime ideals.

The empty space has no such chain; its dimension is assigned a value below
zero. Infinite-dimensional spaces and rings are allowed in these general
definitions.

## Depends on

- [Affine and quasi-affine varieties](affine-variety.md)

## Sources

- [Hartshorne I.1, definitions of dimension, height and Krull dimension (pp. 5-6)](../../sources/hartshorne.md#i1)
