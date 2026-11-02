---
article_id: af_dbf6174162e22fb1ef61e8b6
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.ringKrullDim_quotient_eq_coheight Hartshorne.height_add_ringKrullDim_quotient_le
---

# One inequality of the dimension formula

For a commutative ring $R$ and a prime ideal $\mathfrak p$,

$$\operatorname{ht}\mathfrak p+\dim(R/\mathfrak p)\leq\dim R.$$

A chain of primes below $\mathfrak p$ and a chain above it can be joined
at $\mathfrak p$. The resulting chain has length equal to the sum of the
two lengths. No finite-generation or domain hypothesis is needed.

The dimension of $R/\mathfrak p$ is the supremum of the lengths of prime
chains above $\mathfrak p$. Equality is supplied under the stronger
hypotheses of [the dimension formula](dim-formula-catenary.md).

## Depends on

- [Dimension of a topological space and of a ring](dimension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
