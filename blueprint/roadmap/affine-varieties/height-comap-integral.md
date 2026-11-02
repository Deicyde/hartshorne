---
article_id: af_f738e02ee27aca87ee002bce
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.height_le_height_comap_of_isIntegral Hartshorne.height_comap_le_height_of_hasGoingDown Hartshorne.height_comap_eq_height_of_isIntegral
---

# Height is preserved by contraction along an integral extension

Let $A\subseteq B$ be an integral extension of domains, with $A$
integrally closed. For every prime ideal $\mathfrak p$ of $B$,

$$\operatorname{ht}(\mathfrak p\cap A)=\operatorname{ht}\mathfrak p.$$

Incomparability ensures that contracting a prime chain below $\mathfrak p$
preserves strict inclusions. Going down lifts a prime chain below
$\mathfrak p\cap A$ to one below $\mathfrak p$. These give the two
inequalities.

The result applies to Noether normalization because a polynomial ring
over a field is a unique factorization domain and hence integrally closed.
It is the height comparison used in [the dimension formula](dim-formula-catenary.md).

## Depends on

- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
