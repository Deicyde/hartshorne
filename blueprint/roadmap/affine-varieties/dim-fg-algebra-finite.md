---
article_id: af_1d979119a72daf4ba70d3a3b
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.exists_ringKrullDim_eq_natCast Hartshorne.finiteRingKrullDim_of_finiteType
---

# A finitely generated algebra over a field has finite dimension

Let $k$ be a field and let $R$ be a nontrivial finitely generated
$k$-algebra. Then its Krull dimension is a finite nonnegative integer.

Noether normalization presents $R$ as an injective integral extension of
a polynomial ring $k[y_1,\ldots,y_s]$. Dimension is invariant under such
extensions, so

$$\dim R=\dim k[y_1,\ldots,y_s]=s.$$

The assertion applies to algebras that are not domains, including the
coordinate rings of reducible algebraic sets.

## Depends on

- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
