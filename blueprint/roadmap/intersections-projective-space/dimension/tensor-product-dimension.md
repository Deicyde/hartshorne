---
article_id: af_bb4d0c3b2bbb4d6b806f3089
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.ringKrullDim_tensorProduct
---

# Dimension of a tensor product of affine domains

Let $A$ and $B$ be finitely generated domain algebras over a field $k$.
Assume that $A\otimes_k B$ is a domain. Then

$$\dim(A\otimes_k B)=\dim A+\dim B.$$

Choose Noether normalizations of $A$ and $B$. Tensor their injective maps
and identify the tensor product of their polynomial rings with a
polynomial ring on the union of the variable sets. The target is integral
over this polynomial ring: the two factors are integral, and pure tensors
and their sums remain integral. Invariance of dimension under injective
integral extensions reduces the three dimensions to the corresponding
numbers of variables.

## Depends on

- [Finite dimension of a finitely generated algebra](../../affine-varieties/dim-fg-algebra-finite.md)
- [Krull dimension is invariant under integral extensions](../../affine-varieties/dimension-integral-extension.md)

## Sources

- [Hartshorne I.3, Exercise 3.15(d), algebraic dimension input used by I.7](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
