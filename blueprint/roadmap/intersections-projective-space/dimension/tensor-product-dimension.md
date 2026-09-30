---
article_id: af_bb4d0c3b2bbb4d6b806f3089
declaration: theorem
origin: background
source_units: [chapter-i-section-7-main]
---

# Dimension of a tensor product of affine domains

Let `A` and `B` be finitely generated domain algebras over a field `k`, and
assume that `A ⊗[k] B` is a domain.  Then

`ringKrullDim (A ⊗[k] B) = ringKrullDim A + ringKrullDim B`.

The sole main declaration is planned as
`Hartshorne.ringKrullDim_tensorProduct`.  In the geometric application the
domain hypothesis is supplied by irreducibility of the affine product.

Choose Noether normalisations of `A` and `B`.  Tensor their injective maps,
identify the tensor product of the two polynomial rings with the polynomial
ring on the sum of their variables, and show that the target is integral over
that polynomial ring by two base changes followed by transitivity.  Invariance
of Krull dimension under injective integral extensions then reduces all three
dimensions to the corresponding numbers of variables.

Pinned Mathlib supplies `MvPolynomial.tensorEquivSum`, tensor-map injectivity
over a field, `Algebra.IsPushout.isIntegral`, and Noether normalisation.  It
does not supply this tensor-product dimension theorem as a packaged result.

## Depends on

- [Dimension of a finitely generated domain](../../affine-varieties/dim-fg-domain.md)
- [Krull dimension is invariant under integral extensions](../../affine-varieties/dimension-integral-extension.md)

## Sources

- [Hartshorne I.3, Exercise 3.15(d), algebraic dimension input used by I.7](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
