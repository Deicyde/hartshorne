---
article_id: af_a7d1a97e3f9969001b1d67d0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.globalToLocal_injective Hartshorne.localToFunctionField_injective
---

# The underlying maps into germs and rational functions are injective

For a quasi-affine variety $Y$ and a point $P\in Y$, passing from a
global regular function to its germ and then forgetting the base point
gives injective maps of sets

$$\mathcal O(Y)\hookrightarrow\mathcal O_{P,Y}\hookrightarrow K(Y).$$

These injectivity statements follow from the agreement relations on
representatives. The identity principle identifies agreement on the whole
overlap with agreement on some neighbourhood of $P$.

The algebra homomorphisms and the intersection formula inside $K(Y)$ are
proved separately in [the global intersection theorem](global-functions/global-regular-intersection-local-rings.md).

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [The local ring at a point](local-ring.md)
- [The function field](function-field.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, the injections $\mathcal{O} (Y) \to \mathcal{O} _P \to K(Y)$ (p. 16)](../../sources/hartshorne.md#i3)
