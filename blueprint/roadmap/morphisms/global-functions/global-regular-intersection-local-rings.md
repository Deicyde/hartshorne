---
article_id: af_0df050d2390884e2b006ce27
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.globalRegularRange_eq_iInf_localRingRange
---

# Global regular functions are the intersection of the local rings

For a variety $X$ over $k$ and every point $P\in X$, restriction to a
germ and forgetting its base point give injective $k$-algebra maps

$$\mathcal O(X)\hookrightarrow\mathcal O_{P,X}\hookrightarrow K(X).$$

Their composite is the canonical embedding of global regular functions
into the function field. Identifying all rings with their images gives

$$\mathcal O(X)=\bigcap_{P\in X}\mathcal O_{P,X}\quad\text{inside }K(X).$$

One inclusion is restriction. Conversely, a rational function in every
local ring is regular near every point, so locality makes it globally regular.
The earlier [underlying injectivity statements](../function-field-injections.md)
concern only maps of sets; the present result includes their algebraic
structure and the intersection identity.

## Depends on

- [The ring of regular functions](../ring-of-regular-functions.md)
- [The local ring at a point](../local-ring.md)
- [The function field of an arbitrary variety](../function-field-abstract.md)
- [Global regular functions inside the function field](global-regular-in-function-field.md)

## Proof depends on

- [Varieties](../variety.md)

## Sources

- [Hartshorne I.3, the injections and intersection formula (p. 16)](../../../sources/hartshorne.md#i3)
