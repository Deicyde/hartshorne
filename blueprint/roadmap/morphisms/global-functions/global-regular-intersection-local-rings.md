---
article_id: af_0df050d2390884e2b006ce27
declaration: theorem
origin: cited
source_units: [chapter-i-section-3]
statement: formalized
proof: formalized
lean: Hartshorne.Variety.globalRegularRange_eq_iInf_localRingRange
---

# Global regular functions are the intersection of the local rings

For a variety `X` over `k`, restriction to a germ and forgetting its base point
give injective `k`-algebra homomorphisms

`𝒪(X) →ₐ[k] 𝒪_{P,X} →ₐ[k] K(X)`

for every `P : X`, and their composite is the canonical map from global regular
functions to rational functions. After identifying their ranges as
`k`-subalgebras of `K(X)`, the main theorem is

`range(𝒪(X) → K(X)) = ⨅ P, range(𝒪_{P,X} → K(X))`.

The inclusion from left to right is restriction. In the other direction, a
rational function lying in every local ring is regular near every point; the
locality axiom `Variety.regular_of_locally` then makes it globally regular.

This is the structural statement Hartshorne uses when he silently treats all
three rings as subrings of `K(X)`. The earlier
[underlying-injections node](../function-field-injections.md) proves only the
set-level injectivity in the concrete model and is not a proof of this equality.

## Depends on

- [The ring of regular functions](../ring-of-regular-functions.md)
- [The local ring at a point](../local-ring.md)
- [The function field of an arbitrary variety](../function-field-abstract.md)
- [Global regular functions inside the function field](global-regular-in-function-field.md)

## Proof depends on

- [Varieties](../variety.md)

## Sources

- [Hartshorne I.3, the injections and intersection formula (p. 16)](../../../sources/hartshorne.md#i3)
