---
article_id: af_ee708c56a9d1c21e6fd3eca4
declaration: def
origin: bridged
source_units: [chapter-i-section-3]
statement: formalized
proof: formalized
lean: Hartshorne.Variety.globalToFunctionField
---

# Global regular functions inside the function field

An injective ring homomorphism `𝒪(X) →+* K(X)` for an arbitrary variety,
together with the fact that it commutes with pullback along a dominant
morphism.

A global regular function is a rational function whose domain happens to be
everything, so the map is nothing but forgetting that, and injectivity is
likewise free: two global functions with the same class agree on the overlap of
their domains, and that overlap is the whole variety. The earlier
[injections node](../function-field-injections.md) contains only the underlying
set map for the concrete subset model; what is new is the bundled ring map over
the abstract structure. Upgrading the local maps to `k`-algebra homomorphisms is
part of the [intersection node](global-regular-intersection-local-rings.md).

## Why it is needed

Theorem 3.4(a) compares a global regular function with the graded pieces of
`S(Y)`, and those two things have no common home until both are inside `K(Y)`.
Parts (b) and (c) of that theorem never needed this, because they worked one
chart at a time and a chart supplies its own ambient ring.

Two compatibilities come with it, and they are what make the readings on
different charts comparable: the embedding commutes with pullback along a
dominant morphism, and on an affine variety the two routes from `A(Y)` into
`K(Y)` — through Theorem 3.2(a) as a global regular function, or directly as a
rational function — agree. Both are `Quotient.sound` on representatives that are
literally the same function.

## Depends on

- [The function field of an arbitrary variety](../function-field-abstract.md)
- [The function field is functorial for dominant morphisms](../function-field-functorial.md)
- [The ring of regular functions](../ring-of-regular-functions.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](../global-regular-eq-coordinate-ring.md)
- [The function field is the fraction field](../function-field-is-fraction-field.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)
