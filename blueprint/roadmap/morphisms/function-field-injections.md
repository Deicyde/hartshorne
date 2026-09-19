---
article_id: af_a7d1a97e3f9969001b1d67d0
declaration: theorem
origin: cited
source_units: [chapter-i-section-3]
statement: formalized
proof: formalized
lean: Hartshorne.globalToLocal_injective Hartshorne.localToFunctionField_injective
---

# The underlying maps into germs and rational functions are injective

In the concrete subset-of-affine-space model used to construct the objects of
§3, forgetting domain information gives injective functions

`𝒪(Y) ↪ 𝒪_{P,Y} ↪ K(Y)`.

This article records exactly the two statements currently proved in Lean:
`globalToLocal_injective` and `localToFunctionField_injective`. The maps here
are functions between quotient types, not yet bundled `k`-algebra
homomorphisms. Consequently this node does **not** identify the three objects as
subalgebras of one ambient field and does not prove Hartshorne's intersection
formula.

The missing algebraic maps and the equality
`𝒪(Y) = ⋂_{P ∈ Y} 𝒪_{P,Y}` inside `K(Y)` are tracked separately in
[Global regular functions are the intersection of the local rings](global-functions/global-regular-intersection-local-rings.md).

Injectivity is immediate for Hartshorne's representatives. Two global
functions have the same germ exactly when they agree on the whole overlap,
which is all of `Y`; and the local-to-rational map uses the same agreement
relation after forgetting the distinguished point.

The identity principle still matters: `GermRep.rel_iff_eventually` proves that
Hartshorne's whole-overlap relation agrees with the usual germ relation of
agreement on some neighbourhood of `P`.

## Depends on

- [The ring of regular functions](ring-of-regular-functions.md)
- [The local ring at a point](local-ring.md)
- [The function field](function-field.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, the injections `𝒪(Y) → 𝒪_P → K(Y)` (p. 16)](../../sources/hartshorne.md#i3)
