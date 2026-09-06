---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.Variety.globalRationalRep Hartshorne.Variety.globalToFunctionField Hartshorne.Variety.globalToFunctionField_injective Hartshorne.VarietyHom.globalPullback Hartshorne.VarietyHom.globalPullback_id Hartshorne.VarietyHom.globalPullback_comp Hartshorne.VarietyHom.functionFieldHom_globalToFunctionField Hartshorne.coordToRational_eq_globalToFunctionField
---

# Global regular functions inside the function field

`𝒪(X) → K(X)` for an arbitrary variety, injectively, together with the fact
that it commutes with pullback along a dominant morphism.

A global regular function is a rational function whose domain happens to be
everything, so the map is nothing but forgetting that, and injectivity is
likewise free: two global functions with the same class agree on the overlap of
their domains, and that overlap is the whole variety. The affine version is part
of [the injections node](function-field-injections.md); what is new is only that
it holds over the abstract structure.

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

- [The function field of an arbitrary variety](function-field-abstract.md)
- [The function field is functorial for dominant morphisms](function-field-functorial.md)
- [The ring of regular functions](ring-of-regular-functions.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)
- [The function field is the fraction field](function-field-is-fraction-field.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../sources/hartshorne.md#i3)
