---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.globalRegular Hartshorne.polynomialToRegular Hartshorne.isRegular_polynomialToRegular Hartshorne.polynomialToRegular_eq_zero_iff
---

# The ring of regular functions

For a variety `Y`, `𝒪(Y)` is the ring of regular functions `Y → k`. It is a
`k`-algebra under pointwise operations, and an isomorphism of varieties induces
an isomorphism of `k`-algebras, so `𝒪(Y)` is an invariant of `Y`.

The ring structure is routine; the substance is functoriality, since Proposition
3.5 is stated in terms of the induced map `𝒪(Y) → 𝒪(X)` for a morphism
`φ : X → Y`. Establish that map here as part of the definition rather than
rebuilding it later.

## Depends on

- [Varieties](variety.md)
- [Morphisms](morphism.md)

## Sources

- [Hartshorne I.3, definition of `𝒪(Y)` (p. 16)](../../sources/hartshorne.md#i3)
