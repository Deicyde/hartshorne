---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.globalRegular Hartshorne.polynomialToRegular Hartshorne.isRegular_polynomialToRegular Hartshorne.polynomialToRegular_eq_zero_iff Hartshorne.VarietyHom.pullback Hartshorne.VarietyHom.pullback_id Hartshorne.VarietyHom.pullback_comp Hartshorne.compAlgHom Hartshorne.isRegular_iff_top
---

# The ring of regular functions

For a variety `Y`, `𝒪(Y)` is the ring of regular functions `Y → k`. It is a
`k`-algebra under pointwise operations, and an isomorphism of varieties induces
an isomorphism of `k`-algebras, so `𝒪(Y)` is an invariant of `Y`.

The ring structure is routine; the substance is functoriality, since Proposition
3.5 is stated in terms of the induced map `𝒪(Y) → 𝒪(X)` for a morphism
`φ : X → Y`. That map is `VarietyHom.pullback`, and it is contravariantly
functorial.

One wrinkle is worth recording. `Variety` indexes regular functions by open
subsets, so its `𝒪(Y)` consists of functions on `↥(⊤ : Opens Y)` rather than on
`Y`. The two readings agree, but not definitionally: they differ by the
homeomorphism between a space and its top open subset.
`Hartshorne.isRegular_iff_top` converts between them, and it is a corollary of
the general fact that regularity survives any homeomorphism commuting with the
map to affine space. Statements that mention both a concrete `Y ⊆ 𝔸ⁿ` and a
bundled variety need it.

## Depends on

- [Varieties](variety.md)
- [Morphisms](morphism.md)

## Sources

- [Hartshorne I.3, definition of `𝒪(Y)` (p. 16)](../../sources/hartshorne.md#i3)
