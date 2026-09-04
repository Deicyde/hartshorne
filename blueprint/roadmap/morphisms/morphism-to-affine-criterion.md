---
declaration: theorem
origin: cited
---

# Criterion for a morphism into an affine variety

Let `X` be any variety and `Y ⊆ 𝔸ⁿ` an affine variety. A map of sets
`ψ : X → Y` is a morphism if and only if `xᵢ ∘ ψ` is regular on `X` for each
coordinate function `xᵢ` (Lemma 3.6).

Necessity is the definition. For sufficiency: if each `xᵢ ∘ ψ` is regular then so
is `f ∘ ψ` for every polynomial `f`, so `ψ⁻¹` of a closed set is closed and `ψ`
is continuous; and since regular functions on open subsets of `Y` are locally
quotients of polynomials, `g ∘ ψ` is regular for every regular `g`.

This is the workhorse of the section. Checking `n` regular functions is a finite,
concrete task, whereas checking the definition of a morphism quantifies over all
open sets and all regular functions on them. Every construction of a morphism
into affine space in Chapter I goes through it.

## Status

**The continuity half is proved**
(`Hartshorne.Variety.continuous_of_coords_regular`): if the coordinates of a map
from an open subset of a variety into `𝔸ⁿ` are regular, the map is continuous.
Regular functions form a subalgebra, so `f ∘ ψ` is regular for every polynomial
`f`, and the preimage of `Z(T)` is the intersection of the zero loci of those.

Discharging it required one addition to the `Variety` structure: that zero loci
of regular functions are closed. Every construction proves it as Lemma 3.1, and
there is no way to recover it from the abstract data, so it is now carried as a
field. See [Varieties](variety.md).

## What the other half still needs

The pullback of a regular function is *not* yet reachable for an abstract `X`,
and the reason is structural rather than a missing proof. A regular `f` on
`V ⊆ Y` is only *locally* a quotient `g/h`, so `f ∘ ψ` is only locally
`(g ∘ ψ)/(h ∘ ψ)`. Concluding it is regular on `ψ⁻¹(V)` needs two closure
properties that `Variety` does not have:

- closure under division by a regular function with no zeros, which a
  `Subalgebra` does not give; and
- locality, which was deliberately dropped when the structure was fixed.

Both hold in all four of Hartshorne's cases, where regularity is *defined* by
the local-quotient condition, so both can be added as fields and discharged.
That is the next step for this node, and it is a change to the central
structure rather than a proof, so it should land on its own.

## Depends on

- [Morphisms](morphism.md)
- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)

## Proof depends on

- [Regular functions are continuous](regular-function-continuous.md)

## Sources

- [Hartshorne I.3, Lemma 3.6 (p. 20)](../../sources/hartshorne.md#i3)
