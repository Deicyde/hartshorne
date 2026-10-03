---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Connected spectra, idempotents, and products

For a commutative ring `A`, the following are equivalent:

1. `Spec A` is disconnected;
2. `1 = e₁ + e₂` for nonzero orthogonal idempotents `e₁,e₂`;
3. `A` is isomorphic to a product `A₁ × A₂` of two nonzero rings.

A clopen decomposition of the spectrum gives complementary sections of the
structure sheaf and hence complementary idempotents in
`Γ(Spec A,𝒪) ≅ A`.  Conversely an idempotent splits the spectrum into the two
clopen principal opens `D(e)` and `D(1-e)`.  The standard map
`a ↦ (ae₁,ae₂)` gives the ring product decomposition.  This is Exercise 2.19.

## Depends on

- [The Zariski topology on Spec](../spectrum-and-schemes/spec-zero-loci.md)

## Proof depends on

- [Global sections of Spec](../spectrum-and-schemes/spec-global-sections.md)

## Sources

- [Hartshorne II.2, Exercise 2.19, used in Theorem III.11.3 immediately before Zariski's Main Theorem, Corollary III.11.4](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
