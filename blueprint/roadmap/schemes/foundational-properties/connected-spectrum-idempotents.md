---
article_id: af_9320492f02cd29177eca029f
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.IsSpectrumDisconnected Hartshorne.not_isSpectrumDisconnected_of_subsingleton Hartshorne.HasNontrivialOrthogonalIdempotents Hartshorne.HasNontrivialProductDecomposition Hartshorne.isSpectrumDisconnected_iff_orthogonalIdempotents Hartshorne.orthogonalIdempotents_iff_productDecomposition Hartshorne.disconnectedSpectrum_idempotents_products_tfae Hartshorne.isSpectrumDisconnected_iff_not_isConnected
---

# Connected spectra, idempotents, and products

For a commutative ring `A`, the following are equivalent:

1. `Spec A` is disconnected;
2. `1 = e₁ + e₂` for nonzero orthogonal idempotents `e₁,e₂`;
3. `A` is isomorphic to a product `A₁ × A₂` of two nonzero rings.

Here “disconnected” means that the spectrum admits a separation, encoded in
Mathlib as `¬ IsPreconnected univ`.  Thus the empty spectrum of the zero ring
is not disconnected, and all three clauses remain false for that ring.  The
pinned clopen/idempotent correspondence gives the first equivalence directly.
Conversely an idempotent splits the spectrum into the two clopen principal
opens `D(e)` and `D(1-e)`, and complementary idempotents give the ring product
decomposition.  This is Exercise 2.19.

## Depends on

- [The Zariski topology on Spec](../spectrum-and-schemes/spec-zero-loci.md)

## Sources

- [Hartshorne II.2, Exercise 2.19, used in Theorem III.11.3 immediately before Zariski's Main Theorem, Corollary III.11.4](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
