---
article_id: af_860f4cc4dfa97f0017c8d7df
declaration: theorem
origin: background
source_units: [chapter-i-section-6-valuations]
statement: formalized
lean: Hartshorne.dvr_characterizations
---

# Characterizations of discrete valuation rings

Let `A` be a Noetherian local domain of Krull dimension one, with maximal ideal
`𝔪`. Then the following conditions are equivalent:

1. `A` is a discrete valuation ring;
2. `A` is integrally closed;
3. `A` is a regular local ring;
4. `𝔪` is principal.

This is Theorem 6.2A. The pinned Mathlib theorem
`IsDiscreteValuationRing.TFAE` supplies the DVR, integral-closure, and
principal-maximal-ideal implications, while
`IsRegularLocalRing.iff_finrank_cotangentSpace` and
`IsLocalRing.finrank_CotangentSpace_eq_one_iff` provide the regular-local
clause. A project wrapper is needed because no single upstream declaration has
Hartshorne's exact hypotheses and four conclusions.

## Depends on

- [Regular local rings](../nonsingular-varieties/regular-local-rings.md)

## Sources

- [Hartshorne I.6, Theorem 6.2A (p. 40)](../../sources/hartshorne.md#i6-valuation-and-dvr-background)
