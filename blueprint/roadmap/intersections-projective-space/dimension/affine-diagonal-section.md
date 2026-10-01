---
article_id: af_cbb14bbd237a44288abce54a
declaration: def
origin: bridged
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.affineDiagonalSectionHomeomorph
---

# The diagonal section of an affine product

For `Y,Z ⊆ 𝔸^σ`, let the diagonal equations in the affine product on
`σ ⊕ σ` be

`X_(inl i) - X_(inr i) = 0` for `i : σ`.

There is a canonical homeomorphism from `Y ∩ Z` to the intersection of
`affineProduct Y Z` with their common zero locus.  The sole main declaration
is planned as `Hartshorne.affineDiagonalSectionHomeomorph`.

The forward map sends `P` to the pair `P × P`; the inverse restricts either
coordinate block.  Record alongside the construction that the diagonal family
is finite with cardinality at most `Nat.card σ`, that the homeomorphism
preserves dimension, and that it transports irreducible components.  These
facts are the precise interface needed by Proposition 7.1.

## Depends on

- [Affine products are varieties](affine-product-variety.md)
- [Dimension of a topological space and of a ring](../../affine-varieties/dimension.md)

## Proof depends on

- [The Zariski topology on affine space](../../affine-varieties/zariski-topology.md)
- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne I.7, diagonal reduction in the proof of Proposition 7.1](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
