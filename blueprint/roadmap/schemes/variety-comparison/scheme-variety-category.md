---
declaration: structure
origin: bridged
source_units: [chapter-ii-sections-1-3]
---

# The scheme-variety source category

Define the source category for Proposition 2.6 to have objects consisting of a
project `Variety k` together with its existing `Variety.HasAffineOpenBasis`
witness, and morphisms the existing `VarietyHom`s.

Hartshorne's varieties are affine, quasi-affine, projective, or
quasi-projective, and the project has already proved this affine-basis property
for each constructor.  The extra field prevents a false generalization: the
bare project `Variety` axioms describe regular functions but do not imply local
affineness.

## Depends on

- [Affine sets form a basis](../../rational-maps/affine-base.md)
- [Varieties](../../morphisms/variety.md)
- [Morphisms](../../morphisms/morphism.md)

## Sources

- [Hartshorne II.2, domain of Proposition 2.6 and the representation decision](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)
