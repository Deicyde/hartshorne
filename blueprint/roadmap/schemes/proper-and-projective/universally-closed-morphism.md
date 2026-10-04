---
article_id: af_4e295bffa818324292803ca3
declaration: class
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.UniversallyClosed
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean
---

# Universally closed morphisms

A scheme morphism `f : X ⟶ Y` is universally closed when every pullback
`X ×[Y] Y' ⟶ Y'` is a closed map on underlying topological spaces.

Use Mathlib's universal closure of the topological closed-map morphism
property. The identity base change recovers that every universally closed map
is closed. Keeping the quantification over arbitrary scheme morphisms is
essential: the projection `𝔸²_k → 𝔸¹_k` shows that finite type and closedness
alone do not suffice.

## Depends on

- [Base extension](../fiber-products/base-extension.md)
- [The universal property of a fiber product](../fiber-products/fiber-product-universal-property.md)

## Proof depends on

- Stability of closed immersions and closed maps under pullback.

## Sources

- [Hartshorne II.4 (properness-and-the-valuative-criterion)](../../../sources/hartshorne-ii-4.md#properness-and-the-valuative-criterion)
