---
article_id: af_4e295bffa818324292803ca3
declaration: class
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.UniversallyClosed
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean
---

# Universally closed morphisms

A scheme morphism $f : X \longrightarrow Y$ is universally closed when every pullback
$X\times_YY'\longrightarrow Y'$ is a closed map on underlying topological spaces.

Taking the identity base change shows that every universally
closed morphism is closed. Quantification over arbitrary base
changes is essential: finite type and closedness alone do not
suffice, as the projection $\mathbb A^2_k\to\mathbb A^1_k$ shows.

## Depends on

- [Base extension](../fiber-products/base-extension.md)
- [The universal property of a fiber product](../fiber-products/fiber-product-universal-property.md)

## Proof depends on

- Stability of closed immersions and closed maps under pullback.

## Sources

- [Hartshorne II.4 (properness-and-the-valuative-criterion)](../../../sources/hartshorne-ii-4.md#properness-and-the-valuative-criterion)
