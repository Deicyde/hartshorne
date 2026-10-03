---
declaration: theorem
origin: bridged
source_units: [chapter-v-section-5]
---

# A finite projective fibre has a quasi-finite neighbourhood

Let `f : Z -> X` be a projective finite-type morphism of Noetherian schemes.
If the fibre over `P : X` is zero-dimensional, then there is an open
neighbourhood `U` of `P` such that

`f^-1(U) -> U`

is quasi-finite.

## Depends on

- [The fibre of a morphism](../../../schemes/fiber-products/scheme-fiber.md)
- [Images of proper schemes](../../../schemes/proper-and-projective/proper-image.md)
- [Morphisms locally of finite type](../../../schemes/first-properties/locally-finite-type.md)

## Proof depends on

- Quasi-finiteness is open on the source for a locally finite-type morphism.
  The finite fibre is contained in that open; projectivity makes the image of
  its closed complement closed, so removing that image gives the required
  target neighbourhood.

## Sources

- [Hartshorne V.5, neighbourhood step in Theorem 5.2, p.411](../../../../sources/hartshorne-v-5.md)
