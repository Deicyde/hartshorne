---
article_id: af_58af7832c8e46634704bb4df
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.finiteType_affineSource_algebra
---

# Affine source opens of a finite-type morphism

Let `f : X → Y` be finite type, let `V = Spec B` be affine in `Y`, and let
`U = Spec A` be any affine open contained in `f⁻¹(V)`. Then `A` is a finitely
generated `B`-algebra.

Cover `f⁻¹(V)` by finitely many affine opens of finite type and apply the
locality theorem for finite-type algebras to the affine open `U`.

## Depends on

- [The finite affine-cover criterion for finite type](finite-type-finite-affine-cover.md)

## Proof depends on

- The same principal-localization descent pattern as Proposition 3.2, applied
  to finite generation rather than Noetherianity.

## Sources

- [Hartshorne II.3, Exercise 3.3(c) (p. 91)](../../../sources/hartshorne-ii-3.md#finite-type-and-finite-morphisms)
