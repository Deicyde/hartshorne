---
article_id: af_ea760d2f38835a90cbc5ed92
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.Spec.toLocallyRingedSpace
mathlib_file: Mathlib/AlgebraicGeometry/Spec.lean
---

# The contravariant Spec functor

The spectrum of every commutative ring is a locally ringed space.  Every ring
homomorphism $\varphi : A \to B$ induces a morphism

$\operatorname{Spec} B \to \operatorname{Spec} A$

whose point map sends $\mathfrak{p}$ to $\varphi ^{-1}(\mathfrak{p} )$ and whose stalk map is the corresponding
localization homomorphism.  Identity and composition make this a functor from
the opposite of commutative rings.

These are the functoriality statements in Hartshorne's
Proposition II.2.3(a,b).

## Depends on

- [The stalk of Spec](spec-stalk.md)
- [Locally ringed spaces](locally-ringed-space.md)

## Sources

- [Hartshorne II.2, Proposition 2.3(a),(b) (p. 73)](../../../sources/hartshorne-ii-2.md#locally-ringed-spaces-and-proposition-23)
