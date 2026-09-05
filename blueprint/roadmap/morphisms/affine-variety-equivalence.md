---
declaration: theorem
origin: cited
---

# Equivalence with finitely generated domains

The functor `X ↦ A(X)` is an arrow-reversing equivalence between the category of
affine varieties over `k` and the category of finitely generated integral domains
over `k` (Corollary 3.8).

Fully faithful is Proposition 3.5 with `X` affine, using `𝒪(X) ≅ A(X)`.
Essentially surjective is
[the realization theorem](../affine-varieties/coordinate-ring-realization.md),
Hartshorne's Remark 1.4.6. Functoriality and arrow reversal come from the
naturality of `α`.

This is where Chapter I's first three sections are heading. It is the precise
statement that affine algebraic geometry over an algebraically closed field and
the commutative algebra of finitely generated domains are the same subject, and
it is the classical shadow of the `Spec`–`Γ` adjunction that Chapter II makes
into the definition of a scheme. Mathlib already has that adjunction as
`AlgebraicGeometry.ΓSpec.adjunction`; this node is the variety-level statement,
which is not a consequence of it.

## Depends on

- [Morphisms into an affine variety](hom-affine-bijection.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)
- [Morphisms](morphism.md)

## Proof depends on

- [Isomorphism via coordinate rings](affine-iso-iff-algebra-iso.md)
- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)
- [Points and maximal ideals](points-eq-maximal-ideals.md)
- [Every finitely generated domain is a coordinate ring](../affine-varieties/coordinate-ring-realization.md)

## Sources

- [Hartshorne I.3, Corollary 3.8 (p. 20)](../../sources/hartshorne.md#i3)
