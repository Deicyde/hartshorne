---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.coordEquivalence Hartshorne.AffineVarietyCat Hartshorne.FgDomainCat Hartshorne.coordFunctor Hartshorne.AffineVarietyCat.coordMap Hartshorne.AffineVarietyCat.coordMap_comp Hartshorne.AffineVarietyCat.homEquivCoord Hartshorne.AffineVarietyCat.exists_coordMap_eq Hartshorne.AffineVarietyCat.coordMap_injective Hartshorne.AffineVarietyCat.coordEquiv
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

## The two categories

An object on the variety side is an affine variety sitting in some `𝔸ⁿ`, which
is Hartshorne's category verbatim; morphisms are `VarietyHom`s, and the category
axioms are the ones already proved for those. Restricting the ambient index to
`Fin n` costs nothing: it is what the realization theorem produces, and it keeps
every carrier in a single universe.

The algebra side is a full subcategory of Mathlib's `CommAlgCat k`, cut out by
being an integral domain and finitely generated, so identities, composition and
isomorphisms come from upstream.

## Naturality of Proposition 3.5

Naturality of `Hom(X, Y) ≃ Hom_{k-alg}(A(Y), 𝒪(X))` in both arguments is exactly
functoriality of `X ↦ A(X)`, since the bijection *is* the functor's action on
morphisms; it is discharged as `coordMap_comp` and `coordMap_id`. Both reduce to
functoriality of pullback of regular functions, which holds by `rfl`, with the
two `A ≅ 𝒪` conversions at the ends cancelling.

## One friction worth recording

`Variety` indexes regular functions by open subsets, so its `𝒪(X)` consists of
functions on the top open subset rather than on `X`. Composing anything through
that requires the conversion to be phrased in terms of the same `toVariety` on
both sides; stated through `Variety.ofQuasiAffine` directly, the two are
definitionally equal but neither `rw` nor `simp` will match them. Both the
`A ≅ 𝒪` conversion and Proposition 3.5 are therefore re-exposed as
`coordEquiv` and `homEquivCoord`, indexed by the category's objects.

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
