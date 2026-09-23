---
article_id: af_6ae7ab997d79403ec249423a
declaration: def
origin: cited
source_units: [chapter-i-section-6-abstract-curves]
---

# Residue fields of function-field DVRs

Let `R ∈ C_K`.  The algebra map from `k` to the residue field
`κ(R) = R / 𝔪_R` is an isomorphism.  Choose its canonical inverse and
define the residue evaluation

`residueAt R : R →ₐ[k] k`.

Corollary 6.6 realizes `R` as the local ring of a `k`-rational point on an
affine variety.  The residue field at such a point is `k`, by evaluation at
that point. Transport this equivalence through the compatible local-ring
equivalence from Corollary 6.6 and prove that `residueAt` fixes constants. Also
record that, under the affine model, `residueAt R` agrees with evaluation of a
germ at the corresponding point; this is the compatibility used in
Proposition 6.7.

This article's unique main construction is `residueAt`; the residue-field
equivalence and its compatibility lemmas are supporting declarations used to
evaluate rational functions on the valuation space.

## Depends on

- [Discrete valuation rings of a function field](function-field-dvrs.md)

## Proof depends on

- [Every function-field DVR has a nonsingular affine model](dvr-affine-model.md)
- [Points and maximal ideals](../morphisms/points-eq-maximal-ideals.md)
- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)

## Sources

- [Hartshorne I.6, residue fields of points of `C_K` (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
