---
article_id: af_6ae7ab997d79403ec249423a
declaration: def
origin: cited
source_units: [chapter-i-section-6-abstract-curves]
statement: formalized
proof: formalized
lean: Hartshorne.FunctionFieldDVR.residueAt
---

# Residue fields of function-field DVRs

Let `k` be algebraically closed, let `K/k` be an essentially finite-type field
extension with `Algebra.trdeg k K = 1`, and let `R ∈ C_K`.  The algebra map
from `k` to the residue field
`κ(R) = R / 𝔪_R` is an isomorphism.  Package its canonical inverse as

`residueFieldEquiv R : IsLocalRing.ResidueField R.toValuationSubring ≃ₐ[k] k`

and define the residue evaluation as the quotient map followed by this
equivalence:

`residueAt R : R.toValuationSubring →ₐ[k] k`.

Corollary 6.6 realizes `R` as the local ring of a `k`-rational point on an
affine variety.  The residue field at such a point is `k`, by evaluation at
that point. Transport this equivalence through the compatible local-ring
equivalence `e_R` from Corollary 6.6 and prove that `residueAt` fixes constants.
Also record the pointwise compatibility

`residueAt R (e_R z) = evalAtPoint z`

for every `z : Hartshorne.LocalRingAt hY.isIrreducible P`, using the same
affine-model data `hY`, `P`, and `e_R` as the preceding article. This is the
compatibility used in Proposition 6.7.

This article's unique main construction is `residueAt`; the residue-field
equivalence and its compatibility lemmas are supporting declarations used to
evaluate rational functions on the valuation space.

## Depends on

- [Discrete valuation rings of a function field](function-field-dvrs.md)

## Proof depends on

- [Every function-field DVR has a nonsingular affine model](dvr-affine-model.md)
- [The local ring is local](../morphisms/local-ring-is-local.md)

## Sources

- [Hartshorne I.6, residue fields of points of `C_K` (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
