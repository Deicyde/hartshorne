---
article_id: af_23b2537cc3ff2433010bec6d
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.projectiveDiagonal_localRingRange_eq
---

# Local rings of the diagonal model

For a `ProjectiveDiagonalModel` and every `P ∈ C_K`, the map induced by its
projective diagonal identifies the image of `𝒪_{φ(P),Y}` in the common
function field `K` with the valuation ring `P`.  The sole main declaration is
formalized as
`Hartshorne.projectiveDiagonal_localRingRange_eq`.

This records Hartshorne's sandwich

`𝒪_{φᵢ(P),Yᵢ} ⊆ 𝒪_{φ(P),Y} ⊆ 𝒪_{P,C_K}`

inside `K`; the outer composite is an isomorphism on a chart, so both
inclusions are equalities.  Abstract isomorphisms between the three rings are
insufficient for the subsequent point argument.  Bijectivity of each induced
local-ring map is a supporting consequence for Exercise 3.3(b).  The range
equality and bijectivity must use the same packaged field identification and
projection identities as the preceding function-field leaf.

## Depends on

- [The projective diagonal model](projective-diagonal.md)
- [The local ring is functorial](../morphisms/local-ring-functorial.md)
- [The function field of the diagonal model](projective-model-function-field.md)

## Proof depends on

- [The local ring of an abstract curve](abstract-curve-local-ring.md)
- [Dense morphisms inject on local rings](dominant-morphism-local-ring.md)
- [A two-chart affine cover of the valuation curve](two-affine-chart-cover.md)
- [Local rings are unchanged on open neighbourhoods](../nonsingular-varieties/local-ring-open-invariance.md)

## Sources

- [Hartshorne I.6, local-ring sandwich in the proof of Theorem 6.9 (p. 45)](../../sources/hartshorne.md#i6-projective-models)
