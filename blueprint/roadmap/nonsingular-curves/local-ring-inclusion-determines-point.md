---
article_id: af_14eaa7de868a5c79cf51f1a0
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-local-structure]
statement: formalized
lean: Hartshorne.IsQuasiProjVariety.eq_of_localRingRange_le
---

# The local ring determines the point

Let `Y` be a quasi-projective variety and `P,Q ∈ Y`. Regard both local rings as
subalgebras of `K(Y)` using `localRingRange`. Then

`𝒪_{Q,Y} ⊆ 𝒪_{P,Y}  →  P = Q`.

This is Lemma 6.4, with the inclusion orientation exactly as in the source. If
`P ≠ Q`, choose linear forms `g,h` with `g(P) ≠ 0`, `g(Q) ≠ 0`,
`h(P) = 0`, and `h(Q) ≠ 0`. The class `[g/h]` belongs to `𝒪_{Q,Y}` but not to
`𝒪_{P,Y}`, contradicting the assumed inclusion.

Hartshorne reaches the same contradiction after moving both points into one
affine chart and comparing localizations. The homogeneous-fraction proof avoids
formalizing a general coordinate-change theorem solely for this lemma and
retains the full quasi-projective statement.

## Depends on

- [Projective and quasi-projective varieties](../projective-varieties/projective-variety.md)
- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)

## Proof depends on

- [Linear fractions separate projective points](projective-linear-separation.md)
- [Membership of a homogeneous fraction in a local ring](homogeneous-fraction-local-membership.md)

## Sources

- [Hartshorne I.6, Lemma 6.4 (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)
