---
article_id: af_fc163557346aca575b9a0fd2
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-local-structure]
---

# Membership of a homogeneous fraction in a local ring

Let `Y` be quasi-projective, `P ∈ Y`, and let `g,h` be homogeneous polynomials
of the same degree whose fraction defines an element `[g/h] ∈ K(Y)`. If
`g(P) ≠ 0`, then

`[g/h] ∈ Y.localRingRange P ↔ h(P) ≠ 0`.

The forward direction says a fraction with nonvanishing numerator and zero
denominator cannot represent a regular germ at `P`; the reverse direction uses
`g/h` itself on the projective open where `h` is nonzero. The hypothesis on
`g(P)` rules out cancellation, which is essential for the biconditional.

Use the existing `projRatOfFraction` representation of projective rational
functions and identify its germ through the canonical map into `K(Y)`.

## Depends on

- [The function field of a projective variety](../morphisms/projective-rings/projective-function-field.md)
- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)

## Proof depends on

- [The local ring is local](../morphisms/local-ring-is-local.md)
- [The function field is the fraction field of every local ring](local-ring-fraction-field.md)
- [The local ring of a projective variety](../morphisms/projective-rings/projective-local-ring.md)

## Sources

- [Hartshorne I.6, proof of Lemma 6.4 (p. 41)](../../sources/hartshorne.md#i6-local-structure-and-point-separation)
