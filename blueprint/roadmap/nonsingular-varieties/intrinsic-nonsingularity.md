---
article_id: af_2ff2bb8fe76379abcf802044
declaration: def
origin: cited
source_units: [chapter-i-section-5-geometry]
---

# Intrinsic nonsingularity

For a variety `X` and a point `P`, define

`NonsingularAt X P :⇔ IsRegularLocalRing (𝒪_{P,X})`.

Define `Nonsingular X` by requiring this at every point, define
`SingularLocus X = {P | ¬ NonsingularAt X P}`, and call `X` singular when it
is not nonsingular. These are Hartshorne's intrinsic definitions immediately
after Theorem 5.1.

The node also proves the two compatibility statements that make the definitions
usable. For an affine variety the intrinsic predicate agrees with the Jacobian
predicate by Theorem 5.1 and `localRingEquivAffine`. If `U` is an open
neighbourhood of `P`, then `P` is nonsingular in `U` exactly when it is
nonsingular in `X`, because their local rings are isomorphic and regularity is
invariant under ring equivalence. Likewise, an isomorphism of varieties carries
nonsingular points to nonsingular points; this is the form used in the
birational reduction for Theorem 5.3.

## Depends on

- [The Jacobian criterion](jacobian-criterion.md)
- [Local rings are unchanged on open neighbourhoods](local-ring-open-invariance.md)
- [The local ring at a point](../morphisms/local-ring.md)

## Proof depends on

- [The local ring is functorial](../morphisms/local-ring-functorial.md)

## Sources

- [Hartshorne I.5, intrinsic definitions of nonsingular and singular varieties (p. 32)](../../sources/hartshorne.md#i5)
