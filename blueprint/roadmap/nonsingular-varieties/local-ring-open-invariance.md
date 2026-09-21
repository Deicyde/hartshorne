---
article_id: af_b30a1d9b74972ff667ac37db
declaration: theorem
origin: bridged
source_units: [chapter-i-section-5-geometry]
statement: formalized
lean: Hartshorne.Variety.bijective_localRingHom_inclHom Hartshorne.Variety.HasAffineOpenBasis.isNoetherianRing_localRingAt
---

# Local rings are unchanged on open neighbourhoods

Let `U` be a nonempty open subvariety of a variety `X`, and let `P ∈ U`.
The inclusion induces a ring isomorphism

`𝒪_{P,U} ≃ 𝒪_{P,X}`.

This is the local statement used when Hartshorne says that closedness of the
singular locus may be checked on an affine open cover. A germ at `P` has a
representative on a neighbourhood already contained in `U`, and pushing or
restricting that representative gives the two inverse maps. The proof follows
the same quotient-of-germs pattern as the existing affine comparison
`localRingEquivAffine`.

The same pull request also records the corollary needed by the local-algebra
nodes: if `X` has the affine-open-basis witness of Proposition 4.3, every
`𝒪_{P,X}` is Noetherian. Choose an affine open neighbourhood of `P`, use
the displayed equivalence, identify its local ring with the localization of
its coordinate ring, and transfer Noetherianity across the ring equivalences.

## Depends on

- [The local ring at a point](../morphisms/local-ring.md)
- [The local ring is functorial](../morphisms/local-ring-functorial.md)
- [Rational maps](../rational-maps/rational-map.md)
- [Open affine sets are a base for the topology](../rational-maps/affine-base.md)

## Proof depends on

- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)

## Sources

- [Hartshorne I.5, reduction to affine open subsets in Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)
