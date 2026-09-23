---
article_id: af_e1ae36260cfcc00b57e99628
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-abstract-curves]
---

# The local-ring map has open image

Let `Y` be a nonsingular quasi-projective curve with function field `K(Y)`.
Sending a point to the image of its local ring defines a map

`P ↦ 𝒪_{P,Y} : Y → C_{K(Y)}`.

This map is injective, and its image `U` is open in the cofinite valuation
space.  Moreover it is a homeomorphism from `Y` to `U`.

Injectivity is Lemma 6.4.  For openness, it is enough to find a nonempty open
subset of `C_K` contained in the image.  Replace `Y` by a nonempty affine open
with coordinate ring `A`, which is Dedekind.  Its points correspond exactly to
the DVRs containing `A`: one direction is immediate from germs, and the other
uses the center-localization theorem.  If `x_1,…,x_n` generate `A` over `k`,
this set is

`⋂_i {R ∈ C_K | x_i ∈ R}`,

whose complement is finite by Lemma 6.5.  Finally both `Y` and `U` carry the
cofinite topology, so the resulting bijection is a homeomorphism.

Make the affine reduction compatible with the ambient function field: use the
canonical equivalence between the function fields of a variety and a nonempty
open subvariety, and the local-ring equivalence at every point of that open.
Under those transports, the coordinate-ring inclusion, localization at a
point, and resulting valuation subring of `K(Y)` must form commuting triangles.
This is what lets the center computation on the affine open describe the
original point-to-local-ring map.

## Depends on

- [The cofinite valuation space](valuation-space-topology.md)
- [Nonsingular curve points define discrete valuations](../nonsingular-curves/nonsingular-curve-valuation.md)

## Proof depends on

- [The local ring determines the point](../nonsingular-curves/local-ring-inclusion-determines-point.md)
- [A rational function has finitely many poles](finite-poles.md)
- [A DVR containing a Dedekind subring is its localization](dedekind-subring-localization.md)
- [Nonsingular affine curves have Dedekind coordinate rings](nonsingular-affine-curve-dedekind.md)
- [Quasi-projective curves have the cofinite topology](quasiprojective-curve-cofinite.md)
- [Local rings are unchanged on open neighbourhoods](../nonsingular-varieties/local-ring-open-invariance.md)
- [Open affine sets are a base for the topology](../rational-maps/affine-base.md)
- [Rational maps and function fields](../rational-maps/rational-map-function-field.md)

## Sources

- [Hartshorne I.6, proof of Proposition 6.7 (pp. 42--43)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
