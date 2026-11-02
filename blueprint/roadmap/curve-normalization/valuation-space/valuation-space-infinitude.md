---
article_id: af_e1eecc8dc2884eefd2335da4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.FunctionFieldDVR.infinite_of_trdeg_eq_one Hartshorne.ValuationSpace.irreducibleSpace_of_trdeg_eq_one Hartshorne.ValuationSpace.infinite_of_isOpen_of_nonempty
---

# The valuation space is infinite

Let $k$ be algebraically closed and let $K/k$ be a finitely generated
field extension of transcendence degree one. Then $C_K$ is infinite.
Consequently its cofinite topology is irreducible and every nonempty open
subset is infinite.

Choose a separating parameter and a Dedekind normalization chart. Realize
it as the coordinate ring of a nonsingular affine curve, which has infinitely
many points. Sending a point to its local discrete valuation ring inside
$K$ is injective because the local ring determines the point. This gives
an injection of an infinite point set into $C_K$.

## Depends on

- [The cofinite valuation space](valuation-space-topology.md)

## Proof depends on

- [The two separable normalization charts](../separable-normalization-charts.md)
- [Dedekind localizations occur on nonsingular affine curves](../dedekind-affine-model.md)
- [Quasi-projective curves have the cofinite topology](../quasiprojective-curve-cofinite.md)
- [Nonsingular curve points define discrete valuations](../../nonsingular-curves/nonsingular-curve-valuation.md)
- [The local ring determines the point](../../nonsingular-curves/local-ring-inclusion-determines-point.md)

## Sources

- [Hartshorne I.6, infinitude of $C _K$ (p. 42)](../../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
