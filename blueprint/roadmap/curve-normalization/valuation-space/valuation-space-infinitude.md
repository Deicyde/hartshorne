---
article_id: af_e1eecc8dc2884eefd2335da4
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-abstract-curves]
statement: formalized
proof: formalized
lean: Hartshorne.FunctionFieldDVR.infinite_of_trdeg_eq_one Hartshorne.ValuationSpace.irreducibleSpace_of_trdeg_eq_one Hartshorne.ValuationSpace.infinite_of_isOpen_of_nonempty
---

# The valuation space is infinite

Let `k` be algebraically closed and let `K/k` be an essentially finite-type
field extension with

`Algebra.trdeg k K = 1`.

Then `FunctionFieldDVR k K` is infinite.  Consequently its cofinite valuation
space is irreducible, and every nonempty open subset of that space is infinite.

Choose a separating parameter and one of its finite Dedekind normalization
charts.  Realize that chart as the coordinate ring of a nonsingular affine
curve.  The curve has infinitely many points.  Sending a point to its local
DVR inside `K` is injective because inclusion of local rings determines the
point, so `FunctionFieldDVR k K` is infinite.

In the formal proof, the maximal ideal of each affine point is transported to
a height-one prime of the normalization ring. Its embedded localization in
`K` is a function-field DVR. Injectivity of point maximal ideals and of the
height-one-prime construction gives the required injection directly.

State infinitude as a theorem from the algebraic-closedness, finite-type, and
transcendence-degree hypotheses, not as an unconditional global instance.
Downstream constructions can install it locally; Mathlib then supplies the
`IrreducibleSpace` instance for the cofinite topology.

## Depends on

- [The cofinite valuation space](valuation-space-topology.md)

## Proof depends on

- [The two separable normalization charts](../separable-normalization-charts.md)
- [Dedekind localizations occur on nonsingular affine curves](../dedekind-affine-model.md)
- [Quasi-projective curves have the cofinite topology](../quasiprojective-curve-cofinite.md)
- [Nonsingular curve points define discrete valuations](../../nonsingular-curves/nonsingular-curve-valuation.md)
- [The local ring determines the point](../../nonsingular-curves/local-ring-inclusion-determines-point.md)

## Sources

- [Hartshorne I.6, infinitude of `C_K` (p. 42)](../../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
