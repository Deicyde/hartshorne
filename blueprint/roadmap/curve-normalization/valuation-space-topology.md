---
article_id: af_83a64170587955ab5c10023b
declaration: def
origin: cited
source_units: [chapter-i-section-6-abstract-curves]
---

# The cofinite valuation space

For a one-dimensional function field `K/k`, equip `C_K` with the cofinite
topology: a subset is closed exactly when it is finite or is all of `C_K`.
Call the resulting topological space the valuation space of `K/k`.

Show that `C_K` is infinite.  Choose a normalization model of `K`, realize it
as a nonsingular affine curve, and send each point to its local DVR in `K`.
The curve has infinitely many points, and Lemma 6.4 makes this map injective.
It follows that the cofinite valuation space is irreducible; expose the
corresponding `Infinite` and `IrreducibleSpace` instances needed by the
abstract-curve construction.

Use Mathlib's `CofiniteTopology` rather than defining a second topology with
the same closed sets.

## Depends on

- [Discrete valuation rings of a function field](function-field-dvrs.md)

## Proof depends on

- [The two separable normalization charts](separable-normalization-charts.md)
- [Dedekind localizations occur on nonsingular affine curves](dedekind-affine-model.md)
- [Quasi-projective curves have the cofinite topology](quasiprojective-curve-cofinite.md)
- [Nonsingular curve points define discrete valuations](../nonsingular-curves/nonsingular-curve-valuation.md)
- [The local ring determines the point](../nonsingular-curves/local-ring-inclusion-determines-point.md)

## Sources

- [Hartshorne I.6, definition and infinitude of `C_K` (p. 42)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
