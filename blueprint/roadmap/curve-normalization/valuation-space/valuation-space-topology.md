---
article_id: af_83a64170587955ab5c10023b
declaration: def
origin: cited
source_units: [chapter-i-section-6-abstract-curves]
---

# The cofinite valuation space

For a field extension `K/k`, define the valuation space to be

`C_K = CofiniteTopology (FunctionFieldDVR k K)`.

Thus a subset is closed exactly when it is finite or is all of `C_K`.  Expose
the identity equivalence with `FunctionFieldDVR k K` and the resulting
open-set and closed-set characterizations used downstream.  This definition
does not require finite generation or a dimension hypothesis.

Use Mathlib's `CofiniteTopology` rather than defining a second topology with
the same closed sets.

## Depends on

- [Discrete valuation rings of a function field](../function-field-dvrs.md)

## Sources

- [Hartshorne I.6, the cofinite topology on `C_K` (p. 42)](../../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
