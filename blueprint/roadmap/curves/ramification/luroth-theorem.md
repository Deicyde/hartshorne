---
declaration: def
origin: cited
source_units: [chapter-iv-sections-1-2]
mathlib: true
mathlib_declaration: RatFunc.Luroth.algEquiv
mathlib_file: Mathlib/FieldTheory/RatFunc/Luroth.lean
---

# Lüroth's theorem

Let `k` be a field and let `L` be an intermediate field between `k` and the
rational function field `k(t)`. If `L != k`, then there is a `k`-algebra
isomorphism

`k(t) ~= L`.

Equivalently, `L=k(u)` for a transcendental element `u`. Hartshorne derives
the result over algebraically closed `k` from genus monotonicity. The pinned
Mathlib declaration `RatFunc.Luroth.algEquiv` proves the stronger theorem over
an arbitrary field and supplies the exact algebra equivalence.

## Depends on

No project-local prerequisites; the exact field-theoretic result is supplied
by pinned Mathlib.

## Sources

- [Hartshorne IV.2, Example 2.5.5, p.303](../../../sources/hartshorne-iv-2.md#consequences-pp302303)
- P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*, Theorem 11.3.4, as
  cited by the pinned Mathlib implementation.
