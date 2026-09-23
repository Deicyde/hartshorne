---
article_id: af_7a8650a3a8f379e0ba31aae1
declaration: theorem
origin: bridged
source_units: [theorem-i-3-9a]
---

# Normalizations of polynomial rings are finite

Let `k` be algebraically closed, let `P = k[X_1,\ldots,X_n]`, let `F` be its
fraction field, and let `L/F` be a finite field extension.  Then the integral
closure of `P` in `L` is a finite `P`-module, without assuming that `L/F` is
separable.

Let `M` be the maximal separable intermediate field.  The pinned Mathlib
theorem `IsIntegralClosure.finite` makes the integral closure of `P` in `M`
finite over `P`.  That ring is again a normal finitely generated `k`-domain,
and `L/M` is finite and purely inseparable, so the purely inseparable
normalization theorem applies.  Transitivity of integrality identifies the
resulting iterated integral closure with the integral closure of `P` in `L`.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Purely inseparable normalizations are finite](purely-inseparable-normalization-finite.md)

## Sources

- [Hartshorne I.3, Theorem 3.9A (p. 20)](../../sources/hartshorne.md#i3)
