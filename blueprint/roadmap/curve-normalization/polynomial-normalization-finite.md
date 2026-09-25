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

## Provenance

The conclusion also follows from the stronger Nagata theorem in Stacks
Project, Tag 0335. The decomposition here is project-authored, assembled from
the sourced maximal separable subextension, separable integral-closure,
transitivity, and finite-map inputs together with the preceding inseparable
bridge. It is therefore an intermediate bridge rather than a direct
Hartshorne target.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Purely inseparable normalizations are finite](purely-inseparable-normalization-finite.md)

## Sources

- [Project-authored proof specification for Hartshorne I.3.9A](../../sources/hartshorne.md#project-authored-proof-specification-for-theorem-i39a)
- [Stacks Project, finite-type algebras over fields are Nagata (Tag 0335)](https://stacks.math.columbia.edu/tag/0335)
- [Stacks Project, Japanese and N-2 rings (Tag 032F)](https://stacks.math.columbia.edu/tag/032F)
- [Stacks Project, maximal separable subextension (Tag 030K)](https://stacks.math.columbia.edu/tag/030K)
- [Stacks Project, finite separable integral closure (Tag 032L)](https://stacks.math.columbia.edu/tag/032L)
- [Stacks Project, transitivity of integral closure (Tag 0308)](https://stacks.math.columbia.edu/tag/0308)
- [Stacks Project, composition of finite ring maps (Tag 00GL)](https://stacks.math.columbia.edu/tag/00GL)
