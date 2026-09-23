---
article_id: af_a80104f765e1ab68f0ef60db
declaration: theorem
origin: bridged
source_units: [theorem-i-6-3a]
---

# Finite-length quotients in Krull--Akizuki

Let `A` be a one-dimensional Noetherian domain with fraction field `K`, let
`L/K` be finite, and let `B` be an intermediate `A`-subalgebra of `L`. For
every nonzero ideal `I` of `B`, the quotient `B/I` has finite length as an
`A`-module. In particular, it is a finite `A`-module.

This is the finiteness lemma at the heart of the Krull--Akizuki theorem. First
show that every nonzero ideal `I` of `B` meets `A` nontrivially. Bound the
`A`-rank of `B` by `[L : K]`, choose `0 ≠ a ∈ I ∩ A`, and compare `B/aB` with
a free module of that finite rank. Since `A/(a)` is Artinian, the comparison
gives finite `A`-length for `B/aB`, hence for its quotient `B/I`. The result
must apply to an arbitrary intermediate ring `B`; assuming that `B` is already
finite or integral over `A` would make the later Krull--Akizuki step circular.

Open Mathlib PR
[#41755](https://github.com/leanprover-community/mathlib4/pull/41755)
contains the closely matching declaration
`krullAkizuki_quotient_ideal_finiteLength`. Treat it as implementation prior
art only: the roadmap targets the pinned checkout and does not assume the PR
will merge.

## Depends on

No project-local statement prerequisites.

## Sources

- [Hartshorne I.6, Theorem 6.3A and its cited algebraic input (p. 40)](../../sources/hartshorne.md#i6-integral-closure-theorem)
- [Stacks Project, the finite-length step before Krull–Akizuki (Tag 00PF)](https://stacks.math.columbia.edu/tag/00PF)
- [Stacks Project, Krull–Akizuki (Tag 00PG)](https://stacks.math.columbia.edu/tag/00PG)
