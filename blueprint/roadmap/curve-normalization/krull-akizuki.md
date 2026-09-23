---
article_id: af_cf2398d956660cee93095537
declaration: theorem
origin: bridged
source_units: [theorem-i-6-3a]
---

# The Krull--Akizuki theorem

Let `A` be a one-dimensional Noetherian domain with fraction field `K`, let
`L/K` be a finite field extension, and let `B` be any intermediate ring
`A ⊆ B ⊆ L`.  Then `B` is Noetherian and has Krull dimension at most
one.

For a nonzero ideal `I` of `B`, finite `A`-length of `B/I` controls the ideals
above `I`; the usual Krull--Akizuki argument then gives a finite generating set
for every ideal of `B`. The zero ideal is already finitely generated. Prime
chains have length at most one because a nonzero prime contracts, after
clearing denominators, to the one-dimensional base.

Record the Noetherian and dimension conclusions separately as well as in one
packaged theorem; the integral-closure wrapper consumes both.

Open Mathlib PR
[#41755](https://github.com/leanprover-community/mathlib4/pull/41755)
provides a full implementation with headline declarations
`krullAkizuki_isNoetherianRing`, `krullAkizuki_krullDimLE_one`, and
`krull_akizuki`. It is useful prior art, but not an upstream dependency of the
pinned project.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [Finite-length quotients in Krull--Akizuki](krull-akizuki-quotient-finite.md)

## Sources

- [Hartshorne I.6, Theorem 6.3A and its cited algebraic input (p. 40)](../../sources/hartshorne.md#i6-integral-closure-theorem)
- [Stacks Project, Krull–Akizuki (Tag 00PG)](https://stacks.math.columbia.edu/tag/00PG)
