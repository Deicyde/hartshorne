---
article_id: af_cf2398d956660cee93095537
declaration: theorem
origin: bridged
source_units: [theorem-i-6-3a]
statement: formalized
proof: formalized
lean: Hartshorne.krullAkizuki_isNoetherianRing Hartshorne.krullAkizuki_krullDimLE_one Hartshorne.krullAkizuki_dimensionLEOne Hartshorne.krull_akizuki
---

# The Krull--Akizuki theorem

Let `A` be a one-dimensional Noetherian domain with fraction field `K`, let
`L/K` be a finite field extension, and let `B` be any intermediate ring
`A ⊆ B ⊆ L`.  Then `B` is Noetherian and has Krull dimension at most
one.

For a nonzero ideal `I` of `B`, choose `0 ≠ x ∈ I`. Finite `A`-length of
`B/xB` makes its submodule `I/xB` finite over `A`. Lift a finite set of
`A`-module generators and adjoin `x`; these elements generate `I` as a
`B`-ideal. The zero ideal is already finitely generated, so `B` is Noetherian.
For a nonzero prime `𝔭` of `B`, finite length makes `B/𝔭` Artinian; because it
is also a domain, it is a field. Thus every nonzero prime is maximal and prime
chains have length at most one.

Record the Noetherian conclusion together with both pinned-compatible dimension
interfaces, `Ring.KrullDimLE 1 B` and `Ring.DimensionLEOne B`, as well as in one
packaged theorem. The integral-closure wrapper consumes the legacy
`Ring.DimensionLEOne` class used by the pinned `IsDedekindDomain` API.

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

- [Hartshorne I.6, Theorem 6.3A and its cited algebraic input (p. 40)](../../../sources/hartshorne.md#i6-integral-closure-theorem)
- [Stacks Project, Krull–Akizuki (Tag 00PG)](https://stacks.math.columbia.edu/tag/00PG)
