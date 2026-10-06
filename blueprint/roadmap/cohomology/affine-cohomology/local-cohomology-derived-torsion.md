---
article_id: af_91220b35caef1aca051b5e58
declaration: definition
origin: cited
source_units: [chapter-iii-sections-1-4]
statement: formalized
proof: formalized
lean: Hartshorne.idealPowerTorsionFunctor Hartshorne.localCohomology Hartshorne.localCohomologyObject Hartshorne.localCohomologyZeroIso
---

# Algebraic local cohomology as derived torsion

For a Noetherian ring `A` and ideal `a`, the ideal-power torsion functor

`Γ_a(M) = {m | a^n m = 0 for some n}`

is left exact. Define `H_a^i(M)` to be its right derived functors in
`A`-modules.

## Depends on

- [Right derived functors](../derived-functors/right-derived-functors.md)

## Proof depends on

- `Submodule.primaryComponent` models the degree-zero functor.
- Mathlib's Ext-colimit local cohomology is only a partial primitive and is
  not used definitionally.

## Sources

- [Hartshorne III, Exercise 3.3(a) (p.217)](../../../sources/hartshorne-iii-3-4.md#local-cohomology-exercises)
- [Local-cohomology representation choice](../../../sources/hartshorne-iii-3-4.md#project-authored-representation-choices)
