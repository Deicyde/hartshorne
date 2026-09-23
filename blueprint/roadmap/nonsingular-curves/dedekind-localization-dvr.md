---
article_id: af_f77fddedd3b45d252d8d3124
declaration: theorem
origin: background
source_units: [chapter-i-section-6-valuations]
statement: formalized
lean: Hartshorne.dedekind_localization_dvr
---

# Localizations of a Dedekind domain are DVRs

Let `A` be a Noetherian, integrally closed domain of Krull dimension one, and
let `𝔭` be a nonzero prime ideal. Then the localization `A_𝔭` is a discrete
valuation ring.

These are Hartshorne's definition of a Dedekind domain and the observation
immediately following it. Mathlib's `IsDedekindDomain` permits dimension zero,
so the source-facing theorem retains the explicit dimension-one hypotheses,
packages the corresponding Mathlib instance, and applies
`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`.

## Depends on

No project-local statement prerequisites.

## Sources

- [Hartshorne I.6, definition of a Dedekind domain and the following observation (p. 40)](../../sources/hartshorne.md#i6-valuation-and-dvr-background)
