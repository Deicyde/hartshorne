# Birational invariance of regular q-forms

## Status

Lean written on frontier/w20g but not yet compiled: host load was above 150. Nothing is recorded.
The missing pieces listed in the earlier version of this note now exist (canonical-pullback-injective,
plurigenus-birational-invariant and geometric-genus-birational-invariant machinery).

## Lean written (WIP)

- `Hartshorne.regularFormDimension f q = finrank_k Γ(X, ⋀^q Ω_{X/k})`, with `Γ` the `k`-space
  `GlobalSectionsOver` (module `Hartshorne.Scheme.Differentials.PlurigenusBirational`).
- `Hartshorne.regularFormDimension_eq_of_birational`: `k` algebraically closed; `X`, `X'`
  integral, regular, proper over `k`, with `∃ e : X.PartialIso X', e.IsOver pX pX'`; then
  `regularFormDimension pX q = regularFormDimension pX' q` for all `q`.
- `rank_globalSections_exteriorPower_le_of_partialIso` generalizes the geometric-genus rank
  lemma from `n = dim X` to any `q`. `geometricGenus_eq_of_birational` now uses it at `q = n`,
  with its statement unchanged.
- `isLocallyFreeOfRank_exteriorPower_relativeDifferentials`: `⋀^q Ω_{X/k}` is locally free of rank
  `n choose q` (II.8.15 plus `Ringed.IsLocallyFreeOfRank.moduleSheafExteriorPower`).
- In CanonicalPullback, `presheaf_map_injective_of_isLocallyFreeOfRank` generalizes the invertible
  case (now a one-line corollary), and `injective_app_top_of_comp_eq_unit` takes `F` locally free
  of rank `r` instead of invertible (it is not recorded).

## Remaining

1. Compile CanonicalPullback and PlurigenusBirational and fix any errors.
2. Default build, axioms, the unusedArguments lint, check, audit and dag-reach. Expect possible
   link requests: canonical-pullback-injective, serre-normality-criterion, geometric-genus.
3. Record `lean: Hartshorne.regularFormDimension_eq_of_birational Hartshorne.regularFormDimension`
   and delete this note.
