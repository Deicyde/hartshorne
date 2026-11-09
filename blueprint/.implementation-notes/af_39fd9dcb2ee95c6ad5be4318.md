# Birational invariance of regular q-forms

## Status

Not stated or proved in Lean. A bounded attempt (Formalize pass of 2026-11-09)
surveyed the available pieces and stopped: the proof needs two constructions that
no article or module provides yet (items 1 and 2 under "Missing pieces"), and the
analogous `q = n` argument (Theorem 8.19, articles
`canonical-bertini/canonical-pullback-injective` and
`canonical-bertini/geometric-genus-birational-invariant`) is itself not
formalized. Those pieces should land first, ideally as their own articles.

## Target shape

Schemes over `Spec k`, in the conventions of
`AlgebraicGeometry.Scheme.RationalMap.codim_compl_domain_birational`
(`Hartshorne.Scheme.Differentials.BirationalMapDomain`): `[X.Over (Spec (.of k))]`,
`IsIntegral X`, `IsSeparated`/`IsProper (X ↘ Spec (.of k))`, `X.IsRegular`, and a
birational map given as `T : X ⤏ X'` with
`∃ f : X.PartialIso X', f.IsOver (X ↘ _) (X' ↘ _) ∧ f.toRationalMap = T`.

- `h^{q,0}(X) = finrank k Γ(X, ⋀^q Ω_{X/k})`, with `⋀^q` the project's
  `Hartshorne.moduleSheafExteriorPower q (Scheme.relativeDifferentials (X ↘ Spec (.of k)))`.
  `Γ(X, M)` needs its `k`-module structure through
  `(X ↘ Spec (.of k)).appTop` and `Scheme.ΓSpecIso`; no project helper for this was
  found. Prove equality of `Module.rank` first (injections both ways and
  `le_antisymm`), so no finite-dimensionality theorem is needed; `finrank`
  equality follows.

## Available Lean (checked to exist on this base)

- Domain of a birational map has codimension-two complement:
  `AlgebraicGeometry.Scheme.RationalMap.codim_compl_domain_birational`.
- Sections of a finite locally free sheaf extend across codimension two:
  `AlgebraicGeometry.Scheme.Modules.bijective_presheaf_map_top_of_two_le_codim`
  (needs `[IsIntegral X] [IsNoetherian X] [Hartshorne.IsNormal X]` and
  `E.IsLocallyFreeOfRank r`); regular implies normal: `isNormal_of_isRegular`.
- Pullback of differentials along a morphism:
  `AlgebraicGeometry.Scheme.pullbackRelativeDifferentialsToComp`
  (`f^* Ω_{Y/Z} ⟶ Ω_{X/Z}`, `Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity`).
- Exterior powers of a module sheaf and of semilinear maps:
  `Hartshorne.moduleSheafExteriorPower`, `Hartshorne.SheafTensorOperations.exteriorPowerMap`,
  and the sheaf-level functoriality `Hartshorne.ExteriorPowerExactFiltration.extMap`.
- Local freeness of `⋀^q` of a rank-`n` locally free module (rank `n choose q`):
  `Hartshorne.Ringed.IsLocallyFreeOfRank.moduleSheafExteriorPower`, on branch
  `frontier/w30b` (canonical-sheaf leaf, in review), not yet on this base. With
  II.8.15 (`Hartshorne.isRegular_iff_relativeDifferentials_isLocallyFreeOfRank`) it
  makes `⋀^q Ω_{X/k}` locally free on a nonsingular variety.

## Missing pieces (exact remaining goals)

1. Pullback of `q`-forms along a morphism `φ : V ⟶ X'` over `k`: a `k`-linear map
   `Γ(X', ⋀^q Ω_{X'/k}) → Γ(V, ⋀^q Ω_{V/k})`. Route: a sheaf map
   `φ^* (⋀^q E) ⟶ ⋀^q (φ^* E)` (by adjunction, `⋀^q E ⟶ φ_* ⋀^q (φ^* E)`: on the
   presheaf `U ↦ ⋀^q E(U)` apply `exteriorPowerMap` to the unit
   `E(U) → (φ^* E)(φ⁻¹ U)`, then the sheafification universal property), followed by
   `extMap` of `pullbackRelativeDifferentialsToComp`, then global sections and the unit
   `M ⟶ φ_* φ^* M`.
2. Injectivity of the map in (1) when `φ` is birational: on a dense open `W ⊆ V`
   where `φ` restricts to an isomorphism onto an open of `X'`, the map is an
   isomorphism (Ω and `⋀^q` commute with restriction to opens:
   `AlgebraicGeometry.RelDiffLocal.restrictIso`,
   `Hartshorne.moduleSheafExteriorPowerRestrictIso`), and a section of a locally free
   sheaf on an integral scheme that vanishes on a dense open is zero. This is the
   `q`-form version of `canonical-bertini/canonical-pullback-injective`.
3. Assembly: for `T : X ⤏ X'` birational with domain `V = T.domain`, compose (1) for
   the representative on `V` with the inverse of the codimension-two extension
   bijection on `X`; injective by (2). Symmetrically for `T⁻¹`. Then rank equality.

## Roadmap observations (for the lead)

- The `## Depends on` list lacks the pullback-injection step (item 2) and the
  local-freeness of `⋀^q Ω` (the exterior-power rank lemma above); the prose
  "Proof depends on" bullets describe them. A split mirroring Theorem 8.19
  (a `q`-form pullback-injective article, depending on
  `canonical-pullback-injective`'s method) would make this leaf
  pull-request-sized.
