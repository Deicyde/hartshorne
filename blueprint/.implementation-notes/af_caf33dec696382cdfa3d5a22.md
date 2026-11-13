# Vector bundles on curves are successive extensions of line bundles

Lean module: `Hartshorne.Curve.VectorBundleLineFiltration`, with helper modules
`Hartshorne.RingedSpace.InvertibleTensorEquivalence` and `Hartshorne.Scheme.LocallyFreeExtension`.

## Status: candidate

- `Hartshorne.exists_lineBundleFiltration`: the article's statement. Hypotheses: `k` algebraically
  closed, `C` integral with `C.IsNonsingularCurve k` and `Projective (C ↘ Spec k)`, and
  `E.IsLocallyFreeOfRank r`. Conclusion: `Fil : ℕ → Subobject E` with `Fil 0 = ⊥`, `Fil r = ⊤`,
  `Monotone Fil`, `Fil i` locally free of rank `i` for `i ≤ r`, and the cokernel of
  `Subobject.ofLE (Fil i) (Fil (i + 1))` invertible for `i < r`.
- `Hartshorne.exists_lineBundleFiltration_of_projective`: the same for any integral projective
  `k`-scheme of dimension one (regularity is not used); the article form is a corollary.

## Hypotheses

The article says "nonsingular curve". The printed hint twists by a sufficiently ample sheaf, so
the Lean takes the curve projective (the Chapter V reading: base curves of ruled surfaces are
projective). A proof for non-projective nonsingular curves would need either quasi-projectivity
of curves or the structure of projective modules over Dedekind domains; neither is available.

## Route

Induction on `r`, following the printed hint.

- `r = 0`: a rank-zero sheaf is zero (`Ringed.isZero_of_isLocallyFreeOfRank_zero`).
- Step (private `lineFiltration_of_shortExact`): from `0 → A → E → E' → 0` with `A` invertible and
  a filtration `(E'_j)` of `E'`, set `E_0 = ⊥`, `E_{j+1} = p⁻¹(E'_j)` (`Subobject.pullback`).
  `shortExact_pullback_subobject` gives `0 → A → p⁻¹(E'_j) → E'_j → 0`;
  `isLocallyFreeOfRank_of_shortExact` (stalks split, constant fibre dimension criterion) makes
  `p⁻¹(E'_j)` locally free of rank `j + 1`; `isIso_cokernelMap_ofLE_pullback_subobject` (pullback
  square of inclusions, `Abelian.mono_cokernel_map_of_isPullback`, epi from base change) identifies
  the successive quotients.
- Rank one: the sequence `0 → E → E → 0 → 0`.
- Rank `r + 1 ≥ 2`: `L` = pullback of `𝒪(1)` along the closed embedding from `Projective`, very
  ample; `exists_isGeneratedBySections_tensorPowerTwist_of_projective` gives finitely many
  generating sections of `E ⊗ L^m`, reindexed to `Fin (N + 1)` with an extra zero section;
  `exists_nonvanishing_section_shortExact` (II Ex. 8.2, `n = 1 < r + 1`) gives
  `0 → 𝒪 → E ⊗ L^m → E'' → 0`. Apply the inverse of `Ringed.invertibleTensorEquivalence`
  (`F ↦ M^∨ ⊗ F`, `M = L^m`), an exact functor, and compose with `M^∨ ⊗ (E ⊗ M) ≅ E`;
  `Ringed.isLocallyFreeOfRank_moduleSheafTensor_of_isInvertible` gives the ranks of the ends.

## Helpers added

- `Hartshorne.Ringed.moduleSheafTensorLeft`, `moduleSheafTensorAssoc_hom_naturality`,
  `moduleSheafUnitTensor_hom_naturality`, `tensorLeftCompIsoOfTensorIso`,
  `invertibleTensorEquivalence`, `isLocallyFreeOfRank_moduleSheafTensor_of_isInvertible`,
  `isLocallyFreeOfRank_zero_of_isZero`, `isZero_of_isLocallyFreeOfRank_zero` (ringed spaces).
- `Hartshorne.isLocallyFreeOfRank_of_shortExact` (reduced locally Noetherian schemes; the middle
  term is assumed coherent).
- `Hartshorne.isPullback_ofLE_pullback_subobject`, `isIso_cokernelMap_ofLE_pullback_subobject`,
  `shortExact_pullback_subobject` (abelian categories).
