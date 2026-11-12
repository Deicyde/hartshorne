# Finite-dimensional linear systems on an arbitrary variety

## Lean

Module `Hartshorne.Scheme.FiniteLinearSystem`.

- Zero scheme of a section of an invertible sheaf: `Hartshorne.invertibleZeroIdeal hL s`, the
  existing `Hartshorne.sectionZeroIdeal` (image of `s^∨ : L^∨ → 𝒪_X`, Appendix A C6) for `E = L`.
  Local equation `invertibleZeroIdeal_ideal_eq_span` (on an affine open trivialized by `e`, with
  `s = g e`, the ideal is `(g)`; the dual section is `Ringed.IsLocalFrame.dualLocalFrame`),
  support `mem_support_invertibleZeroIdeal_iff`, iso invariance `invertibleZeroIdeal_map_iso`,
  pullback `invertibleZeroIdeal_pullbackGlobalSection` (`Z(f^* t) = (Z t).comap f`, via
  `Hartshorne.inverseImageIdeal_ideal`).
- Base locus: `baseLocusIdeal hL S = ⨆ t ∈ S, invertibleZeroIdeal hL t` for any set `S` of
  sections, closed subscheme `baseLocus`, pointwise description `mem_support_baseLocusIdeal_iff`.
- `V` is presented by a spanning family `s : Fin (n + 1) → Γ(L, ⊤)` over `k`, with
  `q : X ⟶ Spec k`: `linearSystemSection q s a = ∑ kConst q (a i) • s i`,
  `linearSystem q s = Set.range (linearSystemSection q s)`. No coordinate-free `ℙ(V)` exists in
  the project, so the morphism lands in `ℙⁿ_k = projectiveSpaceOverScheme n (Spec k)`; for a
  basis this is `ℙ(V)`. Linear independence is not assumed (not needed by any statement).
- Complement of the base locus: `linearSystemDomain hL s = ⨆ i, nonvanishingLocusOpens hL (s i)`,
  identified with the complement by `mem_linearSystemDomain_iff` and
  `range_baseLocus_subschemeι`. Surjectivity of evaluation: `span_germ_linearSystem_eq_top`
  (stalks on `X`) and `isGeneratedBySections_linearSystemSections` (on the open subscheme).
- Morphism: `linearSystemMorphism q hL s`, from `existsUnique_morphism_of_isGeneratedBySections`
  (II Thm 7.1), with `existsUnique_linearSystemMorphism`, `linearSystemMorphism_spec`; same
  pattern as `pointProjection` in `ProjectionFromPoint`.
- Hyperplane clause: `comap_invertibleZeroIdeal_linearSystemSection`: for every `a ∈ kⁿ⁺¹`,
  `(Z(∑ aᵢ sᵢ)).comap U.ι = (Z(linearSection k n a)).comap φ` as ideal sheaves on `U`
  (`IdealSheafData.comap` is the ideal of the fibre product). Uses `iso_app_linearSection`.
- Cartier clause: `isLocallyPrincipalNonZeroDivisor_invertibleZeroIdeal` and
  `exists_isEffective_idealSheafData_eq_invertibleZeroIdeal`, for `[IsIntegral X]` and `s ≠ 0`.
  An integral scheme has one component, and a section vanishing identically on it is `0`, so the
  "away from components on which it vanishes identically" proviso reduces to `s ≠ 0`.
  Nonsingularity is not used.

## Hypotheses

Finite type over `k` is never used, and integrality only in the Cartier clause, so the Lean is
stated without them (no unused hypotheses).
