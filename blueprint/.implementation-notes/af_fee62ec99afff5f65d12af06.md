# The normalization defect quotient

## Lean (module `Hartshorne.Curve.NormalizationDeltaQuotient`)

- `normalizationPushforward X` is `ν_* 𝒪_X̃` for `ν = absoluteNormalizationMap X`;
  `structureSheafModule X` is `𝒪_X`; `normalizationUnitMap X` is Mathlib's
  `SheafOfModules.unitToPushforwardObjUnit` for `ν`.
- `normalizationDeltaQuotient X := cokernel (normalizationUnitMap X)` in `X.Modules`, and
  `normalizationDeltaSequence X` is the short complex; `normalizationDeltaSequence_shortExact`
  needs only `IsIntegral X`.
- `semilocalIntegralClosure X P := integralClosure (X.presheaf.stalk P) X.functionField`;
  `normalizationDefectModule X P` is its quotient by the range of `Algebra.linearMap`.
- `normalizationPushforwardStalkEquiv` (stalk of `ν_* 𝒪_X̃` ≃ₗ `Õ_P`) and
  `normalizationPushforwardStalkEquiv_unit` (compatibility with `𝒪_{X,P} ⊆ Õ_P`, stated on germs
  of sections); `normalizationDeltaQuotientStalkEquiv` is `Q_P ≃ₗ Õ_P/𝒪_{X,P}`.
- `normalizationDelta X P : ℕ∞` is `Module.length` of `normalizationDefectModule X P`;
  `normalizationDelta_eq_length_stalk` identifies it with the length of `Q_P`.
- Under `s : X ⟶ Spec k`, `FiniteType s`: `isCoherent_normalizationPushforward`,
  `isCoherent_normalizationDeltaQuotient`, `module_finite_semilocalIntegralClosure`,
  `finite_setOf_isMaximal_semilocalIntegralClosure` (semilocal). With also
  `topologicalKrullDim X = 1`: `finite_moduleSheafSupport_normalizationDeltaQuotient`,
  `normalizationDelta_ne_top`, `finite_setOf_normalizationDelta_ne_zero`, and the bundle
  `normalizationDeltaQuotient_spec`. Coherence of `𝒪_X` is the existing
  `isCoherent_structureSheafModule`.
- The Lean generalizes Hartshorne's hypotheses: finite type over any field instead of projective
  over an algebraically closed field.

## Proof route

- The stalk map `Φ : (ν_* 𝒪_X̃)_P → K(X)` is the colimit of
  `Γ(X̃, ν⁻¹V) → Γ(Spec K, ⊤) ≅ K`, the `appLE` of `toNormalization : Spec K ⟶ X̃`.
  Over an affine `V`, Mathlib's `normalizationObjIso_hom_val` identifies this with the integral
  closure of `Γ(X, V)` in `K` (`genericPreimageSectionsAlgEquiv`). Injectivity and the image
  (`IsIntegral.exists_multiple_integral_of_isLocalization` plus `𝒪_{X,P}`-linearity of `Φ`)
  follow.
- Stalk exactness of the cokernel: `modules_exists_local_lift` for surjectivity, and
  sectionwise exactness via `Functor.preservesFiniteLimits_tfae` for the middle.
- Finite support: the support of a coherent sheaf is closed, misses the generic point, and
  `finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_eq_one` (T0 version, in
  `NormalizationDivisorDescent`) finishes. This avoids the normal-locus route named in the
  article's proof sketch.
- Finite length: `FractionalIdeal.isFractional_of_fg` gives `d ∈ 𝒪_{X,P}⁰` with `d Õ_P ⊆ 𝒪_{X,P}`;
  `x ↦ d x` embeds `Õ_P/𝒪_{X,P}` into `𝒪_{X,P}/(d)`, which has finite length by
  `isFiniteLength_quotient_span_singleton` (`Ring.KrullDimLE 1` from
  `ringKrullDim_stalk_eq_coheight`).

## Friction

- `InvertibleSectionClearingDenominators.moduleSheafStalkModule` duplicates
  `schemeModulesStalkModule` (definitionally equal). Once both are imported, `rw` with
  `schemeModules_germ_smul` fails syntactically, so the module erases the duplicate with
  `attribute [-instance]`. Merging the two instances would remove this.
- For `P = genericPoint X`, `X.presheaf.stalk P` and `X.functionField` are the same type, so
  `algebraMap` between them can elaborate to `Algebra.id`. State lemmas for a general `P` and
  specialize.

## Localizations of `Õ_P` (the fibre over `P`)

- `exists_normalizationFibre_localization`: for each `Q ∈ ν⁻¹(P)` a ring map
  `ρ_Q : Õ_P →+* 𝒪_{X̃,Q}` extending the stalk map of `ν` (stated on germs:
  `ρ_Q (germ_P a) = germ_Q (ν.app U a)`, helper `ρ_algebraMap_germ`, proved by
  `IsLocalization.ringHom_ext` over `Γ(X, V) → 𝒪_{X,P}` and `Scheme.Hom.germ_stalkMap_apply`),
  with `𝔫_Q = ρ_Q⁻¹(𝔪_Q)` maximal and
  `IsLocalization.AtPrime 𝒪_{X̃,Q} 𝔫_Q`; `Q ↦ 𝔫_Q` is injective and hits every maximal ideal.
  `nonempty_localization_ringEquiv_stalk` gives, for such a `ρ_Q`, the ring isomorphism
  `Localization.AtPrime 𝔫_Q ≃+* 𝒪_{X̃,Q}`.
- Route (helpers in `NormalizationDeltaAux`, section `Fibre`, for a fixed affine `V ∋ P`):
  `ψ : B → Õ_P` with `B = Γ(X̃, ν⁻¹ V)`; `isLocalization_ψ` (Õ_P is `B` localized at
  `Msub`, the image of `Γ(X, V) ∖ 𝔭_P`); `ρ` is `IsLocalization.lift` of the germ map;
  `isLocalization_ρ` uses `IsLocalization.isLocalization_of_submonoid_le` and
  `isLocalization_of_is_exists_mul_mem`; `isMaximal_iff` (a prime of `Õ_P` is maximal iff it lies
  over `𝔭_P`, via integrality over the local ring `𝒪_{X,P}`); `fromSpec_comap` and `comap_qQ`
  (from `IsAffineOpen.SpecMap_appLE_fromSpec`); `bijective_fibre`.
- `ρ_Q` is built from a chosen affine `V`; the compatibility with the stalk map of `ν` determines
  it on the image of `𝒪_{X,P}`, and the theorem is existential in `ρ`.
