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

## Not formalized

- The article's remark that the localizations of `Õ_P` at its maximal ideals are the local rings
  of `X̃` above `P` is not stated in Lean. The Lean proves that `Õ_P` is the stalk of `ν_* 𝒪_X̃`,
  is finite, and is semilocal.
