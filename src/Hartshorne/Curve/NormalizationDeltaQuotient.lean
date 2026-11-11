/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AbsoluteNormalizationFinite
import Hartshorne.Scheme.FinitePushforwardCoherent
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.ModuleSheafSupport
import Hartshorne.Scheme.CoherentFreeLocus
import Hartshorne.Scheme.AffineGlobalSectionsExact
import Hartshorne.Scheme.ModuleSheafTensor
import Hartshorne.Scheme.NormalizationDivisorDescent
import Hartshorne.Cohomology.Flatness.CoherentSelfFlatLocallyFree
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The normalization defect quotient

Hartshorne, *Algebraic Geometry*, IV, Exercise 1.8 (preamble), p. 298.

Let `X` be an integral scheme with normalization `ν : X̃ ⟶ X`
(`Hartshorne.absoluteNormalizationMap`). We define the defect quotient
`Q = ν_* 𝒪_X̃ / 𝒪_X` as the cokernel of `ν^# : 𝒪_X ⟶ ν_* 𝒪_X̃` and prove:

* `0 → 𝒪_X → ν_* 𝒪_X̃ → Q → 0` is short exact (`normalizationDeltaSequence_shortExact`);
* at every point `P`, the stalk `(ν_* 𝒪_X̃)_P` is `Õ_P`, the integral closure of `𝒪_{X,P}` in
  the function field `K(X)` (`normalizationPushforwardStalkEquiv`), compatibly with
  `𝒪_{X,P} ⊆ Õ_P` (`normalizationPushforwardStalkEquiv_unit`), and hence
  `Q_P ≅ Õ_P / 𝒪_{X,P}` (`normalizationDeltaQuotientStalkEquiv`);
* the localizations of `Õ_P` at its maximal ideals are the local rings `𝒪_{X̃,Q}` of the points
  `Q` over `P`, and `Q ↦ 𝔫_Q` is a bijection from `ν⁻¹(P)` onto the maximal ideals of `Õ_P`
  (`exists_normalizationFibre_localization`). On an affine `V ∋ P`, `Õ_P` is the localization of
  `B = Γ(X̃, ν⁻¹ V)` at the image of `Γ(X, V) ∖ 𝔭_P`, `𝒪_{X̃,Q}` is `B_{𝔮_Q}`, and the maximal
  ideals of `Õ_P` (integral over the local ring `𝒪_{X,P}`) are the primes lying over `𝔭_P`.

If moreover `X` is of finite type over a field (Hartshorne's `X` is projective over an
algebraically closed field), then `𝒪_X`, `ν_* 𝒪_X̃` and `Q` are coherent, `Õ_P` is a finite
`𝒪_{X,P}`-module with finitely many maximal ideals; if also `dim X = 1`, then `Q` has finite
support, each `δ_P = length (Õ_P / 𝒪_{X,P})` is finite (`normalizationDelta_ne_top`), and only
finitely many `δ_P` are nonzero (`finite_setOf_normalizationDelta_ne_zero`).

The stalk computation maps the germ of a section of `𝒪_X̃` over `ν⁻¹ V` to its value at the
generic point. Over an affine `V` the sections of `𝒪_X̃` are the integral closure of `Γ(X, V)`
in `K(X)` (`Scheme.Hom.normalizationObjIso`); localizing at `P` gives the integral closure of
`𝒪_{X,P}`. Finiteness of `δ_P` uses a common denominator `d ≠ 0` of the finite module `Õ_P`,
which embeds `Õ_P / 𝒪_{X,P}` into `𝒪_{X,P} / (d)`, of finite length since `dim 𝒪_{X,P} ≤ 1`.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Hartshorne

open AlgebraicGeometry

-- A definitionally equal duplicate of `schemeModulesStalkModule`; erased so that the germ
-- lemma `schemeModules_germ_smul` applies syntactically.
attribute [-instance] moduleSheafStalkModule

universe u

noncomputable section

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_X` as an `𝒪_X`-module. -/
abbrev structureSheafModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

variable [IsIntegral X]

/-- The pushforward `ν_* 𝒪_X̃` of the structure sheaf of the normalization `ν : X̃ ⟶ X`. -/
abbrev normalizationPushforward : X.Modules :=
  (Scheme.Modules.pushforward (absoluteNormalizationMap X)).obj
    (SheafOfModules.unit (absoluteNormalization X).ringCatSheaf)

/-- The morphism `𝒪_X ⟶ ν_* 𝒪_X̃` given by `ν^#`. -/
def normalizationUnitMap : structureSheafModule X ⟶ normalizationPushforward X :=
  SheafOfModules.unitToPushforwardObjUnit (absoluteNormalizationMap X).toRingCatSheafHom

namespace NormalizationDeltaAux

/-- The generic-point morphism `Spec K(X) ⟶ X`. -/
abbrev g : Spec X.functionField ⟶ X := absoluteNormalizationGenericMap X

/-- The factorization `Spec K(X) ⟶ X̃`. -/
abbrev t : Spec X.functionField ⟶ absoluteNormalization X := (g X).toNormalization

lemma t_comp : t X ≫ absoluteNormalizationMap X = g X :=
  (g X).toNormalization_fromNormalization

lemma top_le (V : X.Opens) [Nonempty V] :
    (⊤ : (Spec X.functionField).Opens) ≤ t X ⁻¹ᵁ (absoluteNormalizationMap X ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, t_comp, absoluteNormalizationGenericMap_preimage_eq_top]

/-- The map `Γ(X̃, ν⁻¹ V) → K(X)` restricting a section to the generic point. -/
def φ (V : X.Opens) [Nonempty V] :
    Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V) ⟶ X.functionField :=
  (t X).appLE _ ⊤ (top_le X V) ≫ (Scheme.ΓSpecIso X.functionField).hom

lemma φ_app (V : X.Opens) [Nonempty V] (a : Γ(X, V)) :
    φ X V ((absoluteNormalizationMap X).app V a) = X.germToFunctionField V a := by
  have hη : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by
      simpa using (inferInstance : Nonempty V))
  have h : (absoluteNormalizationMap X).app V ≫ φ X V = X.germToFunctionField V := by
    have key : ∀ {Y Z W : Scheme.{u}} {f : Y ⟶ Z} {h : Z ⟶ W} {g : Y ⟶ W} (H : f ≫ h = g)
        (U : W.Opens) (U' : Y.Opens) (e : U' ≤ f ⁻¹ᵁ (h ⁻¹ᵁ U)) (e' : U' ≤ g ⁻¹ᵁ U),
        h.app U ≫ f.appLE (h ⁻¹ᵁ U) U' e = g.appLE U U' e' := by
      intros Y Z W f h g H U U' e e'
      subst H
      rw [Scheme.Hom.comp_appLE]
    rw [φ, ← Category.assoc, key (t_comp X) V ⊤ (top_le X V)
      (absoluteNormalizationGenericMap_preimage_eq_top X V).ge]
    simp only [Scheme.Hom.appLE, g, absoluteNormalizationGenericMap]
    rw [Scheme.fromSpecStalk_app hη]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    have hid : ∀ (i : (op (⊤ : (Spec X.functionField).Opens)) ⟶ op ⊤),
        (Spec X.functionField).presheaf.map i = 𝟙 _ := fun i => by
      rw [Subsingleton.elim i (𝟙 _), CategoryTheory.Functor.map_id]
    erw [hid]
    simp [Scheme.germToFunctionField]
  exact congr($h a)

lemma map_φ (V V' : X.Opens) [Nonempty V] [Nonempty V'] (i : V' ≤ V)
    (s : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V)) :
    φ X V' ((absoluteNormalization X).presheaf.map
      (homOfLE ((Opens.map (absoluteNormalizationMap X).base).monotone i)).op s) = φ X V s := by
  simp only [φ, CommRingCat.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

variable {X} in
/-- The map from the stalk `(ν_* 𝒪_X̃)_P` to the function field. -/
def Φ (P : X) :
    (normalizationPushforward X).presheaf.stalk P ⟶ AddCommGrpCat.of X.functionField :=
  ModuleSheafTensor.stalkDesc (P := (normalizationPushforward X).presheaf) (x := P)
    (fun U hU => haveI : Nonempty U := ⟨⟨P, hU⟩⟩
      AddCommGrpCat.ofHom (φ X U).hom.toAddMonoidHom)
    (fun U V i hV => by
      have : Nonempty U := ⟨⟨P, i.le hV⟩⟩
      have : Nonempty V := ⟨⟨P, hV⟩⟩
      ext s
      exact map_φ X U V i.le s)

lemma Φ_germ {P : X} (U : X.Opens) (hU : P ∈ U) [Nonempty U]
    (s : Γ(normalizationPushforward X, U)) :
    Φ P ((normalizationPushforward X).presheaf.germ U P hU s) = φ X U s := by
  change ((normalizationPushforward X).presheaf.germ U P hU ≫ Φ P) s = _
  exact ConcreteCategory.congr_hom
    (colimit.ι_desc (F := (OpenNhds.inclusion P).op ⋙ (normalizationPushforward X).presheaf) _
      (op (⟨U, hU⟩ : OpenNhds P))) s

lemma Φ_smul (P : X) (r : X.presheaf.stalk P)
    (m : (normalizationPushforward X).presheaf.stalk P) :
    Φ P (r • m) = algebraMap (X.presheaf.stalk P) X.functionField r * Φ P m := by
  obtain ⟨U, hU, s, rfl⟩ := (normalizationPushforward X).presheaf.exists_germ_eq m
  obtain ⟨W, hWU, hW, c, rfl⟩ := X.presheaf.exists_le_germ_eq r hU
  have : Nonempty W := ⟨⟨P, hW⟩⟩
  rw [← TopCat.Presheaf.germ_res_apply (normalizationPushforward X).presheaf (homOfLE hWU) P hW s,
    ← schemeModules_germ_smul, Φ_germ, Φ_germ, Scheme.algebraMap_germ_eq_germToFunctionField]
  generalize ((normalizationPushforward X).presheaf.map (homOfLE hWU).op) s = y
  have h1 := (φ X W).hom.map_mul ((absoluteNormalizationMap X).app W c) y
  rw [φ_app] at h1
  exact h1

lemma φ_apply_of_isAffineOpen (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (s : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V)) :
    letI := ((g X).app V).hom.toAlgebra
    φ X V s = genericPreimageSectionsAlgEquiv X V (((g X).normalizationObjIso hV).hom s).1 := by
  let := ((g X).app V).hom.toAlgebra
  have hle : g X ⁻¹ᵁ V ≤ t X ⁻¹ᵁ (absoluteNormalizationMap X ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, t_comp]
  have h1 : φ X V s = (Scheme.ΓSpecIso X.functionField).hom
      ((Spec X.functionField).presheaf.map (homOfLE (top_le X V |>.trans
        (by rw [← Scheme.Hom.comp_preimage, t_comp]))).op
        ((t X).appLE _ (g X ⁻¹ᵁ V) hle s)) := by
    rw [φ, ← Scheme.Hom.appLE_map (t X) hle]
    rfl
  have h2 : ((t X).appLE _ (g X ⁻¹ᵁ V) hle s) =
      (((g X).normalizationObjIso hV).hom s).1 := by
    have := (g X).normalizationObjIso_hom_val hV
    exact congr($this s).symm
  rw [h1, h2]
  change _ = (Scheme.ΓSpecIso X.functionField).hom ((Spec X.functionField).presheaf.map _ _)
  congr 2

lemma φ_injective_of_isAffineOpen (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    Function.Injective (φ X V) := by
  let := ((g X).app V).hom.toAlgebra
  intro a b h
  rw [φ_apply_of_isAffineOpen X V hV, φ_apply_of_isAffineOpen X V hV] at h
  exact ((g X).normalizationObjIso hV).commRingCatIsoToRingEquiv.injective
    (Subtype.ext ((genericPreimageSectionsAlgEquiv X V).injective h))

lemma mem_range_φ_iff (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] (x : X.functionField) :
    x ∈ Set.range (φ X V) ↔ IsIntegral Γ(X, V) x := by
  let := ((g X).app V).hom.toAlgebra
  let e := genericPreimageSectionsAlgEquiv X V
  constructor
  · rintro ⟨s, rfl⟩
    rw [φ_apply_of_isAffineOpen X V hV]
    exact (((g X).normalizationObjIso hV).hom s).2.map e
  · intro hx
    have hy : IsIntegral Γ(X, V) (e.symm x) := hx.map e.symm
    let z : integralClosure Γ(X, V) Γ(Spec X.functionField, g X ⁻¹ᵁ V) := ⟨e.symm x, hy⟩
    let sv : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V) :=
      ((g X).normalizationObjIso hV).inv z
    refine ⟨sv, ?_⟩
    rw [φ_apply_of_isAffineOpen X V hV]
    have hz : ((g X).normalizationObjIso hV).hom sv = z := Iso.inv_hom_id_apply _ _
    rw [hz]
    exact e.apply_symm_apply x

lemma Φ_injective (P : X) : Function.Injective (Φ P) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨U, hU, s, rfl⟩ := (normalizationPushforward X).presheaf.exists_germ_eq m
  obtain ⟨_, ⟨V, hV, rfl⟩, hPV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hU U.2
  have : Nonempty V := ⟨⟨P, hPV⟩⟩
  rw [← TopCat.Presheaf.germ_res_apply (normalizationPushforward X).presheaf (homOfLE hVU) P hPV s]
    at hm ⊢
  rw [Φ_germ] at hm
  have h0 := φ_injective_of_isAffineOpen X V hV (hm.trans (map_zero _).symm)
  rw [h0]
  exact map_zero _

lemma mem_range_Φ_iff (P : X) (x : X.functionField) :
    x ∈ Set.range (Φ P) ↔ IsIntegral (X.presheaf.stalk P) x := by
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨U, hU, s, rfl⟩ := (normalizationPushforward X).presheaf.exists_germ_eq m
    obtain ⟨_, ⟨V, hV, rfl⟩, hPV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hU U.2
    have : Nonempty V := ⟨⟨P, hPV⟩⟩
    rw [← TopCat.Presheaf.germ_res_apply (normalizationPushforward X).presheaf (homOfLE hVU) P hPV
      s, Φ_germ]
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨P, hPV⟩ : V)
    have := functionField_isScalarTower X V ⟨P, hPV⟩
    refine IsIntegral.tower_top (R := Γ(X, V)) (A := X.presheaf.stalk (⟨P, hPV⟩ : V)) ?_
    exact (mem_range_φ_iff X V hV _).mp (Set.mem_range_self _)
  · intro hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hPV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ P) isOpen_univ
    have : Nonempty V := ⟨⟨P, hPV⟩⟩
    let P' : V := ⟨P, hPV⟩
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf P'
    have := hV.isLocalization_stalk P'
    have := functionField_isScalarTower X V P'
    obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (M := (hV.primeIdealOf P').asIdeal.primeCompl) (Rₘ := X.presheaf.stalk P') x hx
    obtain ⟨s, hs⟩ := (mem_range_φ_iff X V hV _).mpr hmx
    have hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk P') m) :=
      IsLocalization.map_units (X.presheaf.stalk P')
        (⟨m, hm⟩ : (hV.primeIdealOf P').asIdeal.primeCompl)
    obtain ⟨u, hu⟩ := hu
    refine ⟨(↑u⁻¹ : X.presheaf.stalk P) • (normalizationPushforward X).presheaf.germ V P hPV s, ?_⟩
    rw [Φ_smul]
    erw [Φ_germ]
    rw [hs, Submonoid.mk_smul, Algebra.smul_def,
      IsScalarTower.algebraMap_apply Γ(X, V) (X.presheaf.stalk P') X.functionField, ← hu,
      ← mul_assoc, ← map_mul]
    change algebraMap (X.presheaf.stalk P) X.functionField (↑u⁻¹ * ↑u) * x = x
    rw [Units.inv_mul, map_one, one_mul]

lemma normalizationUnitMap_app (U : X.Opens) (a : Γ(X, U)) :
    (normalizationUnitMap X).app U a = (absoluteNormalizationMap X).app U a := rfl

lemma normalizationUnitMap_app_injective (U : X.Opens) :
    Function.Injective ((normalizationUnitMap X).app U) := by
  rcases isEmpty_or_nonempty U with hU | hU
  · have hbot : U = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hU.false ⟨x, hx⟩
    subst hbot
    intro a b _
    have : Subsingleton Γ(X, (⊥ : X.Opens)) := inferInstance
    exact @Subsingleton.elim Γ(X, ⊥) this a b
  · have hinj : Function.Injective ((absoluteNormalizationMap X).app U) := by
      intro a b h
      have h' := congrArg (φ X U) h
      rwa [φ_app, φ_app, (Scheme.germToFunctionField_injective X U).eq_iff] at h'
    exact hinj

lemma sections_exact (W : X.Opens) (y : Γ(normalizationPushforward X, W))
    (hy : (cokernel.π (normalizationUnitMap X)).app W y = 0) :
    ∃ a, (normalizationUnitMap X).app W a = y := by
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (normalizationUnitMap X) (cokernel.π _) (cokernel.condition _)
  have : Mono (normalizationUnitMap X) := by
    apply (SheafOfModules.forget _).mono_of_mono_map
    exact PresheafOfModules.mono_of_injective fun U => normalizationUnitMap_app_injective X U.unop
  have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel _)
  let G : X.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (op W)
  have hG : PreservesFiniteLimits G := by
    have := PreservesLimitsOfSize.preservesFiniteLimits (Scheme.Modules.toPresheaf X)
    have := PreservesLimitsOfSize.preservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W))
    exact comp_preservesFiniteLimits _ _
  have : G.Additive := ⟨fun {_ _ _ _} => rfl⟩
  have key0 : PreservesFiniteLimits G → ∀ S : ShortComplex X.Modules,
      S.Exact ∧ Mono S.f → (S.map G).Exact ∧ Mono (G.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae G).out 3 1).mp
  have key := key0 hG S ⟨hS, (inferInstance : Mono (normalizationUnitMap X))⟩
  exact (ShortComplex.ab_exact_iff _).mp key.1 y hy

variable {X} in
/-- The `𝒪_{X,P}`-linear map on stalks induced by a morphism of `𝒪_X`-modules. -/
def stalkHom {F G : X.Modules} (f : F ⟶ G) (P : X) :
    F.presheaf.stalk P →ₗ[X.presheaf.stalk P] G.presheaf.stalk P where
  toFun := ((TopCat.Presheaf.stalkFunctor Ab P).map f.mapPresheaf).hom
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hU, s, rfl⟩ := F.presheaf.exists_germ_eq m
    obtain ⟨W, hWU, hW, c, rfl⟩ := X.presheaf.exists_le_germ_eq r hU
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hWU) P hW s,
      ← schemeModules_germ_smul]
    simp only [RingHom.id_apply]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
      Scheme.Modules.mapPresheaf_app, Scheme.Modules.Hom.app_smul, schemeModules_germ_smul]

omit [IsIntegral X] in
lemma stalkHom_germ {F G : X.Modules} (f : F ⟶ G) {P : X} (U : X.Opens) (hU : P ∈ U)
    (s : Γ(F, U)) : stalkHom f P (F.presheaf.germ U P hU s) = G.presheaf.germ U P hU (f.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U P hU f.mapPresheaf s

lemma stalk_π_surjective (P : X) :
    Function.Surjective (stalkHom (cokernel.π (normalizationUnitMap X)) P) := by
  intro b
  have : Epi (cokernel.π (normalizationUnitMap X)) := coequalizer.π_epi
  obtain ⟨U, hU, t, rfl⟩ := (cokernel (normalizationUnitMap X)).presheaf.exists_germ_eq b
  obtain ⟨V, hVU, hV, s, hs⟩ := modules_exists_local_lift (cokernel.π (normalizationUnitMap X)) t hU
  refine ⟨(normalizationPushforward X).presheaf.germ V P hV s, ?_⟩
  rw [stalkHom_germ, hs, TopCat.Presheaf.germ_res_apply]

lemma stalk_range_eq_ker (P : X) :
    LinearMap.range (stalkHom (normalizationUnitMap X) P) =
      LinearMap.ker (stalkHom (cokernel.π (normalizationUnitMap X)) P) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨U, hU, a, rfl⟩ :=
      (structureSheafModule X).presheaf.exists_germ_eq a
    rw [LinearMap.mem_ker, stalkHom_germ, stalkHom_germ]
    have h0 : (cokernel.π (normalizationUnitMap X)).app U
        ((normalizationUnitMap X).app U a) = 0 := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition]
      rfl
    rw [h0, map_zero]
  · intro m hm
    obtain ⟨U, hU, s, rfl⟩ := (normalizationPushforward X).presheaf.exists_germ_eq m
    rw [LinearMap.mem_ker, stalkHom_germ] at hm
    have hm' : (cokernel (normalizationUnitMap X)).presheaf.germ U P hU
        ((cokernel.π (normalizationUnitMap X)).app U s) =
        (cokernel (normalizationUnitMap X)).presheaf.germ U P hU 0 := by
      rw [hm, map_zero]
    obtain ⟨W, hW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq _ P hU hU _ _ hm'
    rw [map_zero] at e
    have hnat := ConcreteCategory.congr_hom
      ((cokernel.π (normalizationUnitMap X)).mapPresheaf.naturality iU.op) s
    simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hnat
    obtain ⟨a, ha⟩ := sections_exact X W _ (hnat.trans e)
    refine ⟨(structureSheafModule X).presheaf.germ W P hW a, ?_⟩
    rw [stalkHom_germ, ha, TopCat.Presheaf.germ_res_apply]

/-- The map `Φ` as an `𝒪_{X,P}`-linear map. -/
def ΦL (P : X) :
    (normalizationPushforward X).presheaf.stalk P →ₗ[X.presheaf.stalk P] X.functionField where
  toFun := Φ P
  map_add' := map_add _
  map_smul' r m := by
    rw [Φ_smul, Algebra.smul_def]
    rfl

lemma range_ΦL (P : X) : LinearMap.range (ΦL X P) =
    Subalgebra.toSubmodule (integralClosure (X.presheaf.stalk P) X.functionField) := by
  ext x
  exact mem_range_Φ_iff X P x

end NormalizationDeltaAux

open NormalizationDeltaAux

/-- The semilocal ring `Õ_P`: the integral closure of `𝒪_{X,P}` in the function field `K(X)`. -/
abbrev semilocalIntegralClosure (P : X) : Subalgebra (X.presheaf.stalk P) X.functionField :=
  integralClosure (X.presheaf.stalk P) X.functionField

/-- The quotient `Õ_P / 𝒪_{X,P}` as an `𝒪_{X,P}`-module. -/
abbrev normalizationDefectModule (P : X) : Type u :=
  semilocalIntegralClosure X P ⧸
    LinearMap.range (Algebra.linearMap (X.presheaf.stalk P) (semilocalIntegralClosure X P))

/-- The stalk `(ν_* 𝒪_X̃)_P` is `Õ_P`, the integral closure of `𝒪_{X,P}` in `K(X)`. -/
def normalizationPushforwardStalkEquiv (P : X) :
    (normalizationPushforward X).presheaf.stalk P ≃ₗ[X.presheaf.stalk P]
      semilocalIntegralClosure X P :=
  (LinearEquiv.ofInjective (ΦL X P) (Φ_injective X P)).trans (LinearEquiv.ofEq _ _ (range_ΦL X P))

/-- Under `(ν_* 𝒪_X̃)_P ≃ Õ_P`, the stalk of `𝒪_X ⟶ ν_* 𝒪_X̃` is the inclusion
`𝒪_{X,P} ⊆ Õ_P`. -/
theorem normalizationPushforwardStalkEquiv_unit {P : X} (U : X.Opens) (hU : P ∈ U)
    (a : Γ(structureSheafModule X, U)) :
    (normalizationPushforwardStalkEquiv X P (stalkHom (normalizationUnitMap X) P
      ((structureSheafModule X).presheaf.germ U P hU a)) : X.functionField) =
      algebraMap (X.presheaf.stalk P) X.functionField (X.presheaf.germ U P hU a) := by
  have : Nonempty U := ⟨⟨P, hU⟩⟩
  change Φ P _ = _
  rw [stalkHom_germ]
  erw [Φ_germ]
  exact (φ_app X U a).trans (Scheme.algebraMap_germ_eq_germToFunctionField X hU a).symm

/-- **The normalization defect quotient** (Hartshorne IV, Exercise 1.8, p. 298): the cokernel
`Q = ν_* 𝒪_X̃ / 𝒪_X` of `ν^# : 𝒪_X ⟶ ν_* 𝒪_X̃`. -/
def normalizationDeltaQuotient : X.Modules := cokernel (normalizationUnitMap X)

/-- The sequence `0 → 𝒪_X → ν_* 𝒪_X̃ → Q → 0`. -/
def normalizationDeltaSequence : ShortComplex X.Modules :=
  ShortComplex.mk (normalizationUnitMap X) (cokernel.π (normalizationUnitMap X))
    (cokernel.condition _)

/-- **Hartshorne IV, Exercise 1.8 (exactness).** `0 → 𝒪_X → ν_* 𝒪_X̃ → Q → 0` is a short exact
sequence of `𝒪_X`-modules. -/
theorem normalizationDeltaSequence_shortExact : (normalizationDeltaSequence X).ShortExact := by
  have h1 : Mono (normalizationUnitMap X) := by
    apply (SheafOfModules.forget _).mono_of_mono_map
    exact PresheafOfModules.mono_of_injective fun U => normalizationUnitMap_app_injective X U.unop
  have h2 : Epi (cokernel.π (normalizationUnitMap X)) := coequalizer.π_epi
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) h1 h2

lemma map_range_unit (P : X) :
    (LinearMap.range (stalkHom (normalizationUnitMap X) P)).map
        (normalizationPushforwardStalkEquiv X P : _ →ₗ[X.presheaf.stalk P] _) =
      LinearMap.range (Algebra.linearMap (X.presheaf.stalk P) (semilocalIntegralClosure X P)) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe, Algebra.linearMap_apply]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨U, hU, a, rfl⟩ := (structureSheafModule X).presheaf.exists_germ_eq a
    exact ⟨X.presheaf.germ U P hU a,
      Subtype.ext (normalizationPushforwardStalkEquiv_unit X U hU a).symm⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    exact ⟨_, ⟨(structureSheafModule X).presheaf.germ U P hU a, rfl⟩,
      Subtype.ext (normalizationPushforwardStalkEquiv_unit X U hU a)⟩

/-- **Hartshorne IV, Exercise 1.8 (stalks of the quotient).** `Q_P ≅ Õ_P / 𝒪_{X,P}` as
`𝒪_{X,P}`-modules, where `Õ_P = (ν_* 𝒪_X̃)_P` is the integral closure of `𝒪_{X,P}` in `K(X)`. -/
def normalizationDeltaQuotientStalkEquiv (P : X) :
    (normalizationDeltaQuotient X).presheaf.stalk P ≃ₗ[X.presheaf.stalk P]
      normalizationDefectModule X P :=
  ((Submodule.quotEquivOfEq _ _ (stalk_range_eq_ker X P)).trans
      (LinearMap.quotKerEquivOfSurjective _ (stalk_π_surjective X P))).symm.trans
    (Submodule.Quotient.equiv _ _ (normalizationPushforwardStalkEquiv X P) (map_range_unit X P))

/-- **The local defect `δ_P`** (Hartshorne IV, Exercise 1.8): the length of the
`𝒪_{X,P}`-module `Õ_P / 𝒪_{X,P}`, as an element of `ℕ∞`. -/
def normalizationDelta (P : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk P) (normalizationDefectModule X P)

/-- `δ_P` is also the length of the stalk `Q_P`. -/
theorem normalizationDelta_eq_length_stalk (P : X) :
    normalizationDelta X P = Module.length (X.presheaf.stalk P)
      ((normalizationDeltaQuotient X).presheaf.stalk P) :=
  (normalizationDeltaQuotientStalkEquiv X P).length_eq.symm

section FiniteType

variable (k : Type u) [Field k] (s : X ⟶ Spec (.of k)) (hs : FiniteType s)
include hs

/-- `ν_* 𝒪_X̃` is coherent when `X` is of finite type over a field: `ν` is finite (Hartshorne II,
Exercise 3.8(b)) and finite pushforward preserves coherence (Hartshorne II, Exercise 5.5(c)). -/
theorem isCoherent_normalizationPushforward : IsCoherent (normalizationPushforward X) := by
  have := isFinite_absoluteNormalizationMap_of_finiteType_field k X s hs
  exact isCoherent_pushforward_of_isFinite _ (isCoherent_structureSheafModule _)

omit [IsIntegral X] in
lemma isLocallyNoetherian_of_finiteType : IsLocallyNoetherian X := by
  have : LocallyOfFiniteType s := hs.1
  exact LocallyOfFiniteType.isLocallyNoetherian s

/-- `Q` is coherent when `X` is of finite type over a field. -/
theorem isCoherent_normalizationDeltaQuotient : IsCoherent (normalizationDeltaQuotient X) := by
  have := isLocallyNoetherian_of_finiteType X k s hs
  exact isCoherent_cokernel _ (isCoherent_structureSheafModule X)
    (isCoherent_normalizationPushforward X k s hs)

/-- `Õ_P` is a finite `𝒪_{X,P}`-module. -/
theorem module_finite_semilocalIntegralClosure (P : X) :
    Module.Finite (X.presheaf.stalk P) (semilocalIntegralClosure X P) := by
  have := finite_stalk_of_isCoherent _ (isCoherent_normalizationPushforward X k s hs) P
  exact Module.Finite.equiv (normalizationPushforwardStalkEquiv X P)

/-- `Õ_P` is semilocal: it has only finitely many maximal ideals. -/
theorem finite_setOf_isMaximal_semilocalIntegralClosure (P : X) :
    {I : Ideal (semilocalIntegralClosure X P) | I.IsMaximal}.Finite := by
  have := module_finite_semilocalIntegralClosure X k s hs P
  refine (Algebra.QuasiFinite.finite_primesOver
    (IsLocalRing.maximalIdeal (X.presheaf.stalk P))).subset fun I hI => ?_
  have hI' : I.IsMaximal := hI
  refine ⟨hI'.isPrime, ⟨?_⟩⟩
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := X.presheaf.stalk P) I
  exact (IsLocalRing.eq_maximalIdeal this).symm

end FiniteType

lemma subsingleton_normalizationDefectModule_of_isField (P : X)
    (hP : IsField (X.presheaf.stalk P)) : Subsingleton (normalizationDefectModule X P) := by
  have hsurj : Function.Surjective (algebraMap (X.presheaf.stalk P) X.functionField) :=
    IsFractionRing.surjective_iff_isField.mpr hP
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨r, rfl⟩ := hsurj x
  exact ⟨r, Subtype.ext (by rw [Algebra.linearMap_apply]; rfl)⟩

lemma subsingleton_normalizationDefectModule_genericPoint :
    Subsingleton (normalizationDefectModule X (genericPoint X)) :=
  subsingleton_normalizationDefectModule_of_isField X _ (Field.toIsField X.functionField)

lemma genericPoint_not_mem_support :
    genericPoint X ∉ moduleSheafSupport (normalizationDeltaQuotient X) := by
  rw [mem_moduleSheafSupport_iff, ← not_subsingleton_iff_nontrivial, not_not]
  have := subsingleton_normalizationDefectModule_genericPoint X
  exact (normalizationDeltaQuotientStalkEquiv X (genericPoint X)).toEquiv.subsingleton

omit [IsIntegral X] in
lemma krullDimLE_one_stalk (hdim : topologicalKrullDim X = 1) (P : X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk P) := by
  have hkd : Order.krullDim X ≤ 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim.le
  rw [Ring.krullDimLE_iff, ringKrullDim_stalk_eq_coheight]
  exact (Order.coheight_le_krullDim P).trans hkd

section Curve

variable (k : Type u) [Field k] (s : X ⟶ Spec (.of k)) (hs : FiniteType s)
  (hdim : topologicalKrullDim X = 1)
include hs hdim

/-- **Hartshorne IV, Exercise 1.8 (finite support).** If `X` is one-dimensional and of finite type
over a field, then `Q` has finite support: its support is closed (`Q` is coherent) and misses the
generic point, where `Õ = 𝒪 = K(X)`. -/
theorem finite_moduleSheafSupport_normalizationDeltaQuotient :
    (moduleSheafSupport (normalizationDeltaQuotient X)).Finite := by
  have := isLocallyNoetherian_of_finiteType X k s hs
  have : QuasiCompact s := hs.2
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian X := {}
  refine finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_eq_one hdim
    (isClosed_moduleSheafSupport_of_isCoherent _
      (isCoherent_normalizationDeltaQuotient X k s hs)) ?_
  intro h
  exact genericPoint_not_mem_support X (h ▸ Set.mem_univ _)

/-- **Hartshorne IV, Exercise 1.8.** Only finitely many `δ_P` are nonzero. -/
theorem finite_setOf_normalizationDelta_ne_zero : {P : X | normalizationDelta X P ≠ 0}.Finite := by
  refine (finite_moduleSheafSupport_normalizationDeltaQuotient X k s hs hdim).subset fun P hP => ?_
  rw [Set.mem_ofPred_eq, normalizationDelta_eq_length_stalk, ne_eq, Module.length_eq_zero_iff,
    not_subsingleton_iff_nontrivial] at hP
  exact hP

/-- **Hartshorne IV, Exercise 1.8 (finite length).** If `X` is one-dimensional and of finite type
over a field, then every `δ_P` is finite. -/
theorem normalizationDelta_ne_top (P : X) : normalizationDelta X P ≠ ⊤ := by
  have := isLocallyNoetherian_of_finiteType X k s hs
  have := krullDimLE_one_stalk X hdim P
  have := module_finite_semilocalIntegralClosure X k s hs P
  set R := X.presheaf.stalk P
  set K := X.functionField
  set B := semilocalIntegralClosure X P
  have hfg : (Subalgebra.toSubmodule B).FG := (Module.Finite.iff_fg).mp this
  obtain ⟨d, hd, hdB⟩ :=
    FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) (P := K) hfg
  have hinj := IsFractionRing.injective R K
  let r : B → R := fun x => (hdB x.1 x.2).choose
  have hr : ∀ x : B, algebraMap R K (r x) = d • (x : K) := fun x => (hdB x.1 x.2).choose_spec
  let f : B →ₗ[R] R :=
    { toFun := r
      map_add' := fun x y => hinj (by simp only [map_add, hr, Subalgebra.coe_add, smul_add])
      map_smul' := fun c x => hinj (by
        simp only [hr, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
        rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
        ring) }
  let F : B →ₗ[R] R ⧸ Ideal.span {d} := (Ideal.span {d}).mkQ ∘ₗ f
  let p := LinearMap.range (Algebra.linearMap R B)
  have hpF : p ≤ LinearMap.ker F := by
    rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    have : f (Algebra.linearMap R B c) = d * c := hinj (by
      change algebraMap R K (r _) = _
      rw [hr, map_mul, Algebra.linearMap_apply, Algebra.smul_def]
      rfl)
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self d)
  have hker : LinearMap.ker F ≤ p := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at hx
    obtain ⟨c, hc⟩ := hx
    have hc' : r x = c * d := hc.symm
    refine ⟨c, Subtype.ext ?_⟩
    have hd0 : algebraMap R K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have h1 : algebraMap R K d * (x : K) = algebraMap R K d * algebraMap R K c := by
      rw [← Algebra.smul_def, ← hr, hc', map_mul, mul_comm]
    rw [Algebra.linearMap_apply]
    exact ((mul_left_cancel₀ hd0 h1).symm)
  have hinjF : Function.Injective (p.liftQ F hpF) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot _ _ _ hker]
  rw [normalizationDelta, Module.length_ne_top_iff]
  exact (isFiniteLength_quotient_span_singleton R hd).of_injective hinjF

/-- **Hartshorne IV, Exercise 1.8 (preamble), p. 298: the normalization defect quotient.** Let `X`
be an integral one-dimensional scheme of finite type over a field `k` with normalization
`ν : X̃ ⟶ X`. Then `0 → 𝒪_X → ν_* 𝒪_X̃ → Q → 0` is an exact sequence of coherent sheaves, `Q` has
finite support, `Q_P ≅ Õ_P / 𝒪_{X,P}` for the integral closure `Õ_P = (ν_* 𝒪_X̃)_P` of `𝒪_{X,P}`
in `K(X)`, every `δ_P = length (Õ_P / 𝒪_{X,P})` is finite, and only finitely many `δ_P` are
nonzero. Hartshorne takes `X` projective over an algebraically closed field; this generalizes his
statement. -/
theorem normalizationDeltaQuotient_spec :
    (normalizationDeltaSequence X).ShortExact ∧ IsCoherent (structureSheafModule X) ∧
      IsCoherent (normalizationPushforward X) ∧ IsCoherent (normalizationDeltaQuotient X) ∧
      (moduleSheafSupport (normalizationDeltaQuotient X)).Finite ∧
      (∀ P : X, Nonempty ((normalizationDeltaQuotient X).presheaf.stalk P ≃ₗ[X.presheaf.stalk P]
        normalizationDefectModule X P)) ∧
      (∀ P : X, normalizationDelta X P ≠ ⊤) ∧ {P : X | normalizationDelta X P ≠ 0}.Finite :=
  ⟨normalizationDeltaSequence_shortExact X, isCoherent_structureSheafModule X,
    isCoherent_normalizationPushforward X k s hs, isCoherent_normalizationDeltaQuotient X k s hs,
    finite_moduleSheafSupport_normalizationDeltaQuotient X k s hs hdim,
    fun P => ⟨normalizationDeltaQuotientStalkEquiv X P⟩, normalizationDelta_ne_top X k s hs hdim,
    finite_setOf_normalizationDelta_ne_zero X k s hs hdim⟩

end Curve

/-! ### The local rings of `X̃` above `P` -/

namespace NormalizationDeltaAux

section Fibre

variable {X} (P : X) {V : X.Opens} (hV : IsAffineOpen V) (hPV : P ∈ V) [Nonempty V]
include hV hPV

/-- The prime `𝔭_P` of `Γ(X, V)` at `P`. -/
abbrev pP : Ideal Γ(X, V) := (hV.primeIdealOf ⟨P, hPV⟩).asIdeal

/-- The image of `Γ(X, V) ∖ 𝔭_P` in `B = Γ(X̃, ν⁻¹ V)`. -/
abbrev Msub : Submonoid Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V) :=
  (pP P hV hPV).primeCompl.map ((absoluteNormalizationMap X).app V).hom

lemma φ_mem (s : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V)) :
    φ X V s ∈ semilocalIntegralClosure X P := by
  have h := (mem_range_φ_iff X V hV _).mp ⟨s, rfl⟩
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨P, hPV⟩ : V)
  have := functionField_isScalarTower X V ⟨P, hPV⟩
  exact h.tower_top (A := X.presheaf.stalk (⟨P, hPV⟩ : V))

/-- The map `B = Γ(X̃, ν⁻¹ V) → Õ_P`. -/
def ψ : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V) →+*
    semilocalIntegralClosure X P :=
  (φ X V).hom.codRestrict (semilocalIntegralClosure X P) (φ_mem P hV hPV)

lemma ψ_coe (s : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V)) :
    (ψ P hV hPV s : X.functionField) = φ X V s := rfl

lemma ψ_injective : Function.Injective (ψ P hV hPV) := fun _ _ h =>
  φ_injective_of_isAffineOpen X V hV (congrArg Subtype.val h)

lemma ψ_app (a : Γ(X, V)) :
    ψ P hV hPV ((absoluteNormalizationMap X).app V a) =
      algebraMap (X.presheaf.stalk P) (semilocalIntegralClosure X P)
        (X.presheaf.germ V P hPV a) := by
  apply Subtype.ext
  rw [ψ_coe, Subalgebra.coe_algebraMap]
  exact (φ_app X V a).trans (Scheme.algebraMap_germ_eq_germToFunctionField X hPV a).symm

lemma isLocalization_ψ :
    letI := (ψ P hV hPV).toAlgebra
    IsLocalization (Msub P hV hPV) (semilocalIntegralClosure X P) := by
  let := (ψ P hV hPV).toAlgebra
  let P' : V := ⟨P, hPV⟩
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf P'
  have := hV.isLocalization_stalk P'
  have := functionField_isScalarTower X V P'
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    change IsUnit (ψ P hV hPV ((absoluteNormalizationMap X).app V a))
    rw [ψ_app]
    exact (IsLocalization.map_units (X.presheaf.stalk P')
      (⟨a, ha⟩ : (hV.primeIdealOf P').asIdeal.primeCompl)).map _
  · rintro ⟨z, hz⟩
    obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (M := (hV.primeIdealOf P').asIdeal.primeCompl) (Rₘ := X.presheaf.stalk P') z hz
    obtain ⟨s, hs⟩ := (mem_range_φ_iff X V hV _).mpr hmx
    refine ⟨(s, ⟨(absoluteNormalizationMap X).app V m, m, hm, rfl⟩), ?_⟩
    change _ * ψ P hV hPV ((absoluteNormalizationMap X).app V m) = ψ P hV hPV s
    rw [ψ_app]
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ψ_coe, hs, Submonoid.mk_smul,
      Algebra.smul_def, IsScalarTower.algebraMap_apply Γ(X, V) (X.presheaf.stalk P')
        X.functionField, mul_comm]
    rfl
  · intro x y h
    exact ⟨1, by rw [ψ_injective P hV hPV h]⟩

omit hPV [Nonempty V] in
lemma fromSpec_comap
    (q : PrimeSpectrum Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V)) :
    hV.fromSpec (PrimeSpectrum.comap ((absoluteNormalizationMap X).app V).hom q) =
      absoluteNormalizationMap X ((hV.preimage _).fromSpec q) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (absoluteNormalizationMap X) hV (hV.preimage _)
    le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact congr($h q)

variable (Q : absoluteNormalization X) (hQ : absoluteNormalizationMap X Q = P)
include hQ

omit hV [Nonempty V] in
lemma mem_preimage : Q ∈ absoluteNormalizationMap X ⁻¹ᵁ V := by
  change absoluteNormalizationMap X Q ∈ V
  rw [hQ]
  exact hPV

/-- The prime `𝔮_Q` of `B` at `Q`. -/
abbrev qQ : Ideal Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V) :=
  ((hV.preimage _).primeIdealOf ⟨Q, mem_preimage P hPV Q hQ⟩).asIdeal

omit [Nonempty V] in
lemma comap_qQ : (qQ P hV hPV Q hQ).comap ((absoluteNormalizationMap X).app V).hom =
    pP P hV hPV := by
  have h := fromSpec_comap hV ((hV.preimage _).primeIdealOf ⟨Q, mem_preimage P hPV Q hQ⟩)
  rw [IsAffineOpen.fromSpec_primeIdealOf, hQ] at h
  have h2 : hV.fromSpec (hV.primeIdealOf ⟨P, hPV⟩) = P := hV.fromSpec_primeIdealOf ⟨P, hPV⟩
  exact congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective (h.trans h2.symm))

omit [Nonempty V] in
lemma isLocalization_stalk_qQ :
    letI := TopCat.Presheaf.algebra_section_stalk (absoluteNormalization X).presheaf
      (⟨Q, mem_preimage P hPV Q hQ⟩ : absoluteNormalizationMap X ⁻¹ᵁ V)
    IsLocalization.AtPrime ((absoluteNormalization X).presheaf.stalk Q) (qQ P hV hPV Q hQ) :=
  (hV.preimage _).isLocalization_stalk _

/-- The map `Õ_P → 𝒪_{X̃,Q}` extending the germ map `B → 𝒪_{X̃,Q}`. -/
def ρ : semilocalIntegralClosure X P →+* (absoluteNormalization X).presheaf.stalk Q :=
  letI := (ψ P hV hPV).toAlgebra
  haveI := isLocalization_ψ P hV hPV
  IsLocalization.lift (M := Msub P hV hPV) (S := semilocalIntegralClosure X P)
    (g := ((absoluteNormalization X).presheaf.germ _ Q (mem_preimage P hPV Q hQ)).hom) (by
      rintro ⟨_, a, ha, rfl⟩
      let := TopCat.Presheaf.algebra_section_stalk (absoluteNormalization X).presheaf
        (⟨Q, mem_preimage P hPV Q hQ⟩ : absoluteNormalizationMap X ⁻¹ᵁ V)
      have := isLocalization_stalk_qQ P hV hPV Q hQ
      refine (IsLocalization.AtPrime.isUnit_to_map_iff
        ((absoluteNormalization X).presheaf.stalk Q) (qQ P hV hPV Q hQ)
        ((absoluteNormalizationMap X).app V a)).mpr ?_
      intro hmem
      apply ha
      rw [← comap_qQ P hV hPV Q hQ]
      exact hmem)

lemma ρ_ψ (b : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V)) :
    ρ P hV hPV Q hQ (ψ P hV hPV b) =
      (absoluteNormalization X).presheaf.germ _ Q (mem_preimage P hPV Q hQ) b := by
  let := (ψ P hV hPV).toAlgebra
  have := isLocalization_ψ P hV hPV
  exact IsLocalization.lift_eq _ _

lemma comap_ψ_comap_ρ :
    ((IsLocalRing.maximalIdeal _).comap (ρ P hV hPV Q hQ)).comap (ψ P hV hPV) =
      qQ P hV hPV Q hQ := by
  let := TopCat.Presheaf.algebra_section_stalk (absoluteNormalization X).presheaf
    (⟨Q, mem_preimage P hPV Q hQ⟩ : absoluteNormalizationMap X ⁻¹ᵁ V)
  have := isLocalization_stalk_qQ P hV hPV Q hQ
  ext b
  rw [Ideal.mem_comap, Ideal.mem_comap, ρ_ψ]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff
    ((absoluteNormalization X).presheaf.stalk Q) (qQ P hV hPV Q hQ) b

lemma isLocalization_ρ :
    letI := (ρ P hV hPV Q hQ).toAlgebra
    IsLocalization.AtPrime ((absoluteNormalization X).presheaf.stalk Q)
      ((IsLocalRing.maximalIdeal _).comap (ρ P hV hPV Q hQ)) := by
  let := (ψ P hV hPV).toAlgebra
  let := (ρ P hV hPV Q hQ).toAlgebra
  let := TopCat.Presheaf.algebra_section_stalk (absoluteNormalization X).presheaf
    (⟨Q, mem_preimage P hPV Q hQ⟩ : absoluteNormalizationMap X ⁻¹ᵁ V)
  have : IsScalarTower Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V)
      (semilocalIntegralClosure X P) ((absoluteNormalization X).presheaf.stalk Q) :=
    IsScalarTower.of_algebraMap_eq fun b => (ρ_ψ P hV hPV Q hQ b).symm
  have hloc1 := isLocalization_ψ P hV hPV
  have hloc2 := isLocalization_stalk_qQ P hV hPV Q hQ
  set 𝔫 := (IsLocalRing.maximalIdeal _).comap (ρ P hV hPV Q hQ)
  have hunder : 𝔫.comap (ψ P hV hPV) = qQ P hV hPV Q hQ := comap_ψ_comap_ρ P hV hPV Q hQ
  have hle : Msub P hV hPV ≤ (qQ P hV hPV Q hQ).primeCompl := by
    rintro _ ⟨a, ha, rfl⟩ hmem
    apply ha
    rw [← comap_qQ P hV hPV Q hQ]
    exact hmem
  have h3 := IsLocalization.isLocalization_of_submonoid_le (S := semilocalIntegralClosure X P)
    ((absoluteNormalization X).presheaf.stalk Q) (Msub P hV hPV) _ hle
  refine IsLocalization.isLocalization_of_is_exists_mul_mem
    (M := (qQ P hV hPV Q hQ).primeCompl.map (algebraMap _ (semilocalIntegralClosure X P)))
    (N := 𝔫.primeCompl) (S := (absoluteNormalization X).presheaf.stalk Q) ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩ hmem
    apply hb
    rw [← hunder]
    exact hmem
  · rintro ⟨x, hx⟩
    obtain ⟨⟨b, m⟩, e⟩ := IsLocalization.surj (Msub P hV hPV) x
    refine ⟨algebraMap _ _ (m : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V)), ?_⟩
    rw [mul_comm]
    refine ⟨b, ?_, e.symm⟩
    intro hb
    apply hx
    have hbn : algebraMap _ (semilocalIntegralClosure X P) b ∈ 𝔫 := by
      rw [← hunder] at hb
      exact hb
    rw [← e] at hbn
    refine (Ideal.IsPrime.mem_or_mem inferInstance hbn).resolve_right ?_
    intro hm
    have hm' : (m : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V)) ∈
        𝔫.comap (ψ P hV hPV) := hm
    rw [hunder] at hm'
    exact hle m.2 hm'

omit Q hQ in
lemma isMaximal_iff (𝔫 : Ideal (semilocalIntegralClosure X P)) [𝔫.IsPrime] :
    𝔫.IsMaximal ↔ (𝔫.comap (ψ P hV hPV)).comap ((absoluteNormalizationMap X).app V).hom =
      pP P hV hPV := by
  let P' : V := ⟨P, hPV⟩
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf P'
  have := hV.isLocalization_stalk P'
  have key : (𝔫.comap (ψ P hV hPV)).comap ((absoluteNormalizationMap X).app V).hom =
      (𝔫.comap (algebraMap (X.presheaf.stalk P) (semilocalIntegralClosure X P))).comap
        (algebraMap Γ(X, V) (X.presheaf.stalk P')) := by
    ext a
    simp only [Ideal.mem_comap, ψ_app]
    rfl
  have hmax : (IsLocalRing.maximalIdeal (X.presheaf.stalk P')).comap
      (algebraMap Γ(X, V) (X.presheaf.stalk P')) = pP P hV hPV :=
    IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk P') (pP P hV hPV)
  rw [key]
  constructor
  · intro h
    have : (𝔫.comap (algebraMap (X.presheaf.stalk P) (semilocalIntegralClosure X P))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := X.presheaf.stalk P) 𝔫
    rw [IsLocalRing.eq_maximalIdeal this]
    exact hmax
  · intro h
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := X.presheaf.stalk P)
    have : 𝔫.comap (algebraMap (X.presheaf.stalk P) (semilocalIntegralClosure X P)) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk P') := by
      rw [← IsLocalization.map_under (pP P hV hPV).primeCompl (X.presheaf.stalk P')
          (𝔫.comap (algebraMap (X.presheaf.stalk P) (semilocalIntegralClosure X P))),
        ← IsLocalization.map_under (pP P hV hPV).primeCompl (X.presheaf.stalk P')
          (IsLocalRing.maximalIdeal (X.presheaf.stalk P'))]
      exact congrArg _ (h.trans hmax.symm)
    rw [this]
    infer_instance

omit hQ in
/-- `Q ↦ 𝔫_Q` is a bijection from the fibre `ν⁻¹(P)` onto the maximal ideals of `Õ_P`. -/
lemma bijective_fibre :
    Function.Bijective (fun Q : absoluteNormalizationMap X ⁻¹' {P} =>
      (⟨(IsLocalRing.maximalIdeal _).comap (ρ P hV hPV Q.1 Q.2),
        (isMaximal_iff P hV hPV _).mpr (by
          rw [comap_ψ_comap_ρ P hV hPV Q.1 Q.2]
          exact comap_qQ P hV hPV Q.1 Q.2)⟩ : MaximalSpectrum (semilocalIntegralClosure X P))) := by
  let := (ψ P hV hPV).toAlgebra
  have hloc := isLocalization_ψ P hV hPV
  have hW := hV.preimage (absoluteNormalizationMap X)
  constructor
  · rintro ⟨Q₁, hQ₁⟩ ⟨Q₂, hQ₂⟩ h
    have h1 := congrArg (fun 𝔫 : MaximalSpectrum _ => 𝔫.asIdeal.comap (ψ P hV hPV)) h
    simp only at h1
    rw [comap_ψ_comap_ρ P hV hPV Q₁ hQ₁, comap_ψ_comap_ρ P hV hPV Q₂ hQ₂] at h1
    have h2 := congrArg hW.fromSpec (PrimeSpectrum.ext h1)
    simp only [IsAffineOpen.fromSpec_primeIdealOf] at h2
    exact Subtype.ext h2
  · intro 𝔫
    let 𝔮 : PrimeSpectrum Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ V) :=
      ⟨𝔫.asIdeal.comap (ψ P hV hPV), inferInstance⟩
    have hcomap := (isMaximal_iff P hV hPV 𝔫.asIdeal).mp 𝔫.isMaximal
    have hQ : absoluteNormalizationMap X (hW.fromSpec 𝔮) = P := by
      rw [← fromSpec_comap hV 𝔮]
      have : PrimeSpectrum.comap ((absoluteNormalizationMap X).app V).hom 𝔮 =
          hV.primeIdealOf ⟨P, hPV⟩ := PrimeSpectrum.ext hcomap
      rw [this]
      exact hV.fromSpec_primeIdealOf ⟨P, hPV⟩
    refine ⟨⟨hW.fromSpec 𝔮, hQ⟩, ?_⟩
    have hq : qQ P hV hPV (hW.fromSpec 𝔮) hQ = 𝔮.asIdeal := by
      have h1 : hW.fromSpec (hW.primeIdealOf ⟨hW.fromSpec 𝔮, mem_preimage P hPV _ hQ⟩) =
          hW.fromSpec 𝔮 := IsAffineOpen.fromSpec_primeIdealOf _ _
      exact congrArg PrimeSpectrum.asIdeal (hW.fromSpec.isOpenEmbedding.injective h1)
    apply MaximalSpectrum.ext
    change (IsLocalRing.maximalIdeal _).comap (ρ P hV hPV (hW.fromSpec 𝔮) hQ) = 𝔫.asIdeal
    rw [← IsLocalization.map_under (Msub P hV hPV) (semilocalIntegralClosure X P)
        ((IsLocalRing.maximalIdeal _).comap (ρ P hV hPV (hW.fromSpec 𝔮) hQ)),
      ← IsLocalization.map_under (Msub P hV hPV) (semilocalIntegralClosure X P) 𝔫.asIdeal]
    congr 1
    exact (comap_ψ_comap_ρ P hV hPV _ hQ).trans hq

end Fibre

end NormalizationDeltaAux

open NormalizationDeltaAux in
/-- **Hartshorne IV, Exercise 1.8 (the localizations of `Õ_P`).** For every point `Q` of `X̃`
over `P` there is a ring map `ρ_Q : Õ_P → 𝒪_{X̃,Q}` such that `𝔫_Q = ρ_Q⁻¹(𝔪_Q)` is a maximal
ideal of `Õ_P` and `ρ_Q` identifies `𝒪_{X̃,Q}` with the localization of `Õ_P` at `𝔫_Q`; and
`Q ↦ 𝔫_Q` is a bijection from the fibre `ν⁻¹(P)` onto the maximal ideals of `Õ_P`. -/
theorem exists_normalizationFibre_localization (P : X) :
    ∃ ρ : ∀ Q : absoluteNormalizationMap X ⁻¹' {P},
        semilocalIntegralClosure X P →+* (absoluteNormalization X).presheaf.stalk Q.1,
      (∀ Q, ((IsLocalRing.maximalIdeal _).comap (ρ Q)).IsMaximal ∧
        letI := (ρ Q).toAlgebra
        IsLocalization.AtPrime ((absoluteNormalization X).presheaf.stalk Q.1)
          ((IsLocalRing.maximalIdeal _).comap (ρ Q))) ∧
      Function.Injective (fun Q => (IsLocalRing.maximalIdeal _).comap (ρ Q)) ∧
      ∀ 𝔫 : Ideal (semilocalIntegralClosure X P), 𝔫.IsMaximal →
        ∃ Q, (IsLocalRing.maximalIdeal _).comap (ρ Q) = 𝔫 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hPV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ P) isOpen_univ
  have : Nonempty V := ⟨⟨P, hPV⟩⟩
  have hbij := bijective_fibre P hV hPV
  refine ⟨fun Q => ρ P hV hPV Q.1 Q.2, fun Q => ⟨?_, isLocalization_ρ P hV hPV Q.1 Q.2⟩,
    fun Q₁ Q₂ h => hbij.1 (MaximalSpectrum.ext h), fun 𝔫 h𝔫 => ?_⟩
  · exact (isMaximal_iff P hV hPV _).mpr (by
      rw [comap_ψ_comap_ρ P hV hPV Q.1 Q.2]
      exact comap_qQ P hV hPV Q.1 Q.2)
  · obtain ⟨Q, hQ⟩ := hbij.2 ⟨𝔫, h𝔫⟩
    exact ⟨Q, congrArg MaximalSpectrum.asIdeal hQ⟩

open NormalizationDeltaAux in
/-- For every point `Q` of `X̃` over `P` there is a maximal ideal `𝔫` of `Õ_P` whose localization
is isomorphic to the local ring `𝒪_{X̃,Q}`. -/
theorem nonempty_localization_ringEquiv_stalk (P : X) (Q : absoluteNormalization X)
    (hQ : absoluteNormalizationMap X Q = P) :
    ∃ (𝔫 : Ideal (semilocalIntegralClosure X P)) (_ : 𝔫.IsMaximal),
      Nonempty (Localization.AtPrime 𝔫 ≃+* (absoluteNormalization X).presheaf.stalk Q) := by
  obtain ⟨ρ, h, -⟩ := exists_normalizationFibre_localization X P
  obtain ⟨hmax, hloc⟩ := h ⟨Q, hQ⟩
  let := (ρ ⟨Q, hQ⟩).toAlgebra
  exact ⟨_, hmax, ⟨(IsLocalization.algEquiv
    ((IsLocalRing.maximalIdeal _).comap (ρ ⟨Q, hQ⟩)).primeCompl
    (Localization.AtPrime ((IsLocalRing.maximalIdeal _).comap (ρ ⟨Q, hQ⟩)))
    ((absoluteNormalization X).presheaf.stalk Q)).toRingEquiv⟩⟩

end

end Hartshorne
