/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.GeneratedProjProjective
import Hartshorne.Scheme.RelativeSegre

/-!
# Projective space over `Spec R` is `Proj R[x₀, …, xₙ]`

Relative projective space `ℙⁿ_{Spec R} = ℙⁿ_ℤ ×_ℤ Spec R` (`projectiveSpaceOverScheme`) is
isomorphic over `Spec R` to `Proj R[x₀, …, xₙ]` (`Hartshorne.projectiveSpaceOverSpecIso`). The
comparison allows any renumbering `e` of the coordinates: the coordinate `z_l` of `ℙⁿ_ℤ` is sent
to `x_{e l}`.

The morphism `Proj R[x] ⟶ ℙⁿ_{Spec R}` is the closed immersion of
`GeneratedProj.toProjectiveSpace` (for the generators `x_{e l}`), and its inverse is glued from
the charts: on the preimage of `D₊(z_l)` the inverse is the chart map to `D₊(x_{e l})` sending
`x_m` to the pulled-back ratio `z_{e⁻¹ m}/z_l` and the scalars through the projection to
`Spec R`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

section General

/-- A ring map `A_(f) → B` induced by `F : A → B` sends the degree-zero element `a / 1` to
`F a`. -/
theorem awayLift_fromZeroRingHom {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {B : Type*} [CommRing B] (F : A →+* B) {f : A}
    (hf : IsUnit (F f)) (x : 𝒜 0) :
    awayLift (𝒜 := 𝒜) F f hf (fromZeroRingHom 𝒜 _ x) = F x := by
  simp only [awayLift, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply]
  have h : (fromZeroRingHom 𝒜 (Submonoid.powers f) x).val =
      algebraMap A (Localization.Away f) x := by
    rw [← Localization.mk_one_eq_algebraMap]
    rfl
  rw [h]
  exact IsLocalization.lift_eq _ _

/-- A morphism to an affine scheme `Spec R`, restricted to an open `V`, is `Spec` of the induced
ring map `R → Γ(V)`. -/
theorem ι_comp_eq_toSpecΓ_SpecMap_of_Spec {Y : Scheme.{u}} {R : CommRingCat.{u}} (φ : Y ⟶ Spec R)
    (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ ⊤) :
    V.ι ≫ φ = V.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ φ.appLE ⊤ V h) := by
  rw [Spec.map_comp, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Scheme.Hom.resLE_comp_ι φ h,
    Scheme.Opens.toSpecΓ_top, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Ring maps out of the chart ring `ℤ[z]_(z_c)` agree on the constants. -/
theorem chartConst_ext {κ : Type} {B : Type*} [CommRing B] (c0 : κ)
    (φ ψ : Away (homogeneousSubmodule κ (ULift.{u} ℤ)) (X c0) →+* B) (r : ULift.{u} ℤ) :
    φ (chartConst _ c0 r) = ψ (chartConst _ c0 r) :=
  RingHom.congr_fun (ulift_int_ringHom_ext (φ.comp (chartConst _ c0)) (ψ.comp (chartConst _ c0))) r

end General

variable (R : Type u) [CommRing R] (n : ℕ) (e : Fin (n + 1) ≃ Fin (n + 1))

local notation "𝒮" => homogeneousSubmodule (Fin (n + 1)) R

section Embedding

/-- The degree-zero part of `R[x₀, …, xₙ]` is `R`. -/
theorem bijective_algebraMap_homogeneousSubmodule_zero :
    Function.Bijective (algebraMap R (𝒮 0)) := by
  refine ⟨fun r s h => C_injective (Fin (n + 1)) R (congrArg Subtype.val h), fun a => ?_⟩
  have ha : (a : MvPolynomial (Fin (n + 1)) R) ∈ (1 : Submodule R (MvPolynomial (Fin (n + 1)) R)) :=
    homogeneousSubmodule_zero (σ := Fin (n + 1)) (R := R) ▸ a.2
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp ha
  exact ⟨r, Subtype.ext hr⟩

instance : IsIso (CommRingCat.ofHom (algebraMap R (𝒮 0))) :=
  (RingEquiv.ofBijective _
    (bijective_algebraMap_homogeneousSubmodule_zero R n)).toCommRingCatIso.isIso_hom

/-- The generators `x_{e l}`. -/
abbrev projectiveSpaceGenerators : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R := fun l => X (e l)

theorem projectiveSpaceGenerators_mem (l : Fin (n + 1)) :
    projectiveSpaceGenerators R n e l ∈ 𝒮 1 :=
  X_mem_homogeneousSubmodule_one _ _

theorem adjoin_projectiveSpaceGenerators :
    Algebra.adjoin (𝒮 0) (Set.range (projectiveSpaceGenerators R n e)) = ⊤ := by
  rw [eq_top_iff]
  rintro P -
  induction P using MvPolynomial.induction_on with
  | C r =>
    have h : (C r : MvPolynomial (Fin (n + 1)) R) =
        algebraMap (𝒮 0) (MvPolynomial (Fin (n + 1)) R) (algebraMap R (𝒮 0) r) := rfl
    rw [h]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact add_mem hp hq
  | mul_X p m hp =>
    exact mul_mem hp (Algebra.subset_adjoin ⟨e.symm m, show X (e (e.symm m)) = X m by
      rw [Equiv.apply_symm_apply]⟩)

/-- The graded homomorphism `ℤ[z₀, …, zₙ] → R[x₀, …, xₙ]`, `z_l ↦ x_{e l}`. -/
abbrev projectiveSpaceComparisonHom : GeneratedProj.intGrading.{u} n →+*ᵍ 𝒮 :=
  GeneratedProj.evalGradedHom 𝒮 (projectiveSpaceGenerators_mem R n e)

theorem projectiveSpaceComparisonHom_X_mem (m : Fin (n + 1)) :
    projectiveSpaceComparisonHom R n e (X m) ∈ 𝒮 1 :=
  (projectiveSpaceComparisonHom R n e).map_mem (X_mem_homogeneousSubmodule_one _ m)

theorem projectiveSpaceComparisonHom_X (l : Fin (n + 1)) :
    projectiveSpaceComparisonHom R n e (X l) = X (e l) :=
  GeneratedProj.evalRingHom_X _ _

/-- The morphism `Proj R[x₀, …, xₙ] ⟶ ℙⁿ_ℤ` pulling `z_l` back to `x_{e l}`. -/
def projToProjectiveSpaceInt : Proj 𝒮 ⟶ Proj (GeneratedProj.intGrading.{u} n) :=
  GeneratedProj.toProjectiveSpaceInt 𝒮 (projectiveSpaceGenerators_mem R n e)
    (adjoin_projectiveSpaceGenerators R n e)

/-- The comparison morphism `Proj R[x₀, …, xₙ] ⟶ ℙⁿ_{Spec R}` over `Spec R`, pulling `z_l` back
to `x_{e l}`. -/
def projToProjectiveSpaceOverSpec :
    Proj 𝒮 ⟶ projectiveSpaceOverScheme n (Spec (.of R)) :=
  pullback.lift
    (projToProjectiveSpaceInt R n e)
    (Proj.toSpecZero 𝒮 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒮 0))))
    (specULiftZIsTerminal.hom_ext _ _)

@[reassoc (attr := simp)]
theorem projToProjectiveSpaceOverSpec_fst :
    projToProjectiveSpaceOverSpec R n e ≫ pullback.fst _ _ =
      projToProjectiveSpaceInt R n e :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem projToProjectiveSpaceOverSpec_projection :
    projToProjectiveSpaceOverSpec R n e ≫ projectiveSpaceOverSchemeProjection _ _ =
      Proj.toSpecZero 𝒮 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒮 0))) :=
  pullback.lift_snd _ _ _

instance : IsClosedImmersion (projToProjectiveSpaceOverSpec R n e) := by
  have h : projToProjectiveSpaceOverSpec R n e =
      GeneratedProj.toProjectiveSpace 𝒮 (projectiveSpaceGenerators_mem R n e)
          (adjoin_projectiveSpaceGenerators R n e) ≫
        projectiveSpaceOverSchemeMap _ (Spec.map (CommRingCat.ofHom (algebraMap R (𝒮 0)))) := by
    apply pullback.hom_ext
    · rw [projToProjectiveSpaceOverSpec_fst, Category.assoc, projectiveSpaceOverSchemeMap_fst,
        GeneratedProj.toProjectiveSpace_fst]
      rfl
    · rw [projToProjectiveSpaceOverSpec_projection, Category.assoc,
        projectiveSpaceOverSchemeMap_projection, ← Category.assoc,
        GeneratedProj.toProjectiveSpace_projection]
  rw [h]
  have := GeneratedProj.isClosedImmersion_toProjectiveSpace 𝒮 (projectiveSpaceGenerators_mem R n e)
    (adjoin_projectiveSpaceGenerators R n e)
  have : IsIso (projectiveSpaceOverSchemeMap n
      (Spec.map (CommRingCat.ofHom (algebraMap R (𝒮 0))))) := by
    unfold projectiveSpaceOverSchemeMap
    infer_instance
  infer_instance

end Embedding

section Inverse

/-- The projection `ℙⁿ_{Spec R} ⟶ ℙⁿ_ℤ`, typed as a morphism to `Proj`. -/
abbrev projectiveSpaceOverSpecFst :
    projectiveSpaceOverScheme n (Spec (.of R)) ⟶ Proj (GeneratedProj.intGrading.{u} n) :=
  pullback.fst _ _

/-- The chart of `ℙⁿ_{Spec R}` over `D₊(z_l)`. -/
def projectiveSpaceOverSpecChart (l : Fin (n + 1)) :
    (projectiveSpaceOverScheme n (Spec (.of R))).Opens :=
  projectiveSpaceOverSpecFst R n ⁻¹ᵁ Proj.basicOpen _ (X l)

theorem projectiveSpaceOverSpecChart_eq (l : Fin (n + 1)) :
    projectiveSpaceOverSpecChart R n l =
      projectiveSpaceOverSpecFst R n ⁻¹ᵁ Proj.basicOpen (GeneratedProj.intGrading.{u} n) (X l) :=
  rfl

theorem projectiveSpaceOverSpecChart_isOpenCover :
    TopologicalSpace.IsOpenCover (projectiveSpaceOverSpecChart R n) := by
  refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ => ?_)
  have hx : projectiveSpaceOverSpecFst R n x ∈
      ⨆ l, Proj.basicOpen (GeneratedProj.intGrading.{u} n) (X l) := by
    rw [iSup_proj_basicOpen_X_eq_top]
    trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, hl⟩

/-- The pulled-back ratio `z_m / z_l` on the chart over `D₊(z_l)`. -/
def projectiveSpaceOverSpecRatio (l m : Fin (n + 1)) :
    Γ(projectiveSpaceOverScheme n (Spec (.of R)), projectiveSpaceOverSpecChart R n l) :=
  (projectiveSpaceOverSpecFst R n).appLE _ (projectiveSpaceOverSpecChart R n l) le_rfl
    (Proj.awayToSection _ (X l) (chartRatio _ l m))

theorem projectiveSpaceOverSpecRatio_self (l : Fin (n + 1)) :
    projectiveSpaceOverSpecRatio R n l l = 1 := by
  rw [projectiveSpaceOverSpecRatio, chartRatio_self, map_one, map_one]

/-- The scalars `R → Γ` on the chart over `D₊(z_l)`. -/
def projectiveSpaceOverSpecScalar (l : Fin (n + 1)) :
    R →+* Γ(projectiveSpaceOverScheme n (Spec (.of R)), projectiveSpaceOverSpecChart R n l) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (projectiveSpaceOverSchemeProjection n (Spec (.of R))).appLE ⊤
    (projectiveSpaceOverSpecChart R n l) (show _ ≤ _ ⁻¹ᵁ ⊤ from le_top)).hom

/-- The ring map `R[x₀, …, xₙ] → Γ` on the chart over `D₊(z_l)`, `x_m ↦ z_{e⁻¹ m}/z_l`. -/
def projectiveSpaceOverSpecRingHom (l : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →+*
      Γ(projectiveSpaceOverScheme n (Spec (.of R)), projectiveSpaceOverSpecChart R n l) :=
  eval₂Hom (projectiveSpaceOverSpecScalar R n l)
    fun m => projectiveSpaceOverSpecRatio R n l (e.symm m)

theorem projectiveSpaceOverSpecRingHom_comparison_X (l m : Fin (n + 1)) :
    projectiveSpaceOverSpecRingHom R n e l (projectiveSpaceComparisonHom R n e (X m)) =
      projectiveSpaceOverSpecRatio R n l m := by
  simp [projectiveSpaceComparisonHom_X, projectiveSpaceOverSpecRingHom]

theorem isUnit_projectiveSpaceOverSpecRingHom (l : Fin (n + 1)) :
    IsUnit (projectiveSpaceOverSpecRingHom R n e l (projectiveSpaceComparisonHom R n e (X l))) := by
  rw [projectiveSpaceOverSpecRingHom_comparison_X, projectiveSpaceOverSpecRatio_self]
  exact isUnit_one

/-- The chart map from the chart over `D₊(z_l)` to `D₊(x_{e l}) ⊆ Proj R[x]`. -/
def projectiveSpaceOverSpecChartMap (l : Fin (n + 1)) :
    (projectiveSpaceOverSpecChart R n l).toScheme ⟶ Proj 𝒮 :=
  (projectiveSpaceOverSpecChart R n l).toSpecΓ ≫
    projChartMap (projectiveSpaceOverSpecRingHom R n e l)
      ((projectiveSpaceComparisonHom R n e).map_mem (X_mem_homogeneousSubmodule_one _ l))
      Nat.one_pos (isUnit_projectiveSpaceOverSpecRingHom R n e l)

theorem awayι_comp_toProjectiveSpaceInt (l : Fin (n + 1)) :
    Proj.awayι 𝒮 _ ((projectiveSpaceComparisonHom R n e).map_mem
        (X_mem_homogeneousSubmodule_one _ l)) Nat.one_pos ≫
      projToProjectiveSpaceInt R n e =
    Spec.map (CommRingCat.ofHom (Away.map (projectiveSpaceComparisonHom R n e) (X l))) ≫
      Proj.awayι _ (X l) (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos :=
  Proj.awayι_comp_map _ _ Nat.one_pos _ (X_mem_homogeneousSubmodule_one _ _)

theorem away_map_comparison_chartRatio (l m : Fin (n + 1)) :
    Away.map (projectiveSpaceComparisonHom R n e) (X l) (chartRatio _ l m) =
      Away.mk 𝒮 ((projectiveSpaceComparisonHom R n e).map_mem (X_mem_homogeneousSubmodule_one _ l))
        1 (projectiveSpaceComparisonHom R n e (X m))
        (by simpa using projectiveSpaceComparisonHom_X_mem R n e m) := by
  rw [chartRatio, Away.map_mk]

theorem projectiveSpaceOverSpecChartMap_comp_fst (l : Fin (n + 1)) :
    projectiveSpaceOverSpecChartMap R n e l ≫
        projToProjectiveSpaceInt R n e =
      (projectiveSpaceOverSpecChart R n l).ι ≫ projectiveSpaceOverSpecFst R n := by
  rw [ι_comp_eq_toSpecΓ_SpecMap (projectiveSpaceOverSpecFst R n) (projectiveSpaceOverSpecChart R n l)
    (X_mem_homogeneousSubmodule_one _ l) Nat.one_pos
    (projectiveSpaceOverSpecChart_eq R n l).le,
    projectiveSpaceOverSpecChartMap, projChartMap, Category.assoc, Category.assoc,
    awayι_comp_toProjectiveSpaceInt, ← Category.assoc (Spec.map _), ← Spec.map_comp]
  congr 3
  ext1
  apply chart_ringHom_ext l
  · intro r
    exact chartConst_ext _ _ _ r
  · intro m
    have key := awayLift_mk (𝒜 := 𝒮) (projectiveSpaceOverSpecRingHom R n e l)
      (isUnit_projectiveSpaceOverSpecRingHom R n e l)
      ((projectiveSpaceComparisonHom R n e).map_mem (X_mem_homogeneousSubmodule_one _ l)) 1
      (projectiveSpaceComparisonHom R n e (X m))
      (by simpa using projectiveSpaceComparisonHom_X_mem R n e m)
    rw [projectiveSpaceOverSpecRingHom_comparison_X, projectiveSpaceOverSpecRatio_self, one_pow,
      mul_one, projectiveSpaceOverSpecRingHom_comparison_X] at key
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [away_map_comparison_chartRatio]
    exact key

theorem projectiveSpaceOverSpecChartMap_comp_projection (l : Fin (n + 1)) :
    projectiveSpaceOverSpecChartMap R n e l ≫ Proj.toSpecZero 𝒮 ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (𝒮 0))) =
      (projectiveSpaceOverSpecChart R n l).ι ≫ projectiveSpaceOverSchemeProjection n _ := by
  rw [ι_comp_eq_toSpecΓ_SpecMap_of_Spec _ _ (show _ ≤ _ ⁻¹ᵁ ⊤ from le_top),
    projectiveSpaceOverSpecChartMap, projChartMap, Category.assoc, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext r
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rw [awayLift_fromZeroRingHom]
  change projectiveSpaceOverSpecRingHom R n e l (C r) = _
  rw [projectiveSpaceOverSpecRingHom, eval₂Hom_C]
  rfl

theorem projectiveSpaceOverSpecChartMap_comp (l : Fin (n + 1)) :
    projectiveSpaceOverSpecChartMap R n e l ≫ projToProjectiveSpaceOverSpec R n e =
      (projectiveSpaceOverSpecChart R n l).ι := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg _ (projToProjectiveSpaceOverSpec_fst R n e)).trans
        (projectiveSpaceOverSpecChartMap_comp_fst R n e l))
  · exact (Category.assoc _ _ _).trans
      ((congrArg _ (projToProjectiveSpaceOverSpec_projection R n e)).trans
        (projectiveSpaceOverSpecChartMap_comp_projection R n e l))

/-- The inverse comparison `ℙⁿ_{Spec R} ⟶ Proj R[x₀, …, xₙ]`, glued from the charts. -/
def projectiveSpaceOverSpecToProj :
    projectiveSpaceOverScheme n (Spec (.of R)) ⟶ Proj 𝒮 :=
  glueOpens (projectiveSpaceOverSpecChart R n) (projectiveSpaceOverSpecChart_isOpenCover R n)
    (projectiveSpaceOverSpecChartMap R n e) (by
      intro x y
      rw [← cancel_mono (projToProjectiveSpaceOverSpec R n e)]
      simp only [Category.assoc, projectiveSpaceOverSpecChartMap_comp, Scheme.homOfLE_ι])

theorem ι_projectiveSpaceOverSpecToProj_comp (l : Fin (n + 1)) :
    (projectiveSpaceOverSpecChart R n l).ι ≫ projectiveSpaceOverSpecToProj R n e ≫
        projToProjectiveSpaceOverSpec R n e =
      (projectiveSpaceOverSpecChart R n l).ι ≫ 𝟙 _ := by
  rw [projectiveSpaceOverSpecToProj, ι_glueOpens_assoc, projectiveSpaceOverSpecChartMap_comp,
    Category.comp_id]

theorem projectiveSpaceOverSpecToProj_comp :
    projectiveSpaceOverSpecToProj R n e ≫ projToProjectiveSpaceOverSpec R n e = 𝟙 _ :=
  (Scheme.openCoverOfIsOpenCover _ (projectiveSpaceOverSpecChart R n)
    (projectiveSpaceOverSpecChart_isOpenCover R n)).hom_ext _ _ fun l =>
      ι_projectiveSpaceOverSpecToProj_comp R n e l

end Inverse

/-- **Projective space over `Spec R` is `Proj R[x₀, …, xₙ]`.** The comparison isomorphism
`Proj R[x₀, …, xₙ] ≅ ℙⁿ_{Spec R} = ℙⁿ_ℤ ×_ℤ Spec R`, pulling the coordinate `z_l` of `ℙⁿ_ℤ` back to
`x_{e l}`; it is a morphism over `Spec R` (`projToProjectiveSpaceOverSpec_projection`). -/
def projectiveSpaceOverSpecIso : Proj 𝒮 ≅ projectiveSpaceOverScheme n (Spec (.of R)) where
  hom := projToProjectiveSpaceOverSpec R n e
  inv := projectiveSpaceOverSpecToProj R n e
  hom_inv_id := by
    rw [← cancel_mono (projToProjectiveSpaceOverSpec R n e), Category.assoc,
      projectiveSpaceOverSpecToProj_comp, Category.comp_id, Category.id_comp]
  inv_hom_id := projectiveSpaceOverSpecToProj_comp R n e

@[simp]
theorem projectiveSpaceOverSpecIso_hom :
    (projectiveSpaceOverSpecIso R n e).hom = projToProjectiveSpaceOverSpec R n e :=
  rfl

end Hartshorne
