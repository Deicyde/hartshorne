/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeProjTwistingSheaf
import Hartshorne.Scheme.RelativeProjLineBundleTwistFrames
import Hartshorne.Scheme.ProjectiveClosedImmersionChartCriterion
import Hartshorne.Scheme.AmpleSectionsAffineBasis
import Hartshorne.Scheme.ProjectionFromPoint
import Hartshorne.Scheme.SerreGlobalGeneration

/-!
# Charts for embedding a relative Proj into projective space

Auxiliary results for Hartshorne II, Proposition 7.10(b).

* `IsTrivializingSection.restrictLE`, `IsTrivializingSection.sectionPowSMul`: trivializing
  sections restrict to smaller opens, and `f^n s` trivializes `F ⊗ L^{⊗ n}` when `s` trivializes
  `F` and `f` trivializes `L`.
* `isAffineOpen_preimage_inf_projectiveSpaceChart`: over an affine open `U` of `Y`, the part of
  the standard open `D₊(xᵢ)` of `ℙⁿ_Y` lying over `U` is affine.
* `isImmersion_of_forall_isClosedImmersion_morphismRestrict`: a morphism which is a closed
  immersion over each member of a family of opens whose preimages cover the source is an
  immersion.
* `HomogeneousLocalization.Away.mem_closure_of_adjoin_eq_top`: if `A` is generated over `A₀` by
  elements `vᵢ` of degree one and `f` has degree one, then `A_(f)` is generated as a ring by the
  image of `A₀` and the fractions `vᵢ/f`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

section Trivializing

variable {X : Scheme.{u}}

/-- A trivializing section restricts to a trivializing section on a smaller open. -/
theorem IsTrivializingSection.restrictLE {L : X.Modules} {U V : X.Opens} {e : Γ(L, U)}
    (he : IsTrivializingSection L U e) (h : V ≤ U) :
    IsTrivializingSection L V (L.presheaf.map (homOfLE h).op e) := by
  intro W hW
  have := he W (hW.trans h)
  convert this using 2 with a
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- If `s` trivializes `F` and `f` trivializes `L` on `U`, then `f^n s = s ⊗ f^{⊗ n}` trivializes
`F ⊗ L^{⊗ n}` on `U`. -/
theorem IsTrivializingSection.sectionPowSMul {F L : X.Modules} {U : X.Opens} {s : Γ(F, U)}
    {f : Γ(L, U)} (hs : IsTrivializingSection F U s) (hf : IsTrivializingSection L U f) (n : ℕ) :
    IsTrivializingSection (tensorPowerTwist F L n) U (Hartshorne.sectionPowSMul F L n f s) :=
  IsTrivializingSection.of_isLocalFrame (ι := ULift.{u} (Fin 1))
    ((isLocalFrame_of_isTrivializingSection hs).tensor
      (Ringed.IsLocalFrame.moduleSheafTensorPower (isLocalFrame_of_isTrivializingSection hf) n))

/-- `f^n (a s) = a (f^n s)`. -/
theorem sectionPowSMul_smul_right {F L : X.Modules} {n : ℕ} {U : X.Opens} (f : Γ(L, U))
    (a : Γ(X, U)) (s : Γ(F, U)) :
    Hartshorne.sectionPowSMul F L n f (a • s) = a • Hartshorne.sectionPowSMul F L n f s := by
  unfold Hartshorne.sectionPowSMul
  erw [LinearMap.map_smul₂]
  rfl

/-- A section restricting to a trivializing section on `U` does not vanish at any point of
`U`. -/
theorem mem_nonvanishingLocus_of_isTrivializingSection {L : X.Modules} {U : X.Opens}
    {f : Γ(L, ⊤)} (hf : IsTrivializingSection L U (L.presheaf.map (homOfLE le_top).op f))
    {x : X} (hx : x ∈ U) : x ∈ nonvanishingLocus L f := by
  rw [hf.mem_nonvanishingLocus_iff (g := 1) (one_smul _ _).symm hx, Scheme.basicOpen_one]
  trivial

end Trivializing

section Charts

/-- Over an affine open `U` of `Y`, the part `π⁻¹(U) ∩ D₊(xᵢ)` of the standard open `D₊(xᵢ)` of
`ℙⁿ_Y` lying over `U` is affine. -/
theorem isAffineOpen_preimage_inf_projectiveSpaceChart (n : ℕ) {Y : Scheme.{u}} {U : Y.Opens}
    (hU : IsAffineOpen U) (i : Fin (n + 1)) :
    IsAffineOpen (projectiveSpaceOverSchemeProjection n Y ⁻¹ᵁ U ⊓ projectiveSpaceChart n Y i) := by
  let C := chartInt.{u} n i
  have hC : IsAffineOpen C :=
    Proj.isAffineOpen_basicOpen _ _ (X_mem_homogeneousSubmodule_one _ i) Nat.one_pos
  have : IsAffine C := hC
  let g : (projectiveSpaceChart n Y i).toScheme ⟶ Y :=
    (projectiveSpaceChart n Y i).ι ≫ projectiveSpaceOverSchemeProjection n Y
  have hsq : IsPullback (toProjInt n Y ∣_ C) g (C.ι ≫ projectiveSpaceOverIntegersMap n)
      (schemeToSpecZ Y) :=
    (isPullback_morphismRestrict (toProjInt n Y) C).paste_vert (IsPullback.of_hasPullback _ _)
  have : IsAffineHom (C.ι ≫ projectiveSpaceOverIntegersMap n) := isAffineHom_of_isAffine _
  have : IsAffineHom g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) hsq this
  have h := (hU.preimage g).image_of_isOpenImmersion (projectiveSpaceChart n Y i).ι
  rwa [show g ⁻¹ᵁ U = (projectiveSpaceChart n Y i).ι ⁻¹ᵁ
      (projectiveSpaceOverSchemeProjection n Y ⁻¹ᵁ U) from rfl,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm] at h

/-- A morphism `φ : X ⟶ Y` which is a closed immersion over each `Wᵢ`, where the preimages
`φ⁻¹(Wᵢ)` cover `X`, is an immersion: it is a closed immersion into the open `⋃ Wᵢ`. -/
theorem isImmersion_of_forall_isClosedImmersion_morphismRestrict {X Y : Scheme.{u}}
    (φ : X ⟶ Y) {ι : Type*} (W : ι → Y.Opens) (hpre : ⨆ i, φ ⁻¹ᵁ W i = ⊤)
    (h : ∀ i, IsClosedImmersion (φ ∣_ W i)) : IsImmersion φ := by
  set U := ⨆ i, W i with hU
  have hcov : ⨆ i, U.ι ⁻¹ᵁ W i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Opens.ι_preimage_self]
  have hcl : IsClosedImmersion (φ ∣_ U) := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ hcov]
    intro i
    have hi : U.ι ''ᵁ U.ι ⁻¹ᵁ W i = W i := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (le_iSup W i)
    rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (morphismRestrictRestrict φ U _),
      MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (morphismRestrictEq φ hi)]
    exact h i
  have htop : φ ⁻¹ᵁ U = ⊤ := by rw [hU, Scheme.Hom.preimage_iSup, hpre]
  have : IsImmersion ((φ ⁻¹ᵁ U).ι ≫ φ) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have : IsIso (φ ⁻¹ᵁ U).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
    have hx : x ∈ φ ⁻¹ᵁ U := htop ▸ trivial
    exact ⟨⟨x, hx⟩, rfl⟩
  rw [show φ = inv (φ ⁻¹ᵁ U).ι ≫ (φ ⁻¹ᵁ U).ι ≫ φ by simp]
  infer_instance

end Charts

section Away

open HomogeneousLocalization

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

private theorem away_mk_prod_pow {f : A} (hf : f ∈ 𝒜 1) {ι : Type*} (v : ι → A)
    (hv : ∀ i, v i ∈ 𝒜 1) (ai : ι → ℕ) (s : Finset ι) (hs : (∏ i ∈ s, v i ^ ai i) ∈
      𝒜 ((∑ i ∈ s, ai i) • 1)) :
    Away.mk 𝒜 hf (∑ i ∈ s, ai i) (∏ i ∈ s, v i ^ ai i) hs =
      ∏ i ∈ s, Away.mk 𝒜 hf 1 (v i) (by rw [smul_eq_mul, mul_one]; exact hv i) ^ ai i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply HomogeneousLocalization.val_injective
    simp [Away.val_mk]
  | insert j s hj ih =>
    have hs' : (∏ i ∈ s, v i ^ ai i) ∈ 𝒜 ((∑ i ∈ s, ai i) • 1) := by
      have := SetLike.prod_pow_mem_graded 𝒜 (fun _ => 1) v ai (F := s) fun i _ => hv i
      simpa using this
    conv_rhs => rw [Finset.prod_insert hj, ← ih hs']
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, Away.val_mk,
      Localization.mk_pow, Localization.mk_mul]
    congr 1
    · rw [Finset.prod_insert hj]
    · ext
      simp [Finset.sum_insert hj, pow_add]

/-- If `A` is generated over `A₀` by elements `vᵢ` of degree one and `f` has degree one, then
`A_(f)` is generated as a ring by the image of `A₀` and the fractions `vᵢ/f`. -/
theorem away_mem_closure_of_adjoin_eq_top {f : A} (hf : f ∈ 𝒜 1) {ι : Type*} [Fintype ι]
    (v : ι → A) (hv : ∀ i, v i ∈ 𝒜 1) (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)
    (z : Away 𝒜 f) :
    z ∈ Subring.closure (Set.range (fromZeroRingHom 𝒜 (Submonoid.powers f)) ∪
      Set.range (fun i => Away.mk 𝒜 hf 1 (v i) (by rw [smul_eq_mul, mul_one]; exact hv i))) := by
  classical
  set T := Subring.closure (Set.range (fromZeroRingHom 𝒜 (Submonoid.powers f)) ∪
      Set.range (fun i => Away.mk 𝒜 hf 1 (v i) (by rw [smul_eq_mul, mul_one]; exact hv i)))
  have htop := Away.adjoin_mk_prod_pow_eq_top hf ι v hgen (fun _ => 1) hv
  have hz : z ∈ Algebra.adjoin (𝒜 0) _ := htop ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun z _ => z ∈ T) ?_ ?_ ?_ ?_ hz
  · rintro x ⟨a, ai, hai, -, rfl⟩
    have ha : a = ∑ i, ai i := by simpa using hai.symm
    subst ha
    rw [away_mk_prod_pow hf v hv ai Finset.univ]
    refine prod_mem fun i _ => pow_mem ?_ _
    exact Subring.subset_closure (Set.mem_union_right _ ⟨i, rfl⟩)
  · exact fun r => Subring.subset_closure (Set.mem_union_left _ ⟨r, rfl⟩)
  · exact fun x y _ _ hx hy => T.add_mem hx hy
  · exact fun x y _ _ hx hy => T.mul_mem hx hy

end Away

end Hartshorne
