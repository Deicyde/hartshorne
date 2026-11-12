/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveBundleTrivialization
import Hartshorne.Scheme.ProjectiveMorphismCalculus
import Hartshorne.Scheme.RelativeProjDesc
import Hartshorne.Scheme.MorphismFromGeneratedLineBundle

/-!
# Projective bundles of free modules over an arbitrary open

Hartshorne, *Algebraic Geometry*, II.7, p. 162: if `E` is free of rank `n + 1` over an open
`U ⊆ X`, then `P(E)|_U ≅ ℙⁿ_U` over `U`. Over an affine open `V` with a frame this is
`Scheme.Modules.projectiveBundleFrameIso`. For an arbitrary open `U` with a frame `e`, the
identifications over the affine opens `V ⊆ U` (with the restricted frames) are compatible: over
a basic open `D(r) ⊆ V` the restriction of the identification over `V` is the identification over
`D(r)`, because both send the coordinate `z_k` of `ℙⁿ_ℤ` to the frame element `e_k`. Every
intersection `V ∩ V'` is covered by opens basic in both, so the identifications glue
(`Hartshorne.exists_iso_of_openImmersions_over`) to an isomorphism `π⁻¹(U) ≅ ℙⁿ_U` over `U`
(`Scheme.Modules.exists_projectiveBundleIso_of_frame`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

open AlgebraicGeometry

section GlueIso

/-- **Gluing isomorphisms over a base.** Let `f : Y ⟶ B` and `g : Z ⟶ B`, and let `O i` be opens of
`B` covering the images of `f` and `g`. Suppose given open immersions `φ i : f⁻¹(O i) ⟶ Z` over `B`
whose images contain `g⁻¹(O i)`, such that every point of `O i ∩ O j` lies in some `O k ⊆ O i ∩ O j`
on which `φ i` and `φ j` both restrict to `φ k`. Then the `φ i` glue to an isomorphism `Y ≅ Z` over
`B`. -/
theorem exists_iso_of_openImmersions_over {Y Z B : Scheme.{u}} (f : Y ⟶ B) (g : Z ⟶ B)
    {ι : Type*} (O : ι → B.Opens) (φ : ∀ i, (f ⁻¹ᵁ O i).toScheme ⟶ Z)
    [∀ i, IsOpenImmersion (φ i)] (hover : ∀ i, φ i ≫ g = (f ⁻¹ᵁ O i).ι ≫ f)
    (hrange : ∀ i, g ⁻¹ᵁ O i ≤ (φ i).opensRange)
    (hY : ∀ y : Y, ∃ i, f y ∈ O i) (hZ : ∀ z : Z, ∃ i, g z ∈ O i)
    (hcompat : ∀ i j, ∀ b ∈ O i ⊓ O j, ∃ k, ∃ (hki : O k ≤ O i) (hkj : O k ≤ O j), b ∈ O k ∧
      Y.homOfLE (f.preimage_mono hki) ≫ φ i = φ k ∧
        Y.homOfLE (f.preimage_mono hkj) ≫ φ j = φ k) :
    ∃ Φ : Y ≅ Z, Φ.hom ≫ g = f ∧ ∀ i, (f ⁻¹ᵁ O i).ι ≫ Φ.hom = φ i := by
  have hU : IsOpenCover (fun i => f ⁻¹ᵁ O i) := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨i, hi⟩ := hY y
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  have hg : ∀ i j, Y.homOfLE (inf_le_left : f ⁻¹ᵁ O i ⊓ f ⁻¹ᵁ O j ≤ f ⁻¹ᵁ O i) ≫ φ i =
      Y.homOfLE (inf_le_right : f ⁻¹ᵁ O i ⊓ f ⁻¹ᵁ O j ≤ f ⁻¹ᵁ O j) ≫ φ j := by
    intro i j
    let P := f ⁻¹ᵁ O i ⊓ f ⁻¹ᵁ O j
    let κ := {k : ι // ∃ (hki : O k ≤ O i) (hkj : O k ≤ O j),
      Y.homOfLE (f.preimage_mono hki) ≫ φ i = φ k ∧ Y.homOfLE (f.preimage_mono hkj) ≫ φ j = φ k}
    let Q : κ → P.toScheme.Opens := fun k => P.ι ⁻¹ᵁ f ⁻¹ᵁ O k.1
    have hQ : IsOpenCover Q := by
      refine eq_top_iff.2 fun p _ => ?_
      obtain ⟨k, hki, hkj, hk, h1, h2⟩ := hcompat i j (f (P.ι p)) ⟨p.2.1, p.2.2⟩
      exact Opens.mem_iSup.2 ⟨⟨k, hki, hkj, h1, h2⟩, hk⟩
    refine (P.toScheme.openCoverOfIsOpenCover Q hQ).hom_ext _ _ fun k => ?_
    obtain ⟨hki, hkj, h1, h2⟩ := k.2
    change (Q k).ι ≫ _ = (Q k).ι ≫ _
    have e1 : (Q k).ι ≫ Y.homOfLE (inf_le_left : P ≤ f ⁻¹ᵁ O i) =
        (P.ι ∣_ (f ⁻¹ᵁ O k.1)) ≫ Y.homOfLE (f.preimage_mono hki) := by
      rw [← cancel_mono (f ⁻¹ᵁ O i).ι]
      simp [morphismRestrict_ι]
      rfl
    have e2 : (Q k).ι ≫ Y.homOfLE (inf_le_right : P ≤ f ⁻¹ᵁ O j) =
        (P.ι ∣_ (f ⁻¹ᵁ O k.1)) ≫ Y.homOfLE (f.preimage_mono hkj) := by
      rw [← cancel_mono (f ⁻¹ᵁ O j).ι]
      simp [morphismRestrict_ι]
      rfl
    rw [reassoc_of% e1, reassoc_of% e2, h1, h2]
  let Φ := glueOpens (fun i => f ⁻¹ᵁ O i) hU φ hg
  have hΦ : ∀ i, (f ⁻¹ᵁ O i).ι ≫ Φ = φ i := ι_glueOpens _ hU φ hg
  have hΦg : Φ ≫ g = f := by
    refine (Y.openCoverOfIsOpenCover _ hU).hom_ext _ _ fun i => ?_
    change (f ⁻¹ᵁ O i).ι ≫ _ = (f ⁻¹ᵁ O i).ι ≫ _
    rw [reassoc_of% hΦ i]
    exact hover i
  have hiso : IsIso Φ := by
    have hZ' : ⨆ i, g ⁻¹ᵁ O i = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      obtain ⟨i, hi⟩ := hZ z
      exact Opens.mem_iSup.2 ⟨i, hi⟩
    rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _ hZ']
    intro i
    have hpre : Φ ⁻¹ᵁ g ⁻¹ᵁ O i = f ⁻¹ᵁ O i := by
      rw [← Scheme.Hom.comp_preimage, hΦg]
    let e := IsOpenImmersion.isoOfRangeEq (f ⁻¹ᵁ O i).ι (Φ ⁻¹ᵁ g ⁻¹ᵁ O i).ι
      (by rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, hpre])
    let e' := IsOpenImmersion.isoOfRangeEq (φ i) (g ⁻¹ᵁ O i).ι (by
      rw [Scheme.Opens.range_ι]
      refine (Scheme.Hom.coe_opensRange _).symm.trans (Set.Subset.antisymm ?_ (hrange i))
      rintro _ ⟨y, rfl⟩
      change g (φ i y) ∈ O i
      rw [← Scheme.Hom.comp_apply, hover, Scheme.Hom.comp_apply]
      exact y.2)
    have key : e.hom ≫ Φ ∣_ (g ⁻¹ᵁ O i) = e'.hom := by
      rw [← cancel_mono (g ⁻¹ᵁ O i).ι, Category.assoc, morphismRestrict_ι,
        IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, hΦ, IsOpenImmersion.isoOfRangeEq_hom_fac]
    have : Φ ∣_ (g ⁻¹ᵁ O i) = e.inv ≫ e'.hom := by
      rw [← key, Iso.inv_hom_id_assoc]
    rw [MorphismProperty.isomorphisms.iff, this]
    infer_instance
  exact ⟨asIso Φ, hΦg, hΦ⟩

end GlueIso

namespace ProjTwistMap

open HomogeneousIdeal

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **Restricting degree-one sections.** For a graded `φ : S → T` whose `Proj` map is an open
immersion, the morphism `𝒪_{Proj S}(1)|_{Proj T} ⟶ 𝒪_{Proj T}(1)` sends the global section `s` of
`𝒪_{Proj S}(1)` given by `s ∈ S_1` to the global section `φ(s)` of `𝒪_{Proj T}(1)`. -/
theorem twistRestrictHom_app_degreeOneSection (φ : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map φ)
    [IsOpenImmersion (Proj.map φ hf)] {s : A} (hs : s ∈ 𝒜 1) :
    (twistRestrictHom φ hf 1).app ⊤
        ((projTwistingSheaf 𝒜 1).presheaf.map (homOfLE le_top).op
          (ProjTwistingSheaf.degreeOneSection ⟨s, hs⟩)) =
      ProjTwistingSheaf.degreeOneSection ⟨φ s, φ.map_mem hs⟩ := by
  apply Subtype.ext
  funext y
  rw [twistRestrictHom_app_apply]
  change twistFiber φ 1 _ (ProjTwistingSheaf.degreeOneFraction _ hs) =
    ProjTwistingSheaf.degreeOneFraction y.1 (φ.map_mem hs)
  rw [ProjTwistingSheaf.degreeOneFraction, twistFiber_mk]
  simp only [map_one]
  rfl

end ProjTwistMap

end Hartshorne

namespace AlgebraicGeometry.Scheme.Modules

open Hartshorne Hartshorne.SheafAlgebraOperations Hartshorne.ModuleSheafAlgebra HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {E : X.Modules} (hE : E.IsLocallyFree)
  (hfin : ∀ x, E.rankAt x < Cardinal.aleph0)

/-- An affine open as an object of the affine Zariski site. -/
private abbrev siteOf {V : X.Opens} (hV : IsAffineOpen V) : X.AffineZariskiSite := ⟨V, hV⟩

/-- The coordinates of a frame `e` over an affine open `V`, as the graded homomorphism
`ℤ[z₀, …, zₙ] → Γ(V, S(E))`, `z_k ↦ e_k`. -/
def frameIntHom {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (e : ULift.{u} (Fin (n + 1)) → Γ(E, V)) :
    GeneratedProj.intGrading.{u} n →+*ᵍ (symmetricGradedAlgebra hE hfin).grading (siteOf hV) :=
  (frameGradedHom hE hfin hV e).comp (projectiveSpaceComparisonHom Γ(X, V) n (Equiv.refl _))

lemma frameIntHom_X {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (e : ULift.{u} (Fin (n + 1)) → Γ(E, V)) (k : Fin (n + 1)) :
    frameIntHom hE hfin hV e (MvPolynomial.X k) = E.symDegreeOne V (e (ULift.up k)) := by
  change frameGradedHom hE hfin hV e (projectiveSpaceComparisonHom Γ(X, V) n (Equiv.refl _)
    (MvPolynomial.X k)) = _
  rw [projectiveSpaceComparisonHom_X, frameGradedHom_apply, MvPolynomial.rename_X,
    chartRingHom_X]
  rfl

/-- Followed by the projection to `ℙⁿ_ℤ`, the identification `π⁻¹(V) ≅ ℙⁿ_V` is the morphism
`π⁻¹(V) ≅ Proj Γ(V, S(E)) ⟶ ℙⁿ_ℤ` given by `z_k ↦ e_k`. -/
lemma projectiveBundleFrameIso_hom_fst [IsNoetherian X] {V : X.Opens}
    (hV : IsAffineOpen V) {n : ℕ} {e : ULift.{u} (Fin (n + 1)) → Γ(E, V)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) E V e) :
    ∃ h, (projectiveBundleFrameIso hE hfin hV he).hom ≫ pullback.fst _ _ =
      ((symmetricGradedAlgebra hE hfin).restrictIso (siteOf hV)).hom ≫
        Proj.map (frameIntHom hE hfin hV e) h := by
  exact ⟨_, by
    change (((symmetricGradedAlgebra hE hfin).restrictIso (siteOf hV)).hom ≫
      (projIsoOfBijective _ (frameGradedHom_bijective hE hfin hV he)).hom ≫
        projToProjectiveSpaceOverSpec Γ(X, V) n (Equiv.refl _) ≫
          projectiveSpaceOverSchemeMap n hV.isoSpec.inv) ≫ pullback.fst _ _ = _
    simp only [Category.assoc, projectiveSpaceOverSchemeMap_fst,
      projToProjectiveSpaceOverSpec_fst]
    rw [projIsoOfBijective_hom, projToProjectiveSpaceInt, GeneratedProj.toProjectiveSpaceInt,
      ← Proj.map_comp]
    rfl⟩

private lemma projMap_congr {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜]
    [GradedRing ℬ] {f f' : 𝒜 →+*ᵍ ℬ} (h : ∀ x, f x = f' x) (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hf' : ℬ₊ ≤ 𝒜₊.map f') : Proj.map f hf = Proj.map f' hf' := by
  obtain rfl : f = f' := GradedRingHom.ext h
  rfl

/-- **Naturality along a basic open**: for a basic open `W = D(s)` of an affine open `V` and frames
`e` over `V`, `e'` over `W` with `e' = e|_W`, the morphisms `π⁻¹(W) ⟶ ℙⁿ_ℤ` given by `z_k ↦ e'_k`
and `z_k ↦ e_k` agree on `π⁻¹(W)`. -/
private lemma projectiveBundleFrameIso_fst_naturality [IsNoetherian X] {V W : X.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) {s : Γ(X, V)} (hWs : W = X.basicOpen s) {n : ℕ}
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, V)} {e' : ULift.{u} (Fin (n + 1)) → Γ(E, W)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) E V e)
    (he' : Ringed.IsLocalFrame (R := X.sheaf) E W e')
    (hres : ∀ k, E.presheaf.map (homOfLE (hWs.trans_le (X.basicOpen_le s))).op (e k) = e' k) :
    (projectiveBundle hE hfin).homOfLE (Scheme.Hom.preimage_mono _
        (hWs.trans_le (X.basicOpen_le s))) ≫
      (projectiveBundleFrameIso hE hfin hV he).hom ≫ pullback.fst _ _ =
    (projectiveBundleFrameIso hE hfin hW he').hom ≫ pullback.fst _ _ := by
  subst hWs
  let S := symmetricGradedAlgebra hE hfin
  let a : (siteOf hV).basicOpen s ⟶ (siteOf hV) :=
    homOfLE ((siteOf hV).basicOpen_le s)
  obtain ⟨h1, eq1⟩ := projectiveBundleFrameIso_hom_fst hE hfin hV he
  obtain ⟨h2, eq2⟩ := projectiveBundleFrameIso_hom_fst hE hfin hW he'
  rw [eq1, eq2]
  have hA : Proj.map (S.restrict a) (S.irrelevant_le a) ≫ S.projι (siteOf hV) =
      S.projι ((siteOf hV).basicOpen s) :=
    colimit.w S.relativeGluingData.functor a
  have hB : (projectiveBundle hE hfin).homOfLE (Scheme.Hom.preimage_mono _
        (X.basicOpen_le s)) ≫ (S.restrictIso (siteOf hV)).hom =
      (S.restrictIso (siteOf hW)).hom ≫ Proj.map (S.restrict a) (S.irrelevant_le a) := by
    rw [← cancel_mono (S.projι (siteOf hV)), Category.assoc, Category.assoc, hA,
      S.restrictIso_hom_projι]
    exact (Scheme.homOfLE_ι _ _).trans (S.restrictIso_hom_projι (siteOf hW)).symm
  rw [reassoc_of% hB, ← Proj.map_comp]
  congr 1
  refine projMap_congr (fun x => ?_) _ _
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (f := (S.restrict a).toRingHom.comp
    (frameIntHom hE hfin hV e).toRingHom) (g := (frameIntHom hE hfin hW e').toRingHom)
    (fun r => ?_) (fun k => ?_)) x
  · obtain ⟨m⟩ := r
    have hC : (MvPolynomial.C (⟨m⟩ : ULift.{u} ℤ) : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) =
        (m : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) := by
      rw [← map_intCast (MvPolynomial.C (σ := Fin (n + 1)) (R := ULift.{u} ℤ)) m]
      rfl
    rw [hC, map_intCast, map_intCast]
  · change S.restrict a (frameIntHom hE hfin hV e (MvPolynomial.X k)) =
      frameIntHom hE hfin hW e' (MvPolynomial.X k)
    rw [frameIntHom_X, frameIntHom_X, S.restrict_apply, ← hres]
    exact E.symDegreeOne_naturality _ _

/-- Base change of an open immersion `Y' ⟶ Y` is an open immersion `ℙⁿ_{Y'} ⟶ ℙⁿ_Y`. -/
private instance isOpenImmersion_projectiveSpaceOverSchemeMap (n : ℕ) {Y Y' : Scheme.{u}}
    (j : Y' ⟶ Y) [IsOpenImmersion j] : IsOpenImmersion (projectiveSpaceOverSchemeMap n j) :=
  MorphismProperty.of_isPullback (projectiveSpaceOverSchemeMap_isPullback n j).flip inferInstance

/-- The affine opens contained in `U`. -/
private abbrev AffineIn (U : X.Opens) : Type u := {V : X.Opens // IsAffineOpen V ∧ V ≤ U}

variable [IsNoetherian X]

/-- The identification over an affine open `V ⊆ U`, with the frame restricted from `U`, as a
morphism from the part of `π⁻¹(U)` over `V` to `ℙⁿ_U`. -/
private def framePiece {U : X.Opens} {n : ℕ} {e : ULift.{u} (Fin (n + 1)) → Γ(E, U)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) E U e) (V : AffineIn U) :
    ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⁻¹ᵁ projectiveBundleProj hE hfin ⁻¹ᵁ V.1).toScheme ⟶
      projectiveSpaceOverScheme n U :=
  (Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin) V.2.2)).hom ≫
    (projectiveBundleFrameIso hE hfin V.2.1 (he.restrictLE V.2.2)).hom ≫
      projectiveSpaceOverSchemeMap n (X.homOfLE V.2.2)

private instance {U : X.Opens} {n : ℕ} {e : ULift.{u} (Fin (n + 1)) → Γ(E, U)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) E U e) (V : AffineIn U) :
    IsOpenImmersion (framePiece hE hfin he V) := by
  unfold framePiece
  infer_instance

private lemma framePiece_over {U : X.Opens} {n : ℕ} {e : ULift.{u} (Fin (n + 1)) → Γ(E, U)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) E U e) (V : AffineIn U) :
    framePiece hE hfin he V ≫ projectiveSpaceOverSchemeProjection n U ≫ U.ι =
      ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⁻¹ᵁ projectiveBundleProj hE hfin ⁻¹ᵁ V.1).ι ≫
        (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ≫ projectiveBundleProj hE hfin := by
  simp only [framePiece, Category.assoc, projectiveSpaceOverSchemeMap_projection_assoc,
    Scheme.homOfLE_ι]
  rw [reassoc_of% (projectiveBundleFrameIso_hom_projection hE hfin V.2.1 (he.restrictLE V.2.2)),
    morphismRestrict_ι, Scheme.Opens.isoOfLE_hom_ι_assoc]

private lemma framePiece_range {U : X.Opens} {n : ℕ} {e : ULift.{u} (Fin (n + 1)) → Γ(E, U)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) E U e) (V : AffineIn U) :
    (projectiveSpaceOverSchemeProjection n U ≫ U.ι) ⁻¹ᵁ V.1 ≤
      (framePiece hE hfin he V).opensRange := by
  intro z hz
  let j := X.homOfLE V.2.2
  have hpb := projectiveSpaceOverSchemeMap_isPullback n j
  have h1 : projectiveSpaceOverSchemeProjection n U z ∈ j.opensRange := by
    rw [Scheme.opensRange_homOfLE]
    exact hz
  have h2 : z ∈ Set.range (pullback.fst (projectiveSpaceOverSchemeProjection n U) j) := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact h1
  obtain ⟨w, rfl⟩ := h2
  let I := Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin) V.2.2)
  let ψ := projectiveBundleFrameIso hE hfin V.2.1 (he.restrictLE V.2.2)
  have hfac : framePiece hE hfin he V =
      (I.hom ≫ ψ.hom ≫ hpb.isoPullback.hom) ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, hpb.isoPullback_hom_fst]
    rfl
  have key : (hpb.isoPullback.inv ≫ ψ.inv ≫ I.inv) ≫ framePiece hE hfin he V =
      pullback.fst _ _ := by
    rw [hfac]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ⟨(hpb.isoPullback.inv ≫ ψ.inv ≫ I.inv) w, by rw [← Scheme.Hom.comp_apply, key]⟩

private lemma framePiece_naturality {U : X.Opens} {n : ℕ}
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, U)} (he : Ringed.IsLocalFrame (R := X.sheaf) E U e)
    (V W : AffineIn U) {s : Γ(X, V.1)} (hWs : W.1 = X.basicOpen s) :
    (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme.homOfLE
        (Scheme.Hom.preimage_mono ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ≫
          projectiveBundleProj hE hfin) (hWs.trans_le (X.basicOpen_le s))) ≫
      framePiece hE hfin he V = framePiece hE hfin he W := by
  apply pullback.hom_ext
  · simp only [framePiece, Category.assoc, projectiveSpaceOverSchemeMap_fst]
    have hI : (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme.homOfLE
          (Scheme.Hom.preimage_mono ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ≫
            projectiveBundleProj hE hfin) (hWs.trans_le (X.basicOpen_le s))) ≫
          (Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin)
            V.2.2)).hom =
        (Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin)
            W.2.2)).hom ≫ (projectiveBundle hE hfin).homOfLE
          (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin)
            (hWs.trans_le (X.basicOpen_le s))) := by
      rw [← cancel_mono (projectiveBundleProj hE hfin ⁻¹ᵁ V.1).ι]
      simp [Scheme.Opens.isoOfLE_hom_ι]
    rw [reassoc_of% hI, projectiveBundleFrameIso_fst_naturality hE hfin V.2.1 W.2.1 hWs
      (he.restrictLE V.2.2) (he.restrictLE W.2.2)]
    intro k
    change (E.val.presheaf.map (homOfLE V.2.2).op ≫ E.val.presheaf.map (homOfLE _).op) (e k) = _
    rw [← Functor.map_comp]
    rfl
  · rw [← cancel_mono U.ι]
    simp only [Category.assoc]
    rw [framePiece_over, framePiece_over]
    exact Scheme.homOfLE_ι_assoc _ _ _

/-- **`P(E)` over an open on which `E` has a frame** (Hartshorne II.7, p. 162): a frame `e` of `E`
of rank `n + 1` over an arbitrary open `U ⊆ X` gives an isomorphism `π⁻¹(U) ≅ ℙⁿ_U` over `U`. Over
every affine open `V ⊆ U` it restricts to the identification `π⁻¹(V) ≅ ℙⁿ_V` of the frame `e|_V`
(`projectiveBundleFrameIso`), followed by `ℙⁿ_V ⊆ ℙⁿ_U`. -/
theorem exists_projectiveBundleIso_of_frame {U : X.Opens} {n : ℕ}
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, U)} (he : Ringed.IsLocalFrame (R := X.sheaf) E U e) :
    ∃ ψ : (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme ≅ projectiveSpaceOverScheme n U,
      ψ.hom ≫ projectiveSpaceOverSchemeProjection n U = projectiveBundleProj hE hfin ∣_ U ∧
      ∀ (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U),
        ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⁻¹ᵁ projectiveBundleProj hE hfin ⁻¹ᵁ V).ι ≫
            ψ.hom =
          (Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin)
              hVU)).hom ≫
            (projectiveBundleFrameIso hE hfin hV (he.restrictLE hVU)).hom ≫
              projectiveSpaceOverSchemeMap n (X.homOfLE hVU) := by
  obtain ⟨Φ, hΦg, hΦ⟩ := exists_iso_of_openImmersions_over
    ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ≫ projectiveBundleProj hE hfin)
    (projectiveSpaceOverSchemeProjection n U ≫ U.ι) (fun V : AffineIn U => V.1)
    (framePiece hE hfin he) (framePiece_over hE hfin he) (framePiece_range hE hfin he)
    (fun y => by
      obtain ⟨V, hV, hyV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (show projectiveBundleProj hE hfin y.1 ∈ U from y.2)
      exact ⟨⟨V, hV, hVU⟩, hyV⟩)
    (fun z => by
      obtain ⟨V, hV, hzV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (show U.ι (projectiveSpaceOverSchemeProjection n U z) ∈ U from
          (projectiveSpaceOverSchemeProjection n U z).2)
      exact ⟨⟨V, hV, hVU⟩, hzV⟩)
    (fun i j b hb => by
      obtain ⟨r, t, hrt, hbr⟩ := exists_basicOpen_le_affine_inter i.2.1 j.2.1 b hb
      let k : AffineIn U := ⟨X.basicOpen r, i.2.1.basicOpen r, (X.basicOpen_le r).trans i.2.2⟩
      exact ⟨k, X.basicOpen_le r, hrt.trans_le (X.basicOpen_le t), hbr,
        framePiece_naturality hE hfin he i k rfl, framePiece_naturality hE hfin he j k hrt⟩)
  refine ⟨Φ, ?_, fun V hV hVU => hΦ ⟨V, hV, hVU⟩⟩
  rw [← cancel_mono U.ι, Category.assoc, hΦg, morphismRestrict_ι]

/-- **`P(E)` over an open on which `E` is free** (Hartshorne II.7, p. 162): if
`E|_U ≅ 𝒪_U^{n+1}` on an open `U ⊆ X`, then `π⁻¹(U) ≅ ℙⁿ_U` over `U`. -/
theorem nonempty_projectiveBundle_iso_of_restrict_iso_free_open {U : X.Opens} {n : ℕ}
    (α : E.restrict U.ι ≅ SheafOfModules.free (ULift.{u} (Fin (n + 1)))) :
    ∃ ψ : (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme ≅ projectiveSpaceOverScheme n U,
      ψ.hom ≫ projectiveSpaceOverSchemeProjection n U = projectiveBundleProj hE hfin ∣_ U := by
  obtain ⟨β⟩ := (nonempty_restrict_iso_free_iff E U _).mp ⟨α⟩
  obtain ⟨ψ, hψ, -⟩ := exists_projectiveBundleIso_of_frame hE hfin
    (Ringed.isLocalFrame_of_over_iso (R := X.sheaf) β)
  exact ⟨ψ, hψ⟩

end AlgebraicGeometry.Scheme.Modules
