/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveBundleGluing

/-!
# The twisting sheaf of a projective bundle over an open where the module is free

Hartshorne, *Algebraic Geometry*, II.7, p. 162.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

open AlgebraicGeometry

/-- A trivializing section of the restriction `M|_Z` of `M` along an open immersion `f : Z ⟶ Y`
over `W` is a trivializing section of `M` over `f(W)`. -/
theorem IsTrivializingSection.image_of_restrict {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [IsOpenImmersion f] {M : Y.Modules} {W : Z.Opens} {t : Γ(M, f ''ᵁ W)}
    (ht : IsTrivializingSection (M.restrict f) W t) : IsTrivializingSection M (f ''ᵁ W) t := by
  have key : ∀ {V₁ V₂ : Y.Opens} (_ : V₁ = V₂) (h₁ : V₁ ≤ f ''ᵁ W) (h₂ : V₂ ≤ f ''ᵁ W),
      Function.Bijective (fun a : Γ(Y, V₁) => a • M.presheaf.map (homOfLE h₁).op t) →
      Function.Bijective (fun a : Γ(Y, V₂) => a • M.presheaf.map (homOfLE h₂).op t) := by
    rintro _ _ rfl _ _ h
    exact h
  intro V hV
  have hle : f ⁻¹ᵁ V ≤ W := (f.preimage_mono hV).trans (f.preimage_image_eq W).le
  have heq : f ''ᵁ f ⁻¹ᵁ V = V := by
    rw [f.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.2 (hV.trans (f.image_le_opensRange W))
  refine key heq (f.image_mono hle) hV ?_
  have h := ht (f ⁻¹ᵁ V) hle
  have hfun : (fun a : Γ(Z, f ⁻¹ᵁ V) => a • (M.restrict f).presheaf.map (homOfLE hle).op t) =
      (fun a : Γ(Y, f ''ᵁ f ⁻¹ᵁ V) => a • M.presheaf.map (homOfLE (f.image_mono hle)).op t) ∘
        (f.appIso (f ⁻¹ᵁ V)).inv := rfl
  rw [hfun] at h
  exact (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso _)).mp h

/-- Naturality of an isomorphism out of a restriction, on sections over the image of `⊤`. -/
theorem restrict_iso_hom_app_map {Z Y : Scheme.{u}} (f : Z ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} {N : Z.Modules} (α : M.restrict f ≅ N) (W : Z.Opens) (x : Γ(M, f ''ᵁ ⊤)) :
    α.hom.app W (M.presheaf.map (homOfLE (f.image_mono (le_top : W ≤ ⊤))).op x) =
      N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (α.hom.app ⊤ x) :=
  hom_app_map α.hom (le_top : W ≤ ⊤) x

/-- The compatibility `DirectedModuleGluing.DataTr.ψ_compat` of the gluing isomorphisms with the
transition isomorphisms, on sections over the image of `⊤`. -/
theorem DirectedModuleGluing.DataTr.ψ_hom_app_top {Y : Scheme.{u}}
    {𝒰 : Scheme.OpenCover.{u} Y} [Category.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] [𝒰.LocallyDirected]
    (E : DirectedModuleGluing.DataTr 𝒰) {i j : 𝒰.I₀} (f : i ⟶ j) (h : E.tr f ≫ 𝒰.f j = 𝒰.f i)
    (hle : 𝒰.f j ''ᵁ (E.tr f ''ᵁ ⊤) ≤ 𝒰.f i ''ᵁ ⊤) (x : Γ(E.glue, 𝒰.f i ''ᵁ ⊤)) :
    (E.ψ i).hom.app ⊤ x = (E.θ f).hom.app ⊤ ((E.ψ j).hom.app (E.tr f ''ᵁ ⊤)
      (E.glue.presheaf.map (homOfLE hle).op x)) := by
  rw [← E.ψ_compat f h]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  exact congrArg (fun y => (E.θ f).hom.app ⊤ ((E.ψ j).hom.app (E.tr f ''ᵁ ⊤) y))
    (DirectedModuleGluing.pmap_map E.glue _ _ _ x)

end Hartshorne

namespace AlgebraicGeometry.Scheme.Modules

open Hartshorne Hartshorne.SheafAlgebraOperations Hartshorne.ModuleSheafAlgebra HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {E : X.Modules} (hE : E.IsLocallyFree)
  (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) [IsNoetherian X]

/-- An affine open as an object of the affine Zariski site. -/
private abbrev site {V : X.Opens} (hV : IsAffineOpen V) : X.AffineZariskiSite := ⟨V, hV⟩

/-- The affine piece `Proj Γ(V, S(E))` over an affine open `V ⊆ U`, as an open subscheme of
`π⁻¹(U)`. -/
private def pieceι {U V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) :
    Proj ((symmetricGradedAlgebra hE hfin).grading (site hV)) ⟶
      (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme :=
  ((symmetricGradedAlgebra hE hfin).restrictIso (site hV)).inv ≫
    (Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin) hVU)).inv ≫
      ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⁻¹ᵁ projectiveBundleProj hE hfin ⁻¹ᵁ V).ι

private instance {U V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) :
    IsOpenImmersion (pieceι hE hfin hV hVU) := by
  unfold pieceι
  infer_instance

private lemma pieceι_ι {U V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) :
    pieceι hE hfin hV hVU ≫ (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι =
      (symmetricGradedAlgebra hE hfin).projι (site hV) := by
  rw [pieceι, Category.assoc, Category.assoc,
    ← Scheme.Opens.isoOfLE_hom_ι (Scheme.Hom.preimage_mono _ hVU), Iso.inv_hom_id_assoc,
    Iso.inv_comp_eq]
  exact ((symmetricGradedAlgebra hE hfin).restrictIso_hom_projι (site hV)).symm

variable {U : X.Opens} {n : ℕ} {e : ULift.{u} (Fin (n + 1)) → Γ(E, U)}
  (he : Ringed.IsLocalFrame (R := X.sheaf) E U e)
  (ψ : (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme ≅ projectiveSpaceOverScheme n U)
  (hψ : ∀ (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U),
        ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⁻¹ᵁ projectiveBundleProj hE hfin ⁻¹ᵁ V).ι ≫
            ψ.hom =
          (Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin)
              hVU)).hom ≫
            (projectiveBundleFrameIso hE hfin hV (he.restrictLE hVU)).hom ≫
              projectiveSpaceOverSchemeMap n (X.homOfLE hVU))

include hψ in
/-- On the affine piece over `V`, the morphism `π⁻¹(U) ≅ ℙⁿ_U ⟶ ℙⁿ_ℤ` is
`Proj Γ(V, S(E)) ⟶ Proj ℤ[z₀, …, zₙ]`, `z_k ↦ e_k`. -/
private lemma pieceι_toIntMap {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) :
    ∃ h, pieceι hE hfin hV hVU ≫ toIntMap ψ.hom =
      Proj.map (frameIntHom hE hfin hV (fun k => E.presheaf.map (homOfLE hVU).op (e k))) h := by
  obtain ⟨h, hh⟩ := projectiveBundleFrameIso_hom_fst hE hfin hV (he.restrictLE hVU)
  refine ⟨h, ?_⟩
  rw [pieceι, Category.assoc, Category.assoc, toIntMap, reassoc_of% (hψ V hV hVU),
    Iso.inv_hom_id_assoc, projectiveSpaceOverSchemeMap_fst, hh,
    Iso.inv_hom_id_assoc]
  rfl

/-- The degree-one element `e_i ∈ Γ(V, S(E))` given by the restricted frame. -/
private abbrev pieceElt {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) (i : Fin (n + 1)) :
    (symmetricGradedAlgebra hE hfin).obj.obj (op (site hV)) :=
  frameIntHom hE hfin hV (fun k => E.presheaf.map (homOfLE hVU).op (e k)) (MvPolynomial.X i)

omit [IsNoetherian X] in
private lemma pieceElt_mem {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) (i : Fin (n + 1)) :
    pieceElt hE hfin (e := e) hV hVU i ∈ (symmetricGradedAlgebra hE hfin).grading (site hV) 1 :=
  (frameIntHom hE hfin hV _).map_mem (Hartshorne.X_mem_homogeneousSubmodule_one _ i)

include hψ in
/-- On the affine piece over `V`, the preimage of the chart `D₊(z_i)` under `π⁻¹(U) ≅ ℙⁿ_U` is
`D₊(e_i)`. -/
private lemma pieceι_preimage_chart {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (i : Fin (n + 1)) :
    pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i =
      Proj.basicOpen _ (pieceElt hE hfin (e := e) hV hVU i) := by
  obtain ⟨h, hh⟩ := pieceι_toIntMap hE hfin he ψ hψ hV hVU
  rw [chartPreimage, ← Scheme.Hom.comp_preimage, hh, Proj.map_preimage_basicOpen]

include hψ in
/-- On the affine piece over `V`, the isomorphism `π⁻¹(U) ≅ ℙⁿ_U` pulls `z_j/z_i` back to
`e_j/e_i`. -/
private lemma pieceι_appLE_ratio {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (i j : Fin (n + 1)) :
    (pieceι hE hfin hV hVU).appLE (chartPreimage ψ.hom i)
        (Proj.basicOpen _ (pieceElt hE hfin (e := e) hV hVU i))
        (pieceι_preimage_chart hE hfin he ψ hψ hV hVU i).ge
        ((toIntMap ψ.hom).app (chartInt n i) (ratioInt n i j)) =
      Proj.awayToSection _ (pieceElt hE hfin (e := e) hV hVU i)
        (HomogeneousLocalization.Away.mk _ (pieceElt_mem hE hfin hV hVU i) 1
          (pieceElt hE hfin (e := e) hV hVU j)
          (by simpa using pieceElt_mem hE hfin hV hVU j)) := by
  obtain ⟨h, hh⟩ := pieceι_toIntMap hE hfin he ψ hψ hV hVU
  have h1 := ConcreteCategory.congr_hom (Scheme.Hom.comp_appLE (pieceι hE hfin hV hVU)
    (toIntMap ψ.hom) (chartInt n i) _ (pieceι_preimage_chart hE hfin he ψ hψ hV hVU i).ge)
    (ratioInt n i j)
  simp only [CommRingCat.comp_apply] at h1
  rw [← h1]
  have key : ∀ (φ : Proj ((symmetricGradedAlgebra hE hfin).grading (site hV)) ⟶ projInt.{u} n)
      (_ : φ = Proj.map _ h) (e₁), φ.appLE (chartInt n i)
        (Proj.basicOpen _ (pieceElt hE hfin (e := e) hV hVU i)) e₁ (ratioInt n i j) =
      Proj.awayToSection _ (pieceElt hE hfin (e := e) hV hVU i)
        (HomogeneousLocalization.Away.mk _ (pieceElt_mem hE hfin hV hVU i) 1
          (pieceElt hE hfin (e := e) hV hVU j)
          (by simpa using pieceElt_mem hE hfin hV hVU j)) := by
    rintro _ rfl e₁
    have h2 := ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE
      (frameIntHom hE hfin hV (fun k => E.presheaf.map (homOfLE hVU).op (e k))) h
      (Hartshorne.X_mem_homogeneousSubmodule_one _ i)) (chartRatio (ULift.{u} ℤ) i j)
    refine h2.trans ?_
    simp only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom, chartRatio,
      HomogeneousLocalization.Away.map_mk]
  exact key _ hh _

omit [IsNoetherian X] in
private lemma iso_hom_inv_app {Z : Scheme.{u}} {M N : Z.Modules} (α : M ≅ N) (W : Z.Opens)
    (x : Γ(N, W)) : α.hom.app W (α.inv.app W x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, α.inv_hom_id,
    Scheme.Modules.Hom.id_app]
  rfl

/-- The arrow `D(r) ⟶ V` of the affine Zariski site. -/
private abbrev basicArrow {V : X.Opens} (hV : IsAffineOpen V) (r : Γ(X, V)) :
    site (hV.basicOpen r) ⟶ site hV :=
  homOfLE ⟨r, rfl⟩

omit [IsNoetherian X] in
private lemma pieceElt_restrict {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (r : Γ(X, V)) (i : Fin (n + 1)) :
    (symmetricGradedAlgebra hE hfin).restrict (basicArrow hV r)
        (pieceElt hE hfin (e := e) hV hVU i) =
      pieceElt hE hfin (e := e) (hV.basicOpen r) ((X.basicOpen_le r).trans hVU) i := by
  unfold pieceElt
  rw [frameIntHom_X, frameIntHom_X, (symmetricGradedAlgebra hE hfin).restrict_apply]
  refine (E.symDegreeOne_naturality _ _).trans ?_
  congr 1
  change (E.val.presheaf.map _ ≫ E.val.presheaf.map _) (e _) = _
  rw [← Functor.map_comp]
  rfl


/-! ### Sections of a module glued from the twisting sheaves of the affine pieces

To keep the kernel away from the construction of `𝒪_{P(E)}(1)`, the following is stated for any
module `M` on `P(E)` with isomorphisms `α V : M|_{Proj Γ(V, S(E))} ≅ 𝒪_{Proj Γ(V, S(E))}(1)`
compatible with the transition maps along basic opens. -/

section Abstract

variable (M : (projectiveBundle hE hfin).Modules)
  (α : ∀ V : X.AffineZariskiSite, M.restrict ((symmetricGradedAlgebra hE hfin).projι V) ≅
    (symmetricGradedAlgebra hE hfin).twistingSheaf 1 V)

/-- The degree-one section `e_i` of `𝒪_{Proj Γ(V, S(E))}(1)`, as a section of `M` over the affine
piece over `V`. -/
private def pieceSection {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) (i : Fin (n + 1)) :
    Γ(M.restrict ((symmetricGradedAlgebra hE hfin).projι (site hV)), ⊤) :=
  (α (site hV)).inv.app ⊤
    (ProjTwistingSheaf.degreeOneSection ⟨pieceElt hE hfin (e := e) hV hVU i,
      pieceElt_mem hE hfin hV hVU i⟩)

private lemma pieceSection_hom {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (i : Fin (n + 1)) :
    (α (site hV)).hom.app ⊤ (pieceSection hE hfin (e := e) M α hV hVU i) =
      ProjTwistingSheaf.degreeOneSection ⟨pieceElt hE hfin (e := e) hV hVU i,
        pieceElt_mem hE hfin hV hVU i⟩ :=
  iso_hom_inv_app _ _ _

private lemma pieceSection_spec {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (i : Fin (n + 1)) (W : (Proj ((symmetricGradedAlgebra hE hfin).grading (site hV))).Opens) :
    (α (site hV)).hom.app W (M.presheaf.map
          (homOfLE (Scheme.Hom.image_mono _ (le_top : W ≤ ⊤))).op
          (pieceSection hE hfin (e := e) M α hV hVU i)) =
      (projTwistingSheaf ((symmetricGradedAlgebra hE hfin).grading (site hV)) 1).presheaf.map
        (homOfLE (le_top : W ≤ ⊤)).op
        (ProjTwistingSheaf.degreeOneSection ⟨pieceElt hE hfin (e := e) hV hVU i,
          pieceElt_mem hE hfin hV hVU i⟩) := by
  rw [Hartshorne.restrict_iso_hom_app_map, pieceSection_hom]

omit [IsNoetherian X] in
private lemma projι_image_basicArrow {V : X.Opens} (hV : IsAffineOpen V) (r : Γ(X, V)) :
    (symmetricGradedAlgebra hE hfin).projι (site hV) ''ᵁ
        (Proj.map ((symmetricGradedAlgebra hE hfin).restrict (basicArrow hV r))
          ((symmetricGradedAlgebra hE hfin).irrelevant_le (basicArrow hV r)) ''ᵁ ⊤) ≤
      (symmetricGradedAlgebra hE hfin).projι (site (hV.basicOpen r)) ''ᵁ ⊤ := by
  have hA : Proj.map ((symmetricGradedAlgebra hE hfin).restrict (basicArrow hV r))
      ((symmetricGradedAlgebra hE hfin).irrelevant_le (basicArrow hV r)) ≫
        (symmetricGradedAlgebra hE hfin).projι (site hV) =
      (symmetricGradedAlgebra hE hfin).projι (site (hV.basicOpen r)) :=
    colimit.w (symmetricGradedAlgebra hE hfin).relativeGluingData.functor (basicArrow hV r)
  rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
  exact ⟨y, trivial, by rw [← hA]; rfl⟩

variable (hα : ∀ {V : X.Opens} (hV : IsAffineOpen V) (r : Γ(X, V))
    (x : Γ(M, (symmetricGradedAlgebra hE hfin).projι (site (hV.basicOpen r)) ''ᵁ ⊤)),
    (α (site (hV.basicOpen r))).hom.app ⊤ x =
      ((symmetricGradedAlgebra hE hfin).twistTransition 1 (basicArrow hV r)).hom.app ⊤
        ((α (site hV)).hom.app _
          (M.presheaf.map (homOfLE (projι_image_basicArrow hE hfin hV r)).op x)))

include hα in
/-- Restricting the section `e_i` over `V` to a basic open `D(r) ⊆ V` gives the section `e_i`
over `D(r)`. -/
private lemma pieceSection_basicOpen {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (r : Γ(X, V)) (i : Fin (n + 1))
    (hle : (symmetricGradedAlgebra hE hfin).projι (site (hV.basicOpen r)) ''ᵁ ⊤ ≤
      (symmetricGradedAlgebra hE hfin).projι (site hV) ''ᵁ ⊤) :
    M.presheaf.map (homOfLE hle).op (pieceSection hE hfin (e := e) M α hV hVU i) =
      pieceSection hE hfin (e := e) M α (hV.basicOpen r) ((X.basicOpen_le r).trans hVU) i := by
  apply (ConcreteCategory.bijective_of_isIso ((α (site (hV.basicOpen r))).hom.app ⊤)).1
  rw [pieceSection_hom, hα hV r,
    DirectedModuleGluing.pmap_map M _ _ (homOfLE (Scheme.Hom.image_mono _ le_top)).op,
    pieceSection_spec]
  refine (ProjTwistMap.twistRestrictHom_app_degreeOneSection _ _ _).trans ?_
  congr 1
  exact Subtype.ext (pieceElt_restrict hE hfin hV hVU r i)

end Abstract

end AlgebraicGeometry.Scheme.Modules
