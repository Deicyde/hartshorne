/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveBundleGluing

/-!
# The twisting sheaf of a projective bundle over an open where the module is free

Hartshorne, *Algebraic Geometry*, II.7, p. 162: if `E` is free of rank `n + 1` over an open
`U ⊆ X`, then `P(E)|_U ≅ ℙⁿ_U`, compatibly with the projection and with `𝒪(1)`.

For a frame `e` of `E` over an arbitrary open `U`, `Scheme.Modules.exists_projectiveBundleIso_of_frame`
gives `ψ : π⁻¹(U) ≅ ℙⁿ_U` over `U`. Here we show `ψ^* 𝒪_{ℙⁿ_U}(1) ≅ 𝒪_{P(E)}(1)|_{π⁻¹(U)}`
(`Scheme.Modules.exists_projectiveBundleIso_of_frame_twist`, and
`Scheme.Modules.nonempty_projectiveBundle_iso_twist_of_restrict_iso_free` from `E|_U ≅ 𝒪_U^{n+1}`).

## Proof

On the affine piece `Proj Γ(V, S(E))` over an affine open `V ⊆ U`, the morphism
`π⁻¹(U) ≅ ℙⁿ_U ⟶ ℙⁿ_ℤ` is `Proj` of `z_k ↦ e_k`; so `ψ⁻¹(D₊(z_i))` meets the piece in `D₊(e_i)`
and `ψ^#(z_j/z_i) = e_j/e_i` there. The degree-one sections `e_i` of the twisting sheaves of the
affine pieces are compatible with the transition maps along basic opens, so they glue to sections
`s_i` of `𝒪_{P(E)}(1)` over `π⁻¹(U)`. On `ψ⁻¹(D₊(z_i))` both `ψ^* z_i` and `s_i` are frames, and
both families have the transition functions `ψ^#(z_j/z_i)`; hence the two invertible sheaves are
isomorphic (`Hartshorne.Ringed.exists_iso_of_frames`), as in the proof of Theorem II.7.1.
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
    [IsOpenImmersion f] {M : Y.Modules} {W : Z.Opens} {t : Γ(M.restrict f, W)}
    (ht : IsTrivializingSection (M.restrict f) W t) :
    IsTrivializingSection M (f ''ᵁ W) ((M.restrictAppIso f W).hom t) := by
  change IsTrivializingSection M (f ''ᵁ W) (show Γ(M, f ''ᵁ W) from t)
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

/-- Scalars act on the sections of a restriction along an open immersion through `appIso`. -/
theorem restrictAppIso_inv_smul {Z Y : Scheme.{u}} (f : Z ⟶ Y) [IsOpenImmersion f]
    (N : Y.Modules) (D : Z.Opens) (a : Γ(Y, f ''ᵁ D)) (t : Γ(N, f ''ᵁ D)) :
    (N.restrictAppIso f D).inv (a • t) =
      (f.appIso D).hom a • (N.restrictAppIso f D).inv t := by
  change (a • t) = (f.appIso D).inv ((f.appIso D).hom a) • t
  rw [Iso.hom_inv_id_apply]

/-- A relation `x₂ = r x₁` over `W₁` between restrictions of global sections gives the
corresponding relation on `W₁ ⊓ W₂`. -/
theorem restrict_inf_smul {Z : Scheme.{u}} {N : Z.Modules} {W₁ W₂ : Z.Opens} (x₁ x₂ : Γ(N, ⊤))
    (r : Γ(Z, W₁))
    (h : N.presheaf.map (homOfLE (le_top : W₁ ≤ ⊤)).op x₂ =
      r • N.presheaf.map (homOfLE (le_top : W₁ ≤ ⊤)).op x₁) :
    N.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op
        (N.presheaf.map (homOfLE (le_top : W₂ ≤ ⊤)).op x₂) =
      Z.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op r •
        N.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op
          (N.presheaf.map (homOfLE (le_top : W₁ ≤ ⊤)).op x₁) := by
  rw [Scheme.Modules.map_map_homOfLE, ← Scheme.Modules.map_map_homOfLE N le_top
    (inf_le_left : W₁ ⊓ W₂ ≤ W₁), h, Scheme.Modules.map_smul]

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

/-- The affine opens contained in `U`. -/
private abbrev AffinesIn (U : X.Opens) : Type u := {V : X.Opens // IsAffineOpen V ∧ V ≤ U}

omit [IsNoetherian X] in
private lemma projι_image_top {V : X.Opens} (hV : IsAffineOpen V) :
    (symmetricGradedAlgebra hE hfin).projι (site hV) ''ᵁ ⊤ =
      (symmetricGradedAlgebra hE hfin).relProjToBase ⁻¹ᵁ V := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact ((symmetricGradedAlgebra hE hfin).relProjToBase_preimage (site hV)).symm

private lemma ιU_image_top :
    (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ''ᵁ ⊤ = projectiveBundleProj hE hfin ⁻¹ᵁ U := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

private lemma projι_image_top_le {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) :
    (symmetricGradedAlgebra hE hfin).projι (site hV) ''ᵁ ⊤ ≤
      (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ''ᵁ ⊤ := by
  rw [projι_image_top, ιU_image_top]
  exact Scheme.Hom.preimage_mono _ hVU

/-- Every point of `π⁻¹(U)` lies on one of the affine pieces. -/
private lemma exists_pieceι_eq (x : (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme) :
    ∃ (V : AffinesIn U) (y : Proj ((symmetricGradedAlgebra hE hfin).grading (site V.2.1))),
      pieceι hE hfin V.2.1 V.2.2 y = x := by
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show projectiveBundleProj hE hfin x.1 ∈ U from x.2)
  refine ⟨⟨V, hV, hVU⟩, ((Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono
    (projectiveBundleProj hE hfin) hVU)).hom ≫
      ((symmetricGradedAlgebra hE hfin).restrictIso (site hV)).hom) ⟨x, hxV⟩, ?_⟩
  rw [← Scheme.Hom.comp_apply, pieceι, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_assoc]
  rfl

section Abstract2

variable (M : (projectiveBundle hE hfin).Modules)
  (α : ∀ V : X.AffineZariskiSite, M.restrict ((symmetricGradedAlgebra hE hfin).projι V) ≅
    (symmetricGradedAlgebra hE hfin).twistingSheaf 1 V)
  (hα : ∀ {V : X.Opens} (hV : IsAffineOpen V) (r : Γ(X, V))
    (x : Γ(M, (symmetricGradedAlgebra hE hfin).projι (site (hV.basicOpen r)) ''ᵁ ⊤)),
    (α (site (hV.basicOpen r))).hom.app ⊤ x =
      ((symmetricGradedAlgebra hE hfin).twistTransition 1 (basicArrow hV r)).hom.app ⊤
        ((α (site hV)).hom.app _
          (M.presheaf.map (homOfLE (projι_image_basicArrow hE hfin hV r)).op x)))

include hα in
private lemma pieceSection_basicOpen' {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (hVU : V ≤ U) (hWU : W ≤ U) (r : Γ(X, V)) (hWr : X.basicOpen r = W)
    (i : Fin (n + 1))
    (hle : (symmetricGradedAlgebra hE hfin).projι (site hW) ''ᵁ ⊤ ≤
      (symmetricGradedAlgebra hE hfin).projι (site hV) ''ᵁ ⊤) :
    M.presheaf.map (homOfLE hle).op (pieceSection hE hfin (e := e) M α hV hVU i) =
      pieceSection hE hfin (e := e) M α hW hWU i := by
  subst hWr
  exact pieceSection_basicOpen hE hfin M α hα hV hVU r i hle

include hα in
/-- The sections `e_i` over the affine pieces glue to a section of `M` over `π⁻¹(U)`. -/
private lemma exists_globalSection (i : Fin (n + 1)) :
    ∃ s : Γ(M, (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ''ᵁ ⊤),
      ∀ (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U),
        M.presheaf.map (homOfLE (projι_image_top_le hE hfin hV hVU)).op s =
          pieceSection hE hfin (e := e) M α hV hVU i := by
  let Wf : AffinesIn U → (projectiveBundle hE hfin).Opens :=
    fun V => (symmetricGradedAlgebra hE hfin).projι (site V.2.1) ''ᵁ ⊤
  have hcov : (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ iSup Wf := by
    rw [ιU_image_top]
    intro p hp
    obtain ⟨V, hV, hpV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hp
    refine Opens.mem_iSup.2 ⟨⟨V, hV, hVU⟩, ?_⟩
    change p ∈ (symmetricGradedAlgebra hE hfin).projι (site hV) ''ᵁ ⊤
    rw [projι_image_top]
    exact hpV
  obtain ⟨s, hs⟩ := DirectedModuleGluing.mod_glue M Wf
    (fun V => projι_image_top_le hE hfin V.2.1 V.2.2) hcov
    (fun V => (pieceSection hE hfin (e := e) M α V.2.1 V.2.2 i : Γ(M, Wf V))) (by
      intro k l
      have hx : ∀ p : ↥(Wf k ⊓ Wf l), (symmetricGradedAlgebra hE hfin).relProjToBase p.1 ∈
          k.1 ⊓ l.1 := by
        intro p
        have h := p.2
        simp only [Wf, projι_image_top] at h
        exact h
      choose R T hRT hpR using fun p => exists_basicOpen_le_affine_inter k.2.1 l.2.1 _ (hx p)
      have hD : ∀ p, (symmetricGradedAlgebra hE hfin).projι (site (k.2.1.basicOpen (R p))) ''ᵁ ⊤ =
          (symmetricGradedAlgebra hE hfin).relProjToBase ⁻¹ᵁ X.basicOpen (R p) :=
        fun p => projι_image_top hE hfin _
      have h1 : ∀ p, (symmetricGradedAlgebra hE hfin).projι (site (k.2.1.basicOpen (R p))) ''ᵁ ⊤ ≤
          Wf k := fun p => by
        simp only [Wf]
        rw [hD, projι_image_top]
        exact Scheme.Hom.preimage_mono _ (X.basicOpen_le _)
      have h2 : ∀ p, (symmetricGradedAlgebra hE hfin).projι (site (k.2.1.basicOpen (R p))) ''ᵁ ⊤ ≤
          Wf l := fun p => by
        simp only [Wf]
        rw [hD, projι_image_top, hRT]
        exact Scheme.Hom.preimage_mono _ (X.basicOpen_le _)
      refine DirectedModuleGluing.mod_ext M
        (fun p => (symmetricGradedAlgebra hE hfin).projι (site (k.2.1.basicOpen (R p))) ''ᵁ ⊤)
        (fun p => le_inf (h1 p) (h2 p)) ?_ _ _ fun p => ?_
      · intro q hq
        refine Opens.mem_iSup.2 ⟨⟨q, hq⟩, ?_⟩
        change q ∈ (symmetricGradedAlgebra hE hfin).projι (site (k.2.1.basicOpen (R ⟨q, hq⟩))) ''ᵁ ⊤
        rw [hD]
        exact hpR ⟨q, hq⟩
      · rw [DirectedModuleGluing.pmap_map M _ _ (homOfLE (h1 p)).op,
          DirectedModuleGluing.pmap_map M _ _ (homOfLE (h2 p)).op,
          pieceSection_basicOpen' hE hfin M α hα k.2.1 (k.2.1.basicOpen (R p)) k.2.2
            ((X.basicOpen_le _).trans k.2.2) (R p) rfl,
          pieceSection_basicOpen' hE hfin M α hα l.2.1 (k.2.1.basicOpen (R p)) l.2.2
            ((X.basicOpen_le _).trans k.2.2) (T p) (hRT p).symm])
  exact ⟨s, fun V hV hVU => hs ⟨V, hV, hVU⟩⟩

/-- `M|_{π⁻¹(U)}` restricted to the affine piece over `V` is `𝒪_{Proj Γ(V, S(E))}(1)`. -/
private def pieceIso {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U) :
    (M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).restrict (pieceι hE hfin hV hVU) ≅
      (symmetricGradedAlgebra hE hfin).twistingSheaf 1 (site hV) :=
  ((restrictFunctorComp (pieceι hE hfin hV hVU) (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).app
      M).symm ≪≫
    (restrictFunctorCongr (pieceι_ι hE hfin hV hVU)).app M ≪≫ α (site hV)

private lemma projι_image_le_pieceι {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (D : (Proj ((symmetricGradedAlgebra hE hfin).grading (site hV))).Opens) :
    (symmetricGradedAlgebra hE hfin).projι (site hV) ''ᵁ D ≤
      (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ''ᵁ (pieceι hE hfin hV hVU ''ᵁ D) := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨pieceι hE hfin hV hVU y, ⟨y, hy, rfl⟩, by rw [← pieceι_ι hE hfin hV hVU]; rfl⟩

private lemma pieceIso_hom_app {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (D : (Proj ((symmetricGradedAlgebra hE hfin).grading (site hV))).Opens)
    (y : Γ(M, (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ''ᵁ (pieceι hE hfin hV hVU ''ᵁ D))) :
    (pieceIso hE hfin M α hV hVU).hom.app D y = (α (site hV)).hom.app D
      (M.presheaf.map (homOfLE (projι_image_le_pieceι hE hfin hV hVU D)).op y) := by
  simp only [pieceIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app]
  exact congrArg ((α (site hV)).hom.app D) (DirectedModuleGluing.pmap_map M _ _ _ y)

private lemma pieceIso_hom_app_global {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (i : Fin (n + 1)) (s : Γ(M, (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ''ᵁ ⊤))
    (hs : M.presheaf.map (homOfLE (projι_image_top_le hE hfin hV hVU)).op s =
      pieceSection hE hfin (e := e) M α hV hVU i)
    (D : (Proj ((symmetricGradedAlgebra hE hfin).grading (site hV))).Opens) :
    (pieceIso hE hfin M α hV hVU).hom.app D
        (M.presheaf.map (homOfLE (Scheme.Hom.image_mono _
          (le_top : pieceι hE hfin hV hVU ''ᵁ D ≤ ⊤))).op s) =
      (projTwistingSheaf ((symmetricGradedAlgebra hE hfin).grading (site hV)) 1).presheaf.map
        (homOfLE (le_top : D ≤ ⊤)).op
        (ProjTwistingSheaf.degreeOneSection ⟨pieceElt hE hfin (e := e) hV hVU i,
          pieceElt_mem hE hfin hV hVU i⟩) := by
  rw [pieceIso_hom_app, DirectedModuleGluing.pmap_map_eq M _ _ (homOfLE (projι_image_top_le hE hfin hV hVU)).op
    (homOfLE (Scheme.Hom.image_mono _ (le_top : D ≤ ⊤))).op, hs, pieceSection_spec]

omit [IsNoetherian X] in
private lemma degreeOne_restrict_smul {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (i j : Fin (n + 1)) (D : (Proj ((symmetricGradedAlgebra hE hfin).grading (site hV))).Opens)
    (hD : D ≤ Proj.basicOpen _ (pieceElt hE hfin (e := e) hV hVU i)) :
    (projTwistingSheaf ((symmetricGradedAlgebra hE hfin).grading (site hV)) 1).presheaf.map
        (homOfLE (le_top : D ≤ ⊤)).op
        (ProjTwistingSheaf.degreeOneSection ⟨pieceElt hE hfin (e := e) hV hVU j,
          pieceElt_mem hE hfin hV hVU j⟩) =
      (Proj ((symmetricGradedAlgebra hE hfin).grading (site hV))).presheaf.map (homOfLE hD).op
          (Proj.awayToSection _ (pieceElt hE hfin (e := e) hV hVU i)
            (HomogeneousLocalization.Away.mk _ (pieceElt_mem hE hfin hV hVU i) 1
              (pieceElt hE hfin (e := e) hV hVU j)
              (by simpa using pieceElt_mem hE hfin hV hVU j))) •
        (projTwistingSheaf ((symmetricGradedAlgebra hE hfin).grading (site hV)) 1).presheaf.map
          (homOfLE (le_top : D ≤ ⊤)).op
          (ProjTwistingSheaf.degreeOneSection ⟨pieceElt hE hfin (e := e) hV hVU i,
            pieceElt_mem hE hfin hV hVU i⟩) := by
  have h0 := ProjTwistingSheaf.restrict_degreeOneSection_eq_smul
    (pieceElt_mem hE hfin (e := e) hV hVU i) (pieceElt_mem hE hfin (e := e) hV hVU j)
  have h := congrArg (fun x => (projTwistingSheaf ((symmetricGradedAlgebra hE hfin).grading
    (site hV)) 1).presheaf.map (homOfLE hD).op x) h0
  simp only at h
  rw [Scheme.Modules.map_map_homOfLE, Scheme.Modules.map_smul,
    Scheme.Modules.map_map_homOfLE] at h
  exact h

include hψ in
private lemma pieceι_appIso_ratio {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (i j : Fin (n + 1)) :
    ((pieceι hE hfin hV hVU).appIso (pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i)).hom
        ((projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme.presheaf.map
          (homOfLE (Scheme.Hom.image_preimage_le _ _)).op
          ((toIntMap ψ.hom).app (chartInt n i) (ratioInt n i j))) =
      (Proj ((symmetricGradedAlgebra hE hfin).grading (site hV))).presheaf.map
          (homOfLE (pieceι_preimage_chart hE hfin he ψ hψ hV hVU i).le).op
          (Proj.awayToSection _ (pieceElt hE hfin (e := e) hV hVU i)
            (HomogeneousLocalization.Away.mk _ (pieceElt_mem hE hfin hV hVU i) 1
              (pieceElt hE hfin (e := e) hV hVU j)
              (by simpa using pieceElt_mem hE hfin hV hVU j))) := by
  rw [Scheme.Hom.appIso_hom', ← pieceι_appLE_ratio hE hfin he ψ hψ hV hVU i j]
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
  conv_rhs => rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

private lemma pieceIso_hom_app_global' {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (i : Fin (n + 1)) (s : Γ(M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι, ⊤))
    (hs : M.presheaf.map (homOfLE (projι_image_top_le hE hfin hV hVU)).op
      ((M.restrictAppIso (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⊤).hom s) =
      pieceSection hE hfin (e := e) M α hV hVU i)
    (D : (Proj ((symmetricGradedAlgebra hE hfin).grading (site hV))).Opens) :
    (pieceIso hE hfin M α hV hVU).hom.app D
        (((M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).restrictAppIso
          (pieceι hE hfin hV hVU) D).inv
        ((M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).presheaf.map
          (homOfLE (le_top : pieceι hE hfin hV hVU ''ᵁ D ≤ ⊤)).op s)) =
      (projTwistingSheaf ((symmetricGradedAlgebra hE hfin).grading (site hV)) 1).presheaf.map
        (homOfLE (le_top : D ≤ ⊤)).op
        (ProjTwistingSheaf.degreeOneSection ⟨pieceElt hE hfin (e := e) hV hVU i,
          pieceElt_mem hE hfin hV hVU i⟩) :=
  pieceIso_hom_app_global hE hfin M α hV hVU i _ hs D

omit [IsNoetherian X] in
private lemma iso_inv_hom_app {Z : Scheme.{u}} {M N : Z.Modules} (α : M ≅ N) (W : Z.Opens)
    (x : Γ(M, W)) : α.inv.app W (α.hom.app W x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, α.hom_inv_id,
    Scheme.Modules.Hom.id_app]
  rfl

include he hψ in
/-- **Transition functions.** On `ψ⁻¹(D₊(z_i))`, the glued section `s_j` is `ψ^#(z_j/z_i) s_i`. -/
private lemma global_transition
    (s : Fin (n + 1) → Γ(M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι, ⊤))
    (hs : ∀ i (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U),
      M.presheaf.map (homOfLE (projι_image_top_le hE hfin hV hVU)).op
        ((M.restrictAppIso (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⊤).hom (s i)) =
        pieceSection hE hfin (e := e) M α hV hVU i) (i j : Fin (n + 1)) :
    (M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).presheaf.map
        (homOfLE (le_top : chartPreimage ψ.hom i ≤ ⊤)).op (s j) =
      (toIntMap ψ.hom).app (chartInt n i) (ratioInt n i j) •
        (M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).presheaf.map
          (homOfLE (le_top : chartPreimage ψ.hom i ≤ ⊤)).op (s i) := by
  refine DirectedModuleGluing.mod_ext (M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι)
    (fun V : AffinesIn U => pieceι hE hfin V.2.1 V.2.2 ''ᵁ
      (pieceι hE hfin V.2.1 V.2.2 ⁻¹ᵁ chartPreimage ψ.hom i))
    (fun V => Scheme.Hom.image_preimage_le _ _) ?_ _ _ (fun V => ?_)
  · intro x hx
    obtain ⟨V, y, rfl⟩ := exists_pieceι_eq hE hfin x
    exact Opens.mem_iSup.2 ⟨V, ⟨y, hx, rfl⟩⟩
  · obtain ⟨V, hV, hVU⟩ := V
    rw [Scheme.Modules.map_map_homOfLE, Scheme.Modules.map_smul, Scheme.Modules.map_map_homOfLE]
    apply ((ConcreteCategory.bijective_of_isIso ((pieceIso hE hfin M α hV hVU).hom.app
      (pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i))).comp
      (ConcreteCategory.bijective_of_isIso
        (((M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).restrictAppIso
          (pieceι hE hfin hV hVU) (pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i)).inv))).1
    simp only [Function.comp_apply]
    rw [restrictAppIso_inv_smul, Scheme.Modules.Hom.app_smul,
      pieceIso_hom_app_global' hE hfin M α hV hVU j (s j) (hs j V hV hVU),
      pieceIso_hom_app_global' hE hfin M α hV hVU i (s i) (hs i V hV hVU),
      pieceι_appIso_ratio hE hfin he ψ hψ hV hVU i j]
    exact degreeOne_restrict_smul hE hfin hV hVU i j _ _

include he hψ in
/-- **Frames.** On `ψ⁻¹(D₊(z_i))`, the glued section `s_i` trivializes `M|_{π⁻¹(U)}`. -/
private lemma global_trivializing (i : Fin (n + 1))
    (s : Γ(M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι, ⊤))
    (hs : ∀ (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U),
      M.presheaf.map (homOfLE (projι_image_top_le hE hfin hV hVU)).op
        ((M.restrictAppIso (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⊤).hom s) =
        pieceSection hE hfin (e := e) M α hV hVU i) :
    IsTrivializingSection (M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι)
      (chartPreimage ψ.hom i)
      ((M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).presheaf.map
        (homOfLE (le_top : chartPreimage ψ.hom i ≤ ⊤)).op s) := by
  refine IsTrivializingSection.of_local fun x hx => ?_
  obtain ⟨⟨V, hV, hVU⟩, y, rfl⟩ := exists_pieceι_eq hE hfin x
  refine ⟨pieceι hE hfin hV hVU ''ᵁ (pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i),
    Scheme.Hom.image_preimage_le _ _, ⟨y, hx, rfl⟩, ?_⟩
  rw [Scheme.Modules.map_map_homOfLE, ← Iso.inv_hom_id_apply
    ((M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).restrictAppIso
      (pieceι hE hfin hV hVU) (pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i))
    ((M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).presheaf.map
      (homOfLE (le_top : pieceι hE hfin hV hVU ''ᵁ
        (pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i) ≤ ⊤)).op s)]
  apply IsTrivializingSection.image_of_restrict
  rw [← iso_inv_hom_app (pieceIso hE hfin M α hV hVU)
    (pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i)
    (((M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).restrictAppIso
      (pieceι hE hfin hV hVU) (pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i)).inv
    ((M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).presheaf.map
      (homOfLE (le_top : pieceι hE hfin hV hVU ''ᵁ
        (pieceι hE hfin hV hVU ⁻¹ᵁ chartPreimage ψ.hom i) ≤ ⊤)).op s)),
    pieceIso_hom_app_global' hE hfin M α hV hVU i s (hs V hV hVU)]
  refine IsTrivializingSection.map_iso (pieceIso hE hfin M α hV hVU).symm ?_
  have h := (IsTrivializingSection.of_isLocalFrame (ι := PUnit.{u + 1})
    (ProjTwistingSheaf.isLocalFrame_degreeOneSection
      (pieceElt_mem hE hfin (e := e) hV hVU i))).restrict
    (pieceι_preimage_chart hE hfin he ψ hψ hV hVU i).le
  convert h using 1
  exact (Scheme.Modules.map_map_homOfLE _ _ _ _).symm

include he hψ hα in
/-- **`ψ^* 𝒪(1) ≅ M|_{π⁻¹(U)}`**, glued from the frames `ψ^* z_i` and `s_i` on the opens
`ψ⁻¹(D₊(z_i))`, which have the same transition functions. -/
private lemma nonempty_pullbackTwist_iso :
    Nonempty (pullbackTwist ψ.hom ≅ M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι) := by
  choose s₀ hs₀ using exists_globalSection hE hfin (e := e) M α hα
  let s : Fin (n + 1) → Γ(M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι, ⊤) :=
    fun i => (M.restrictAppIso (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⊤).inv (s₀ i)
  have hs : ∀ i (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U),
      M.presheaf.map (homOfLE (projι_image_top_le hE hfin hV hVU)).op
        ((M.restrictAppIso (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⊤).hom (s i)) =
      pieceSection hE hfin (e := e) M α hV hVU i := by
    intro i V hV hVU
    simp only [s, Iso.inv_hom_id_apply]
    exact hs₀ i V hV hVU
  let W : ULift.{u} (Fin (n + 1)) → (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme.Opens :=
    fun k => chartPreimage ψ.hom k.down
  have hW : ⊤ ≤ iSup W := by
    intro x _
    obtain ⟨k, hk⟩ := exists_mem_chartPreimage ψ.hom x
    exact Opens.mem_iSup.2 ⟨⟨k⟩, hk⟩
  have σ : PUnit.{u + 1} ≃ ULift.{u} (Fin 1) := Equiv.ofUnique _ _
  obtain ⟨φ, -⟩ := Ringed.exists_iso_of_frames
    (R := (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme.sheaf) W hW
    (fun k => (pullbackTwist ψ.hom).presheaf.map (homOfLE le_top).op
      (pullbackGlobalSection ψ.hom (projectiveSpaceCoordinate n U k.down)))
    (fun k => (M.restrict (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι).presheaf.map
      (homOfLE le_top).op (s k.down))
    (fun k => (isLocalFrame_of_isTrivializingSection
      (isTrivializingSection_chartPreimage ψ.hom k.down)).reindex σ)
    (fun k => (isLocalFrame_of_isTrivializingSection
      (global_trivializing hE hfin he ψ hψ M α k.down (s k.down) (hs k.down))).reindex σ)
    (fun i j => ⟨_, restrict_inf_smul _ _ _
      (restrict_pullbackGlobalSection_eq_smul ψ.hom i.down j.down),
      restrict_inf_smul _ _ _ (global_transition hE hfin he ψ hψ M α s hs i.down j.down)⟩)
  exact ⟨φ⟩

include he in
/-- **`P(E)` over an open with a frame, with its twisting sheaf** (Hartshorne II.7, p. 162): a
frame `e` of `E` of rank `n + 1` over an arbitrary open `U ⊆ X` gives an isomorphism
`ψ : π⁻¹(U) ≅ ℙⁿ_U` over `U` with `ψ^* 𝒪_{ℙⁿ_U}(1) ≅ 𝒪_{P(E)}(1)|_{π⁻¹(U)}`. -/
theorem exists_projectiveBundleIso_of_frame_twist :
    ∃ ψ : (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme ≅ projectiveSpaceOverScheme n U,
      ψ.hom ≫ projectiveSpaceOverSchemeProjection n U = projectiveBundleProj hE hfin ∣_ U ∧
      Nonempty ((Scheme.Modules.pullback ψ.hom).obj (projectiveSpaceTwistingSheaf n U 1) ≅
        (projectiveBundleTwistingSheaf hE hfin 1).restrict
          (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι) := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := exists_projectiveBundleIso_of_frame hE hfin he
  refine ⟨ψ, hψ₁, nonempty_pullbackTwist_iso hE hfin he ψ hψ₂ _
    (fun V => (symmetricGradedAlgebra hE hfin).relTwistingSheafRestrictIso 1 V) ?_⟩
  intro V hV r x
  exact ((symmetricGradedAlgebra hE hfin).twistData 1).ψ_hom_app_top (basicArrow hV r)
    (colimit.w (symmetricGradedAlgebra hE hfin).relativeGluingData.functor (basicArrow hV r))
    (projι_image_basicArrow hE hfin hV r) x

end Abstract2

/-- **Projective bundles of free modules** (Hartshorne II.7, p. 162): if `E` is free of rank
`n + 1` on an open `U ⊆ X`, i.e. `E|_U ≅ 𝒪_U^{n+1}`, then `P(E)|_U = π⁻¹(U) ≅ ℙⁿ_U` over `U`,
by an isomorphism `ψ` with `ψ^* 𝒪_{ℙⁿ_U}(1) ≅ 𝒪_{P(E)}(1)|_{π⁻¹(U)}`. -/
theorem nonempty_projectiveBundle_iso_twist_of_restrict_iso_free {U : X.Opens} {n : ℕ}
    (α : E.restrict U.ι ≅ SheafOfModules.free (ULift.{u} (Fin (n + 1)))) :
    ∃ ψ : (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme ≅ projectiveSpaceOverScheme n U,
      ψ.hom ≫ projectiveSpaceOverSchemeProjection n U = projectiveBundleProj hE hfin ∣_ U ∧
      Nonempty ((Scheme.Modules.pullback ψ.hom).obj (projectiveSpaceTwistingSheaf n U 1) ≅
        (projectiveBundleTwistingSheaf hE hfin 1).restrict
          (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι) := by
  obtain ⟨β⟩ := (nonempty_restrict_iso_free_iff E U _).mp ⟨α⟩
  exact exists_projectiveBundleIso_of_frame_twist hE hfin
    (Ringed.isLocalFrame_of_over_iso (R := X.sheaf) β)

end AlgebraicGeometry.Scheme.Modules
