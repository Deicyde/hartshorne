/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjGradedModuleSheafChart
import Hartshorne.Scheme.CoherentAffineLocalCriterion

/-!
# Quasi-coherence and coherence of the sheaf of a graded module on Proj

Hartshorne, *Algebraic Geometry*, II.5, Proposition 5.11(c) (p. 117).

Let `S` be an `ℕ`-graded ring and `M` a graded `S`-module. Then `M~` is a quasi-coherent
`𝒪_{Proj S}`-module, and it is coherent when `S` is Noetherian and `M` is finitely generated.
Both follow from the chart isomorphism `M~|_{D₊(f)} ≅ (M_(f))~` on the cover of `Proj S` by the
`D₊(f)`, `f` homogeneous of positive degree.

## Main results

* `Hartshorne.ProjGradedModuleSheaf.isQuasicoherent`: `M~` is quasi-coherent.
* `Hartshorne.ProjGradedModuleSheaf.isCoherent`: `M~` is coherent if `S` is Noetherian and `M`
  is finitely generated.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
  (ℳ : ℤ → σM) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

namespace ProjGradedModuleSheaf

/-- The index set of the standard cover of `Proj S`: homogeneous elements of positive degree. -/
abbrev ChartIndex : Type u := {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}

/-- The opens `D₊(f)`, `f` homogeneous of positive degree, cover `Proj S`. -/
theorem iSup_basicOpen_chartIndex : ⨆ i : ChartIndex 𝒜, Proj.basicOpen 𝒜 i.1.1 = ⊤ := by
  classical
  refine top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ?_
  obtain ⟨f, m, f_deg, hm, hx⟩ : ∃ (f : A) (m : ℕ) (_ : f ∈ 𝒜 m) (_ : 0 < m),
      f ∉ x.asHomogeneousIdeal := by
    by_contra! H
    refine x.not_irrelevant_le fun z hz => ?_
    rw [← DirectSum.sum_support_decompose 𝒜 z]
    exact x.asHomogeneousIdeal.toIdeal.sum_mem fun k hk => H _ k (SetLike.coe_mem _) <|
      by_contra <| by aesop
  exact ⟨⟨(f, m), hm, f_deg⟩, hx⟩

variable {𝒜} in
theorem basicOpenIsoSpec_hom_awayι {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d) :
    (Proj.basicOpenIsoSpec 𝒜 f f_deg hd).hom ≫ Proj.awayι 𝒜 f f_deg hd =
      (Proj.basicOpen 𝒜 f).ι := by
  rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]

/-- A presentation of the restriction of `M~` to the chart, from the chart isomorphism. -/
def presentationChart {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d) :
    (chartModule 𝒜 ℳ f_deg hd).Presentation :=
  @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ (fromTildeChart 𝒜 ℳ f_deg hd)
    (isIso_fromTildeChart 𝒜 ℳ f_deg hd)
    (presentationTilde.{u} (awayModule 𝒜 ℳ f) .univ (by simp) _ (Submodule.span_eq _))

set_option backward.isDefEq.respectTransparency false in
/-- A presentation of the restriction of `M~` to the open subscheme `D₊(f)`. -/
def presentationRestrictBasicOpen {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d) :
    ((projGradedModuleSheaf 𝒜 ℳ).restrict (Proj.basicOpen 𝒜 f).ι).Presentation :=
  let F := projGradedModuleSheaf 𝒜 ℳ
  let e : (F.restrict (Proj.awayι 𝒜 f f_deg hd)).restrict
      (Proj.basicOpenIsoSpec 𝒜 f f_deg hd).hom ≅ F.restrict (Proj.basicOpen 𝒜 f).ι :=
    ((Scheme.Modules.restrictFunctorComp _ _).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (basicOpenIsoSpec_hom_awayι f_deg hd)).app F
  @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom e.isIso_hom
    (Scheme.Modules.presentationRestrict (Proj.basicOpenIsoSpec 𝒜 f f_deg hd).hom
      (presentationChart 𝒜 ℳ f_deg hd))

set_option backward.isDefEq.respectTransparency false in
/-- A presentation of the restriction of a module sheaf to an open subscheme `U` gives a
presentation of the module sheaf over `U`. -/
def presentationOverOfRestrict {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (P : (F.restrict U.ι).Presentation) : (F.over U).Presentation := by
  let Q := @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P
    (Scheme.Modules.overEquiv U).inverse
    ((Scheme.Modules.overEquiv U).symm.toAdjunction.leftAdjoint_preservesColimits)
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e : F.over U ≅ (Scheme.Modules.overEquiv U).inverse.obj (F.restrict U.ι) :=
    (Scheme.Modules.overEquiv U).unitIso.app (F.over U) ≪≫
      (Scheme.Modules.overEquiv U).inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app F)
  letI : IsIso e.inv := e.isIso_inv
  exact SheafOfModules.Presentation.ofIsIso e.inv Q

/-- A presentation of `M~` over `D₊(f)`, obtained from the chart isomorphism. -/
def presentationOverBasicOpen {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d) :
    ((projGradedModuleSheaf 𝒜 ℳ).over (Proj.basicOpen 𝒜 f)).Presentation :=
  presentationOverOfRestrict _ _ (presentationRestrictBasicOpen 𝒜 ℳ f_deg hd)

/-- **Hartshorne II.5.11(c).** The sheaf `M~` of a graded module on `Proj S` is
quasi-coherent. -/
theorem isQuasicoherent : (projGradedModuleSheaf 𝒜 ℳ).IsQuasicoherent := by
  have hcov : (Opens.grothendieckTopology (Proj 𝒜)).CoversTop
      (fun i : ChartIndex 𝒜 => Proj.basicOpen 𝒜 i.1.1) := by
    rw [Opens.coversTop_iff, IsOpenCover]
    exact iSup_basicOpen_chartIndex 𝒜
  have (i : ChartIndex 𝒜) :
      ((projGradedModuleSheaf 𝒜 ℳ).over (Proj.basicOpen 𝒜 i.1.1)).IsQuasicoherent :=
    (presentationOverBasicOpen 𝒜 ℳ i.2.2 i.2.1).isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop (projGradedModuleSheaf 𝒜 ℳ)
    (fun i : ChartIndex 𝒜 => Proj.basicOpen 𝒜 i.1.1) hcov

/-- The global sections of the restriction of `M~` to the chart are `M_(f)`. -/
def awayModuleIsoChartSections {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d) :
    awayModule 𝒜 ℳ f ≅ chartSections 𝒜 ℳ f_deg hd ⊤ :=
  tilde.isoTop (awayModule 𝒜 ℳ f) ≪≫
    ((sheafToPresheaf _ _).mapIso (modulesSpecToSheaf.mapIso
      (@asIso _ _ _ _ (fromTildeChart 𝒜 ℳ f_deg hd) (isIso_fromTildeChart 𝒜 ℳ f_deg hd)))).app
        (op ⊤)

set_option backward.isDefEq.respectTransparency false in
/-- If `S` is Noetherian and `M` is finitely generated, the sections of `M~` over `D₊(f)` are a
finitely generated module over the sections of `𝒪_{Proj S}`. -/
theorem finite_sections_basicOpen [IsNoetherianRing A] [Module.Finite A M] {f : A} {d : ℕ}
    (f_deg : f ∈ 𝒜 d) (hd : 0 < d) :
    Module.Finite Γ(Proj 𝒜, Proj.basicOpen 𝒜 f)
      Γ(projGradedModuleSheaf 𝒜 ℳ, Proj.basicOpen 𝒜 f) := by
  have h₁ : Module.Finite (Away 𝒜 f) (chartSections 𝒜 ℳ f_deg hd ⊤) :=
    haveI := HomogeneousLocalizedModule.finite_away (ℳ := ℳ) f_deg hd
    Module.Finite.equiv (awayModuleIsoChartSections 𝒜 ℳ f_deg hd).toLinearEquiv
  let _ : Module Γ(Spec (.of (Away 𝒜 f)), ⊤) (chartSections 𝒜 ℳ f_deg hd ⊤) :=
    inferInstanceAs (Module Γ(Spec (.of (Away 𝒜 f)), ⊤)
      Γ(chartModule 𝒜 ℳ f_deg hd, ⊤))
  have h₂ : Module.Finite Γ(Spec (.of (Away 𝒜 f)), ⊤) Γ(chartModule 𝒜 ℳ f_deg hd, ⊤) := by
    refine (CoherentAux.finite_iff_of_ringEquiv (N := chartSections 𝒜 ℳ f_deg hd ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).symm.commRingCatIsoToRingEquiv
      (fun a n => ?_)).1 h₁
    have : (⊤ : (Spec (.of (Away 𝒜 f))).Opens).leTop = 𝟙 ⊤ := Subsingleton.elim _ _
    change ((Spec (.of (Away 𝒜 f))).presheaf.map (⊤ : (Spec (.of (Away 𝒜 f))).Opens).leTop.op
      ((Scheme.ΓSpecIso _).inv a)) • n = _
    rw [this, op_id, CategoryTheory.Functor.map_id]
    rfl
  have h₃ := (CoherentAux.finite_restrict_iff (Proj.awayι 𝒜 f f_deg hd)
    (projGradedModuleSheaf 𝒜 ℳ) ⊤).1 h₂
  have hD : (Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤ = Proj.basicOpen 𝒜 f :=
    (Scheme.Hom.image_top_eq_opensRange _).trans (Proj.opensRange_awayι 𝒜 f f_deg hd)
  exact (CoherentAux.finite_congr_opens (projGradedModuleSheaf 𝒜 ℳ) hD).1 h₃

/-- On a quasi-coherent module sheaf whose sections over an affine open `U` are finitely
generated, the restriction to `U` is the tilde of a finitely generated module (from Hartshorne
II.5.4). -/
theorem exists_finite_tilde_of_isQuasicoherent {X : Scheme.{u}} (F : X.Modules)
    (h : F.IsQuasicoherent) (U : X.affineOpens)
    (hfin : Module.Finite Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens))) :
    ∃ N : ModuleCat.{u} Γ(X, (U : X.Opens)), Module.Finite Γ(X, (U : X.Opens)) N ∧
      Nonempty ((tilde.functor Γ(X, (U : X.Opens))).obj N ≅ specRestriction F U) := by
  have h₃ : IsTildeOnEveryAffineOpen F := ((quasicoherent_affine_local_tfae F).out 0 2).mp h
  exact ⟨moduleSpecΓFunctor.obj (specRestriction F U), (finite_specRestriction_iff F U).mpr hfin,
    ⟨@asIso _ _ _ _ (specRestriction F U).fromTildeΓ (h₃ U)⟩⟩

/-- **Hartshorne II.5.11(c).** If `S` is Noetherian and `M` is finitely generated, the sheaf
`M~` on `Proj S` is coherent. -/
theorem isCoherent [IsNoetherianRing A] [Module.Finite A M] :
    IsCoherent (projGradedModuleSheaf 𝒜 ℳ) :=
  ⟨ChartIndex 𝒜, fun i => ⟨Proj.basicOpen 𝒜 i.1.1,
    Proj.isAffineOpen_basicOpen 𝒜 i.1.1 i.2.2 i.2.1⟩, iSup_basicOpen_chartIndex 𝒜,
    fun i => exists_finite_tilde_of_isQuasicoherent _ (isQuasicoherent 𝒜 ℳ) _
      (finite_sections_basicOpen 𝒜 ℳ i.2.2 i.2.1)⟩

end ProjGradedModuleSheaf

end Hartshorne
