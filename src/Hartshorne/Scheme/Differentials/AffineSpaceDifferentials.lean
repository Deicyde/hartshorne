/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.RelativeDifferentialsQuasicoherent
import Hartshorne.Scheme.LocallyFreeInvertible
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Differentials of affine space over an arbitrary base

Hartshorne, *Algebraic Geometry*, II.8, Example 8.12.1 (p. 176).

For every scheme `Y`, the relative differential sheaf of affine space `𝔸(σ; Y) ⟶ Y` is free on
the global sections `d x_i` of the coordinate functions: the morphism `𝒪^{(σ)} ⟶ Ω_{𝔸(σ;Y)/Y}`
sending the `i`-th basis section to `d x_i` is an isomorphism.

Being an isomorphism is local, so it suffices to check this on the open charts
`Spec Γ(Y, V)[x_i] ⟶ 𝔸(σ; Y)` lying over the affine opens `V` of `Y`, which cover `𝔸(σ; Y)`.
Restricted to such a chart, the free module stays free, the relative differential sheaf becomes
`Ω_{Spec Γ(Y, V)[x_i] / Spec Γ(Y, V)}` by locality of differentials, and the coordinates `x_i`
restrict to the polynomial variables, so the restricted morphism is the affine isomorphism
`Scheme.relativeDifferentials_mvPolynomial_free`.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Limits

universe u

namespace AlgebraicGeometry.AffineSpaceDifferentials

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The restriction of a global section of a module sheaf along an open immersion. -/
noncomputable def restrictSection (M : X.Modules) (s : M.sections) : (M.restrict j).sections :=
  PresheafOfModules.sectionsMk (fun W => s.val (op (j ''ᵁ W.unop)))
    (fun _ _ _ => s.property _)

/-- Restricting the morphism `𝒪^{(I)} ⟶ M` given by global sections `s i` along an open
immersion gives the morphism given by the restricted sections. -/
theorem restrictFreeIso_inv_comp_map_freeHomEquiv_symm (M : X.Modules) {I : Type u}
    (s : I → M.sections) :
    (Scheme.Modules.restrictFreeIso j I).inv ≫
      (Scheme.Modules.restrictFunctor j).map (M.freeHomEquiv.symm s) =
    (M.restrict j).freeHomEquiv.symm (fun i => restrictSection j M (s i)) := by
  apply (M.restrict j).freeHomEquiv.injective
  rw [Equiv.apply_symm_apply]
  funext i
  change (M.restrict j).unitHomEquiv (SheafOfModules.ιFree i ≫ _ ≫ _) = _
  rw [Scheme.Modules.restrictFreeIso, Iso.symm_inv]
  erw [SheafOfModules.ιFree_mapFreeIso_hom_assoc]
  erw [← Functor.map_comp]
  have h : SheafOfModules.ιFree i ≫ M.freeHomEquiv.symm s = M.unitHomEquiv.symm (s i) := by
    have := SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (M.freeHomEquiv.symm s) i
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  erw [h]
  refine PresheafOfModules.sections_ext _ _ fun W => ?_
  have h1 : (Scheme.Modules.restrictUnitIso j).inv.val.app W (1 : U.ringCatSheaf.obj.obj W) =
      (1 : X.ringCatSheaf.obj.obj (op (j ''ᵁ W.unop))) := by
    change (j.appIso W.unop).inv 1 = 1
    exact map_one _
  have h2 : ((M.unitHomEquiv.symm (s i)).val.app (op (j ''ᵁ W.unop)) (1 : X.ringCatSheaf.obj.obj (op (j ''ᵁ W.unop)))) =
      (s i).val (op (j ''ᵁ W.unop)) := by
    have := congrArg (fun t => t.val (op (j ''ᵁ W.unop))) (M.unitHomEquiv.apply_symm_apply (s i))
    exact this
  change ((Scheme.Modules.restrictFunctor j).map (M.unitHomEquiv.symm (s i))).val.app W
    ((Scheme.Modules.restrictUnitIso j).inv.val.app W (1 : U.ringCatSheaf.obj.obj W)) = (s i).val (op (j ''ᵁ W.unop))
  rw [h1]
  exact h2

omit [IsOpenImmersion j] in
/-- Two successive restriction maps of a presheaf of rings compose to the restriction map. -/
theorem presheaf_map_map_apply {T : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} T)
    {A B C : (Opens T)ᵒᵖ} (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C) (x : F.obj A) :
    F.map q (F.map p x) = F.map r x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

omit [IsOpenImmersion j] in
/-- Three successive restriction maps of a presheaf of rings compose to the restriction map. -/
theorem presheaf_map_map_map_apply {T : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} T)
    {A B C D : (Opens T)ᵒᵖ} (p : A ⟶ B) (q : B ⟶ C) (r : C ⟶ D) (s : A ⟶ D) (x : F.obj A) :
    F.map r (F.map q (F.map p x)) = F.map s x := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

/-- The inverse of `j.appIso W` sends the restriction of `j^♯ c` to the restriction of `c`. -/
theorem appIso_inv_res_appTop (c : Γ(X, ⊤)) (W : U.Opens) :
    (j.appIso W).inv (U.presheaf.map (homOfLE le_top).op (j.appTop c)) =
      X.presheaf.map (homOfLE le_top).op c := by
  have h1 := ConcreteCategory.congr_hom
    (j.appIso_inv_naturality (homOfLE (le_top : W ≤ ⊤)).op) (j.appTop c)
  have h2 := ConcreteCategory.congr_hom (j.app_appIso_inv ⊤) c
  simp only [ConcreteCategory.comp_apply] at h1 h2
  refine h1.trans ?_
  erw [h2]
  exact presheaf_map_map_apply X.presheaf _ _ _ c

variable {Y V : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ V) (i : V ⟶ Y) [IsOpenImmersion i]
  (w : j ≫ f = g ≫ i)

/-- Under the locality isomorphism `Ω_{U/V} ≅ Ω_{X/Y}|_U`, the global section `d (j^♯ c)` goes
to the restriction of `d c`. -/
theorem sectionsMap_restrictIso_hom_dSection (c : Γ(X, ⊤)) :
    SheafOfModules.sectionsMap (RelDiffLocal.restrictIso f j g i w).hom
      (Scheme.relativeDifferentialsDSection g (j.appTop c)) =
      restrictSection j _ (Scheme.relativeDifferentialsDSection f c) := by
  let r := RelDiffLocal.restrictCorepresentable f j g i w
  have he : Scheme.relativeDifferentialsHomEquiv g _ (RelDiffLocal.restrictIso f j g i w).hom =
      r.homEquiv (𝟙 _) := by
    change (Scheme.relativeDifferentialsHomEquiv g _)
      ((Scheme.relativeDifferentialsHomEquiv g _).symm (r.homEquiv (𝟙 _))) = _
    exact (Scheme.relativeDifferentialsHomEquiv g _).apply_symm_apply _
  rw [Scheme.relativeDifferentialsHomEquiv_apply] at he
  refine PresheafOfModules.sections_ext _ _ fun W => ?_
  have h3 := PresheafOfModules.Derivation.congr_d he
    (U.presheaf.map W.unop.leTop.op (j.appTop c))
  refine h3.trans ?_
  change RelDiffLocal.resD (Scheme.relativeDifferentialsHomEquiv f _
    ((Scheme.Modules.restrictAdjunction j).homEquiv _ _ (𝟙 _))) W.unop
      (U.presheaf.map W.unop.leTop.op (j.appTop c)) = _
  rw [Adjunction.homEquiv_id, Scheme.relativeDifferentialsHomEquiv_apply]
  unfold RelDiffLocal.resD
  erw [PresheafOfModules.Derivation.postcomp_d_apply, appIso_inv_res_appTop]
  let D := Scheme.relativeDifferentialsDerivation f
  change (Scheme.relativeDifferentials f).val.map _ ((Scheme.relativeDifferentials f).val.map
    (homOfLE (j.image_preimage_le (j ''ᵁ W.unop))).op (D.d (X := op (j ''ᵁ W.unop))
      (X.presheaf.map (homOfLE le_top).op c))) = D.d (X.presheaf.map (j ''ᵁ W.unop).leTop.op c)
  refine (congrArg ((Scheme.relativeDifferentials f).val.map _) (D.d_map _ _).symm).trans ?_
  refine (D.d_map _ _).symm.trans ?_
  exact congrArg D.d (presheaf_map_map_map_apply X.presheaf _ _ _ _ c)

end AlgebraicGeometry.AffineSpaceDifferentials

namespace AlgebraicGeometry.AffineSpaceDifferentials

variable (σ : Type u) {Y : Scheme.{u}} (V : Y.affineOpens)

/-- The chart `Spec Γ(Y, V)[x_i] ⟶ 𝔸(σ; Y)` of affine space over an affine open `V` of `Y`. -/
noncomputable def chart : Spec (CommRingCat.of (MvPolynomial σ Γ(Y, (V : Y.Opens)))) ⟶ 𝔸(σ; Y) :=
  (AffineSpace.SpecIso σ Γ(Y, (V : Y.Opens))).inv ≫ AffineSpace.map σ V.2.fromSpec

instance : IsOpenImmersion (chart σ V) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (AffineSpace.map σ V.2.fromSpec) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (AffineSpace.isPullback_map (n := σ) V.2.fromSpec).flip
      inferInstance
  unfold chart
  infer_instance

/-- The chart lies over the affine open `V`. -/
theorem chart_over : chart σ V ≫ 𝔸(σ; Y) ↘ Y =
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, (V : Y.Opens))
      (MvPolynomial σ Γ(Y, (V : Y.Opens))))) ≫ V.2.fromSpec := by
  simp [chart, MvPolynomial.algebraMap_eq]

/-- The coordinate functions restrict to the polynomial variables on a chart. -/
theorem chart_appTop_coord (k : σ) :
    (chart σ V).appTop (AffineSpace.coord Y k) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial σ Γ(Y, (V : Y.Opens))))).inv
        (MvPolynomial.X k) := by
  change (AffineSpace.SpecIso σ _).inv.appTop
    ((AffineSpace.map σ V.2.fromSpec).appTop (AffineSpace.coord Y k)) = _
  rw [AffineSpace.map_appTop_coord, AffineSpace.SpecIso_inv_appTop_coord]

/-- The chart over `V` contains every point of affine space lying over `V`. -/
theorem mem_range_chart (x : 𝔸(σ; Y)) (hx : (𝔸(σ; Y) ↘ Y) x ∈ (V : Y.Opens)) :
    x ∈ (chart σ V).opensRange := by
  have hx' : (𝔸(σ; Y) ↘ Y) x ∈ Set.range V.2.fromSpec := by
    rw [V.2.range_fromSpec]
    exact hx
  obtain ⟨y, hy⟩ := hx'
  have hpb := AffineSpace.isPullback_map (n := σ) V.2.fromSpec
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
  refine ⟨(AffineSpace.SpecIso σ _).hom (hpb.isoPullback.inv z), ?_⟩
  rw [chart, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (AffineSpace.SpecIso σ _).hom,
    Iso.hom_inv_id]
  change (AffineSpace.map σ V.2.fromSpec) (hpb.isoPullback.inv z) = x
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz]

end AlgebraicGeometry.AffineSpaceDifferentials

namespace AlgebraicGeometry

open AffineSpaceDifferentials

variable (σ : Type u) (Y : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
/-- Hartshorne II, Example 8.12.1, for coordinates indexed by any type `σ` (Hartshorne takes
`n` coordinates, see `Scheme.relativeDifferentials_affineSpaceOver_free_rank`): for every scheme
`Y`, the relative differential sheaf of affine space `𝔸(σ; Y) ⟶ Y` is free on the global sections
`d x_i` of the coordinates. -/
theorem Scheme.relativeDifferentials_affineSpaceOver_free :
    IsIso ((Scheme.relativeDifferentials (𝔸(σ; Y) ↘ Y)).freeHomEquiv.symm
      (fun k => Scheme.relativeDifferentialsDSection _ (AffineSpace.coord Y k))) := by
  set φ := (Scheme.relativeDifferentials (𝔸(σ; Y) ↘ Y)).freeHomEquiv.symm
      (fun k => Scheme.relativeDifferentialsDSection _ (AffineSpace.coord Y k))
  refine Hartshorne.Ringed.modules_isIso_of_locally_bijective (R := (𝔸(σ; Y)).sheaf) φ
    fun x => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((𝔸(σ; Y) ↘ Y) x))
      isOpen_univ
  let V' : Y.affineOpens := ⟨V, hV⟩
  let A := Γ(Y, V)
  let j := chart σ V'
  let g := Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial σ A)))
  let e := RelDiffLocal.restrictIso (𝔸(σ; Y) ↘ Y) j g V'.2.fromSpec (chart_over σ V')
  have hiso : IsIso ((Scheme.Modules.restrictFunctor j).map φ) := by
    have h := restrictFreeIso_inv_comp_map_freeHomEquiv_symm j _
      (fun k => Scheme.relativeDifferentialsDSection (𝔸(σ; Y) ↘ Y) (AffineSpace.coord Y k))
    have h2 : (Scheme.Modules.restrictFunctor j).map φ = (Scheme.Modules.restrictFreeIso j σ).hom ≫
        ((Scheme.relativeDifferentials g).freeHomEquiv.symm
          (fun k => Scheme.relativeDifferentialsDSection g
            ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial σ A))).inv (MvPolynomial.X k))) ≫
          e.hom) := by
      rw [← Iso.inv_comp_eq, h, SheafOfModules.freeHomEquiv_symm_comp]
      congr 1
      funext k
      rw [← chart_appTop_coord σ V' k]
      exact (sectionsMap_restrictIso_hom_dSection j _ g _ _ _).symm
    have := Scheme.relativeDifferentials_mvPolynomial_free A σ
    rw [h2]
    infer_instance
  refine ⟨j.opensRange, mem_range_chart σ V' x hxV, fun W hW => ?_⟩
  obtain ⟨W', rfl⟩ : ∃ W' : (Spec (CommRingCat.of (MvPolynomial σ A))).Opens, j ''ᵁ W' = W :=
    ⟨j ⁻¹ᵁ W, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hW]⟩
  have : IsIso (((Scheme.Modules.restrictFunctor j).map φ).val.app (op W')) :=
    Functor.map_isIso (SheafOfModules.forget (Spec (CommRingCat.of (MvPolynomial σ A))).ringCatSheaf ⋙
      PresheafOfModules.evaluation _ (op W')) ((Scheme.Modules.restrictFunctor j).map φ)
  exact ConcreteCategory.bijective_of_isIso
    ((forget₂ _ AddCommGrpCat).map (((Scheme.Modules.restrictFunctor j).map φ).val.app (op W')))

/-- Hartshorne II, Example 8.12.1 for `𝔸ⁿ_Y`: for every scheme `Y`, `Ω_{𝔸ⁿ_Y/Y}` is a free
`𝒪_{𝔸ⁿ_Y}`-module of rank `n`, generated by the global sections `d x₁, …, d xₙ`. -/
theorem Scheme.relativeDifferentials_affineSpaceOver_free_rank (n : ℕ) :
    IsIso ((Scheme.relativeDifferentials (𝔸(ULift.{u} (Fin n); Y) ↘ Y)).freeHomEquiv.symm
      (fun k => Scheme.relativeDifferentialsDSection _ (AffineSpace.coord Y k))) :=
  Scheme.relativeDifferentials_affineSpaceOver_free (ULift.{u} (Fin n)) Y

end AlgebraicGeometry
