/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ChevalleyGenericApproximationGlue

/-!
# Generic coherent pushforward approximation

Hartshorne, *Algebraic Geometry*, III, Exercise 4.2(b) (p. 223).

Let `f : X ⟶ Y` be a finite morphism of Noetherian schemes with `Y` integral, `M` a coherent
`𝒪_X`-module and `α : 𝒪_Y^r ⟶ f_* M` a morphism which is an isomorphism at the generic point `η`
of `Y`. For every coherent `𝒪_Y`-module `F` there are a coherent `𝒪_X`-module `G` and a morphism
`f_* G ⟶ F^r` which is an isomorphism at `η` (`Hartshorne.exists_genericCoherentApproximation`).

## Proof

`G` is the module of `Hartshorne.ChevalleyApprox.approx`: over an affine open `U ⊆ Y` it is the
sheaf on `f⁻¹ U` associated to `Hom_{Γ(U, 𝒪_Y)}(Γ(U, f_* M), Γ(U, F))`, the sections of the
sheaf `ℋom(f_* M, F)` with their `f_* 𝒪_X`-module structure. The global sections `mᵢ` of
`f_* M` defining `α` give the evaluation morphisms `h ↦ h(mᵢ|_U) : f_* G ⟶ F`.

Near `η` the `mᵢ` form a basis of `Γ(U, f_* M)`: the sections of `𝒪_Y^r` over an affine open
have the basis of the standard sections, the stalk map of `α` at `η` is the localization of
`α` on sections over an affine neighbourhood, and a map of finitely presented modules which is
bijective after localizing at a prime is bijective after inverting a single element. On such
`U` the map `h ↦ (h(mᵢ|_U))ᵢ` is bijective, so the evaluation morphisms combine to a morphism
`f_* G ⟶ F^r` which is bijective on sections over small neighbourhoods of `η`, hence an
isomorphism on stalks at `η`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

noncomputable section

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace Hartshorne

namespace ChevalleyApprox

/-! ### Sections of a finite direct sum -/

section Biproduct

variable {Y : Scheme.{u}}

/-- Evaluation of morphisms of module sheaves on a section, as an additive map. -/
def appAddHom {M N : Y.Modules} (U : Y.Opens) (x : Γ(M, U)) : (M ⟶ N) →+ Γ(N, U) where
  toFun φ := φ.app U x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The sections of `F^r = ⨁ F` over an open are the `r`-tuples of sections of `F`. -/
theorem biproduct_sections_bijective (F : Y.Modules) (r : ℕ) (U : Y.Opens) :
    Function.Bijective fun x : Γ((⨁ fun _ : Fin r => F), U) =>
      fun k => (biproduct.π (fun _ : Fin r => F) k).app U x := by
  have htot : ∀ x : Γ((⨁ fun _ : Fin r => F), U),
      x = ∑ k, (biproduct.ι (fun _ : Fin r => F) k).app U
        ((biproduct.π (fun _ : Fin r => F) k).app U x) := by
    intro x
    have h := congrArg (fun φ => appAddHom U x φ) (biproduct.total (f := fun _ : Fin r => F))
    simp only [map_sum] at h
    exact h.symm
  have hιπ : ∀ (k j : Fin r) (t : Γ(F, U)),
      (biproduct.π (fun _ : Fin r => F) j).app U ((biproduct.ι (fun _ : Fin r => F) k).app U t) =
        if k = j then t else 0 := by
    intro k j t
    have h := congrArg (fun φ => appAddHom U t φ) (biproduct.ι_π (fun _ : Fin r => F) k j)
    change (biproduct.ι (fun _ : Fin r => F) k ≫ biproduct.π (fun _ : Fin r => F) j).app U t = _ at h
    refine (Eq.trans rfl h).trans ?_
    split_ifs with hkj
    · subst hkj
      rfl
    · rfl
  refine ⟨fun x y hxy => ?_, fun t => ?_⟩
  · rw [htot x, htot y]
    exact Finset.sum_congr rfl fun k _ => congrArg _ (congrFun hxy k)
  · refine ⟨∑ k, (biproduct.ι (fun _ : Fin r => F) k).app U (t k), funext fun j => ?_⟩
    change appAddHom U _ (biproduct.π (fun _ : Fin r => F) j) = _
    simp only [appAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, hιπ,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Biproduct

/-! ### Stalk isomorphisms from bijectivity on small neighbourhoods -/

/-- A morphism of module sheaves which is bijective on sections over arbitrarily small
neighbourhoods of a point `y` is an isomorphism on stalks at `y`. -/
theorem isIso_stalk_of_forall_exists_bijective {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    (y : Y) (h : ∀ W : Y.Opens, y ∈ W →
      ∃ V : Y.Opens, y ∈ V ∧ V ≤ W ∧ Function.Bijective (φ.app V)) :
    IsIso ((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro s t hst
    obtain ⟨V, hxV, s, rfl⟩ := M.presheaf.exists_germ_eq s
    obtain ⟨V', hxV', t, rfl⟩ := M.presheaf.exists_germ_eq t
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map φ.mapPresheaf _ =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map φ.mapPresheaf _ at hst
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
    obtain ⟨W, hxW, iV, iV', heq⟩ := N.presheaf.germ_eq y hxV hxV' _ _ hst
    obtain ⟨W', hxW', hW'W, hbij⟩ := h W hxW
    have h1 : φ.app W' (M.presheaf.map (homOfLE (hW'W.trans iV.le)).op s) =
        φ.app W' (M.presheaf.map (homOfLE (hW'W.trans iV'.le)).op t) := by
      have h2 := congrArg (N.presheaf.map (homOfLE hW'W).op) heq
      change N.presheaf.map (homOfLE hW'W).op (N.presheaf.map (homOfLE iV.le).op (φ.app V s)) =
        N.presheaf.map (homOfLE hW'W).op (N.presheaf.map (homOfLE iV'.le).op (φ.app V' t)) at h2
      rw [DirectedModuleGluing.pmap_map N _ _ (homOfLE (hW'W.trans iV.le)).op,
        DirectedModuleGluing.pmap_map N _ _ (homOfLE (hW'W.trans iV'.le)).op] at h2
      have hn : ∀ {A B : Y.Opens} (hAB : A ≤ B) (x : Γ(M, B)),
          φ.app A (M.presheaf.map (homOfLE hAB).op x) =
            N.presheaf.map (homOfLE hAB).op (φ.app B x) :=
        fun hAB x => ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hAB).op) x
      rw [hn, hn]
      exact h2
    have h3 := hbij.1 h1
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (hW'W.trans iV.le)) y hxW',
      ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (hW'W.trans iV'.le)) y hxW']
    exact congrArg (M.presheaf.germ W' y hxW') h3
  · intro t
    obtain ⟨V, hxV, t, rfl⟩ := N.presheaf.exists_germ_eq t
    obtain ⟨W', hxW', hW'V, hbij⟩ := h V hxV
    obtain ⟨s, hs⟩ := hbij.2 (N.presheaf.map (homOfLE hW'V).op t)
    refine ⟨M.presheaf.germ W' y hxW' s, ?_⟩
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map φ.mapPresheaf _ = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change N.presheaf.germ W' y hxW' (φ.app W' s) = _
    rw [hs, TopCat.Presheaf.germ_res_apply]

/-! ### Sections of free modules over affine opens -/

section Free

/-- The value of a global section of a module sheaf over an open. -/
theorem sectionsMap_val {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) (s : M.sections)
    (U : Y.Opens) : (SheafOfModules.sectionsMap φ s).val (op U) = φ.app U (s.val (op U)) := rfl

/-- On `Spec R`, the global sections of `𝒪^{(I)}` have the basis of the standard sections. -/
theorem exists_basis_free_top {R : CommRingCat.{u}} (I : Type u) :
    ∃ b : Module.Basis I R ((moduleSpecΓFunctor (R := R)).obj (SheafOfModules.free I)),
      ∀ i, b i = (SheafOfModules.freeSection (R := (Spec R).ringCatSheaf) i).val (op ⊤) := by
  let N := ModuleCat.of R (I →₀ R)
  let bs : Module.Basis I R N := Finsupp.basisSingleOne
  let G : (SheafOfModules.free I : (Spec R).Modules) ⟶ tilde N :=
    (tilde N).freeHomEquiv.symm (fun i => Scheme.Modules.tildeSection (bs i))
  have hG : IsIso G := Scheme.Modules.isIso_freeHomEquiv_symm_tildeSection bs
  let e : (moduleSpecΓFunctor (R := R)).obj (SheafOfModules.free I) ≃ₗ[R] N :=
    (moduleSpecΓFunctor.mapIso (@asIso _ _ _ _ G hG)).toLinearEquiv ≪≫ₗ (tilde.isoTop N).symm.toLinearEquiv
  refine ⟨bs.map e.symm, fun i => ?_⟩
  rw [Module.Basis.map_apply]
  apply e.injective
  rw [e.apply_symm_apply]
  symm
  have h := congrArg (fun s => s.val (op ⊤))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun i => Scheme.Modules.tildeSection (bs i)) i)
  change (tilde.isoTop N).inv (Scheme.Modules.Hom.app G ⊤ _) = bs i
  have h' : Scheme.Modules.Hom.app G ⊤ ((SheafOfModules.freeSection (R := (Spec R).ringCatSheaf) i).val (op ⊤)) =
      (tilde.toOpen N ⊤).hom (bs i) := h
  rw [h']
  exact (tilde.isoTop N).hom_inv_id_apply (bs i)

/-- Over an affine open `U`, the sections of `𝒪^{(I)}` have the basis of the restrictions of
the standard sections. -/
theorem exists_basis_free_sections {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (I : Type u) :
    ∃ b : Module.Basis I Γ(Y, U) Γ((show Y.Modules from SheafOfModules.free I), U),
      ∀ i, b i = (SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op U) := by
  obtain ⟨b0, hb0⟩ := exists_basis_free_top (R := Γ(Y, U)) I
  let E : Y.Modules := SheafOfModules.free I
  let e1 := CoherentAux.sectionsEquiv E hU
  let e2 : (moduleSpecΓFunctor (R := Γ(Y, U))).obj (E.restrict hU.fromSpec) ≃ₗ[Γ(Y, U)]
      (moduleSpecΓFunctor (R := Γ(Y, U))).obj (SheafOfModules.free I) :=
    (moduleSpecΓFunctor.mapIso (Scheme.Modules.restrictFreeIso hU.fromSpec I)).toLinearEquiv
  let e : Γ(E, U) ≃ₗ[Γ(Y, U)] (moduleSpecΓFunctor (R := Γ(Y, U))).obj (SheafOfModules.free I) :=
    e1.trans e2
  refine ⟨b0.map e.symm, fun i => ?_⟩
  refine (LinearEquiv.symm_apply_eq e).mpr ?_
  refine (hb0 i).trans ?_
  have h3 : e ((SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op U)) =
      (Scheme.Modules.restrictFreeIso hU.fromSpec I).hom.app ⊤
        ((Scheme.Modules.restrictSection hU.fromSpec E
          (SheafOfModules.freeSection (R := Y.ringCatSheaf) i)).val (op ⊤)) := by
    change (Scheme.Modules.restrictFreeIso hU.fromSpec I).hom.app ⊤ (e1 _) = _
    congr 1
    exact PresheafOfModules.sections_property _ _
  refine Eq.trans ?_ h3.symm
  have hinv : (Scheme.Modules.restrictFreeIso hU.fromSpec I).inv =
      (E.restrict hU.fromSpec).freeHomEquiv.symm
        (fun i => Scheme.Modules.restrictSection hU.fromSpec E
          (SheafOfModules.freeSection (R := Y.ringCatSheaf) i)) := by
    have := Scheme.Modules.restrictFreeIso_inv_comp_map_freeHomEquiv_symm hU.fromSpec E
      (fun i => SheafOfModules.freeSection (R := Y.ringCatSheaf) i)
    have h1 : E.freeHomEquiv.symm (fun i => SheafOfModules.freeSection (R := Y.ringCatSheaf) i) =
        𝟙 E := E.freeHomEquiv.symm_apply_apply (𝟙 E)
    rw [h1] at this
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at this
    exact this
  have h2 : (Scheme.Modules.restrictFreeIso hU.fromSpec I).inv.app ⊤
      ((SheafOfModules.freeSection (R := (Spec Γ(Y, U)).ringCatSheaf) i).val (op ⊤)) =
      (Scheme.Modules.restrictSection hU.fromSpec E
        (SheafOfModules.freeSection (R := Y.ringCatSheaf) i)).val (op ⊤) := by
    have := congrArg (fun s => s.val (op ⊤))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
        (fun i => Scheme.Modules.restrictSection hU.fromSpec E
          (SheafOfModules.freeSection (R := Y.ringCatSheaf) i)) i)
    rw [← hinv] at this
    exact this
  rw [← h2]
  have h4 := ConcreteCategory.congr_hom (congrArg (fun k => Scheme.Modules.Hom.app k ⊤)
    (Scheme.Modules.restrictFreeIso hU.fromSpec I).inv_hom_id)
    ((SheafOfModules.freeSection (R := (Spec Γ(Y, U)).ringCatSheaf) i).val (op ⊤))
  exact h4.symm

end Free

/-! ### Spreading out an isomorphism on stalks -/

section Spread

variable {Y : Scheme.{u}}

/-- Stalk maps of morphisms of module sheaves are linear over the local ring. -/
theorem stalk_map_smul {M N : Y.Modules} (φ : M ⟶ N) (y : Y) (c : Y.presheaf.stalk y)
    (z : M.presheaf.stalk y) :
    ((Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ
      (c • z) : N.presheaf.stalk y) =
      c • (show N.presheaf.stalk y from
        (Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ z) := by
  obtain ⟨V, hyV, s, rfl⟩ := M.presheaf.exists_germ_eq z
  obtain ⟨V', hyV', a, rfl⟩ := Y.presheaf.exists_germ_eq c
  let W := V ⊓ V'
  have hyW : y ∈ W := ⟨hyV, hyV'⟩
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE inf_le_left : W ⟶ V) y hyW,
    ← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE inf_le_right : W ⟶ V') y hyW]
  erw [← schemeModules_germ_smul, TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [Scheme.Modules.Hom.app_smul, schemeModules_germ_smul]
  rfl

variable {I : Type u} (Q : Y.Modules) (α : (show Y.Modules from SheafOfModules.free I) ⟶ Q)

/-- `α` on sections over `U`, as a linear map. -/
def appₗ (U : Y.Opens) :
    Γ((show Y.Modules from SheafOfModules.free I), U) →ₗ[Γ(Y, U)] Γ(Q, U) where
  toFun := α.app U
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul α

theorem isIso_fromTildeΓ_free {U : Y.Opens} (hU : IsAffineOpen U) :
    IsIso ((show Y.Modules from SheafOfModules.free I).restrict hU.fromSpec).fromTildeΓ :=
  isIso_fromTildeΓ_iff.mpr
    ⟨_, ⟨tildeFinsupp I ≪≫ (Scheme.Modules.restrictFreeIso hU.fromSpec I).symm⟩⟩

/-- **Spreading out**: if `α : 𝒪^{(I)} ⟶ Q` (with `I` finite and `Q` quasi-coherent with finitely
presented sections) is an isomorphism on stalks at `y`, then `α` is bijective on sections over
every basic open of some affine neighbourhood of `y`. -/
theorem exists_bijective_app [Finite I] [Q.IsQuasicoherent]
    [hfp : ∀ V : Y.AffineZariskiSite, Module.FinitePresentation Γ(Y, V.1) Γ(Q, V.1)] (y : Y)
    (hα : IsIso ((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map α)) :
    ∃ W : Y.AffineZariskiSite, y ∈ W.1 ∧
      ∀ U : Y.AffineZariskiSite, U ≤ W → Function.Bijective (α.app U.1) := by
  obtain ⟨_, ⟨W0, hW0', rfl⟩, hyW0, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hW0 : IsAffineOpen W0 := hW0'
  let E : Y.Modules := SheafOfModules.free I
  let yW : W0 := ⟨y, hyW0⟩
  let S := (hW0.primeIdealOf yW).asIdeal.primeCompl
  have := isIso_fromTildeΓ_free (I := I) hW0
  have : IsIso (Q.restrict hW0.fromSpec).fromTildeΓ := inferInstance
  let _ : Algebra Γ(Y, W0) (Y.presheaf.stalk (yW : Y)) := Y.presheaf.algebra_section_stalk yW
  have := hW0.isLocalization_stalk yW
  let _ := FiberDimAux.stalkModuleSections E yW
  let _ := FiberDimAux.stalkModuleSections Q yW
  have hlE := FiberDimAux.isLocalizedModule_germₗ E hW0 inferInstance yW
  have hlQ := FiberDimAux.isLocalizedModule_germₗ Q hW0 inferInstance yW
  let Φ := (Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map α
  let Lη : E.presheaf.stalk y →ₗ[Γ(Y, W0)] Q.presheaf.stalk y :=
    { toFun := ConcreteCategory.hom Φ
      map_add' := map_add (ConcreteCategory.hom Φ)
      map_smul' := fun a z => stalk_map_smul α y (algebraMap Γ(Y, W0) (Y.presheaf.stalk (yW : Y)) a) z }
  have hcomp : Lη ∘ₗ FiberDimAux.germₗ E yW = FiberDimAux.germₗ Q yW ∘ₗ appₗ Q α W0 := by
    ext s
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map α.mapPresheaf _ = _
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl
  have hLη : Lη = IsLocalizedModule.map S (FiberDimAux.germₗ E yW) (FiberDimAux.germₗ Q yW)
      (appₗ Q α W0) := by
    refine IsLocalizedModule.ext S (FiberDimAux.germₗ E yW)
      (IsLocalizedModule.map_units (FiberDimAux.germₗ Q yW)) ?_
    rw [hcomp, IsLocalizedModule.map_comp]
  have hbij : Function.Bijective (IsLocalizedModule.map S (FiberDimAux.germₗ E yW)
      (FiberDimAux.germₗ Q yW) (appₗ Q α W0)) := by
    rw [← hLη]
    exact ConcreteCategory.bijective_of_isIso Φ
  obtain ⟨bE, -⟩ := exists_basis_free_sections hW0 I
  have : Module.Finite Γ(Y, W0) Γ(E, W0) := Module.Finite.of_basis bE
  have : Module.FinitePresentation Γ(Y, W0) Γ(Q, W0) := hfp ⟨W0, hW0⟩
  obtain ⟨g, hgS, hg⟩ := exists_bijective_map_powers S (FiberDimAux.germₗ E yW)
    (FiberDimAux.germₗ Q yW) (appₗ Q α W0) hbij
  have hyg : y ∈ Y.basicOpen g := by
    refine (Y.mem_basicOpen' g yW).mpr ?_
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk (yW : Y)) _ g).mpr hgS
  refine ⟨Scheme.AffineZariskiSite.basicOpen ⟨W0, hW0⟩ g, hyg, fun U hU => ?_⟩
  have hUW0 : U ≤ ⟨W0, hW0⟩ := hU.trans (Scheme.AffineZariskiSite.basicOpen_le ⟨W0, hW0⟩ g)
  have hle : U.1 ≤ W0 := Scheme.AffineZariskiSite.toOpens_mono hUW0
  obtain ⟨t0, ht0⟩ := hUW0
  have hU' : U.1 ≤ Y.basicOpen g := Scheme.AffineZariskiSite.toOpens_mono hU
  have ht : Y.basicOpen (g * t0) = U.1 := by
    rw [Y.basicOpen_mul, ht0]
    exact inf_eq_right.mpr hU'
  have hlocE := isLocalizedModule_resₗ E hW0 (g * t0) hle ht
  have hlocQ := isLocalizedModule_resₗ Q hW0 (g * t0) hle ht
  let _ := Module.compHom Γ(E, U.1) (Y.presheaf.map (homOfLE hle).op).hom
  let _ := Module.compHom Γ(Q, U.1) (Y.presheaf.map (homOfLE hle).op).hom
  let LU : Γ(E, U.1) →ₗ[Γ(Y, W0)] Γ(Q, U.1) :=
    { toFun := α.app U.1
      map_add' := map_add _
      map_smul' := fun a x => Scheme.Modules.Hom.app_smul α _ x }
  have hLU : LU = IsLocalizedModule.map (Submonoid.powers (g * t0)) (resₗ E hle) (resₗ Q hle)
      (appₗ Q α W0) := by
    refine IsLocalizedModule.ext (Submonoid.powers (g * t0)) (resₗ E hle)
      (IsLocalizedModule.map_units (resₗ Q hle)) ?_
    rw [IsLocalizedModule.map_comp]
    ext x
    exact ConcreteCategory.congr_hom (α.mapPresheaf.naturality (homOfLE hle).op) x
  have := (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective (resₗ E hle)
    (resₗ Q hle) (S := Submonoid.powers (g * t0)) (l := appₗ Q α W0)).mpr
    (hg (g * t0) (dvd_mul_right g t0))
  rw [← hLU] at this
  exact this

end Spread

/-! ### Bases near a point -/

/-- If `α : 𝒪_Y^r ⟶ Q` is an isomorphism on stalks at `y`, then over every basic open of some
affine neighbourhood of `y` the restrictions of the global sections defining `α` form a basis
of the sections of `Q`. -/
theorem exists_basis_near {Y : Scheme.{u}} {r : ℕ} (Q : Y.Modules)
    (α : (show Y.Modules from SheafOfModules.free (ULift.{u} (Fin r))) ⟶ Q) [Q.IsQuasicoherent]
    [∀ V : Y.AffineZariskiSite, Module.FinitePresentation Γ(Y, V.1) Γ(Q, V.1)] (y : Y)
    (hα : IsIso ((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map α)) :
    ∃ W : Y.AffineZariskiSite, y ∈ W.1 ∧ ∀ U : Y.AffineZariskiSite, U ≤ W →
      ∃ b : Module.Basis (Fin r) Γ(Y, U.1) Γ(Q, U.1), ∀ k,
        b k = Q.presheaf.map (homOfLE le_top).op ((Q.freeHomEquiv α (ULift.up k)).val (op ⊤)) := by
  obtain ⟨W, hyW, hW⟩ := exists_bijective_app Q α y hα
  refine ⟨W, hyW, fun U hU => ?_⟩
  obtain ⟨bE, hbE⟩ := exists_basis_free_sections U.2 (ULift.{u} (Fin r))
  let e := LinearEquiv.ofBijective (appₗ Q α U.1) (hW U hU)
  refine ⟨(bE.reindex Equiv.ulift).map e, fun k => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.reindex_apply, hbE]
  exact (PresheafOfModules.sections_property (Q.freeHomEquiv α (ULift.up k))
    (homOfLE (le_top : U.1 ≤ ⊤)).op).symm

/-! ### The combined evaluation morphism -/

theorem modules_map_bijective_of_eq {Z : Scheme.{u}} (P : Z.Modules) {A B : Z.Opens} (h : A ≤ B)
    (e : A = B) : Function.Bijective (P.presheaf.map (homOfLE h).op) := by
  subst e
  have : (homOfLE h).op = 𝟙 (op A) := rfl
  rw [this]
  exact ConcreteCategory.bijective_of_isIso _

theorem modules_map_refl {Z : Scheme.{u}} (P : Z.Modules) (A : Z.Opens) (x : Γ(P, A)) :
    P.presheaf.map (homOfLE (le_refl A)).op x = x := by
  have : (homOfLE (le_refl A)).op = 𝟙 (op A) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

section Eval

open QuasiCoherentAlgebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules) (F : Y.Modules)
  [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent] [F.IsQuasicoherent]
  [hfp : ∀ V : Y.AffineZariskiSite,
    Module.FinitePresentation Γ(Y, V.1) Γ((Scheme.Modules.pushforward f).obj M, V.1)]

/-- The evaluation morphisms at global sections `m₁, …, m_r` of `f_* M`, combined into a
morphism to `F^r`. -/
def evalSum {r : ℕ} (m : Fin r → Γ((Scheme.Modules.pushforward f).obj M, ⊤)) :
    (Scheme.Modules.pushforward (ofHom f).relSpecToBase).obj (homData f M F).glue ⟶
      ⨁ fun _ : Fin r => F :=
  biproduct.lift fun k => evalHom f M F (m k)

/-- Over an affine open `U` on which the restrictions of the `mᵢ` form a basis of the sections of
`f_* M`, the combined evaluation morphism is bijective on sections. -/
theorem bijective_evalSum_app {r : ℕ} (m : Fin r → Γ((Scheme.Modules.pushforward f).obj M, ⊤))
    (U : Y.AffineZariskiSite)
    (b : Module.Basis (Fin r) Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1))
    (hb : ∀ k, b k = ((Scheme.Modules.pushforward f).obj M).presheaf.map (homOfLE le_top).op (m k)) :
    Function.Bijective ((evalSum f M F m).app U.1) := by
  refine (Function.Bijective.of_comp_iff' (biproduct_sections_bijective F r U.1) _).mp ?_
  have hR := modules_map_bijective_of_eq (homData f M F).glue (piece_le f (le_refl U.1))
    (piece_eq f U)
  have hlin : Function.Bijective (homSec.lin f M F (U := U.1)) := Function.bijective_id
  have key : ((fun x k => (biproduct.π (fun _ : Fin r => F) k).app U.1 x) ∘
      (evalSum f M F m).app U.1) = (b.constr ℤ).symm ∘ homSec.lin f M F ∘ homOf f M F U ∘
        (homData f M F).glue.presheaf.map (homOfLE (piece_le f (le_refl U.1))).op := by
    funext s k
    change (evalSum f M F m ≫ biproduct.π (fun _ : Fin r => F) k).app U.1 s = _
    rw [evalSum, biproduct.lift_π, ← modules_map_refl F U.1 ((evalHom f M F (m k)).app U.1 s)]
    erw [evalHom_app_restrict f M F (m k) (V := U.1) ⟨U, le_refl U.1⟩ s]
    change _ = homSec.lin f M F (homOf f M F U ((homData f M F).glue.presheaf.map
      (homOfLE (piece_le f (le_refl U.1))).op s)) (b k)
    rw [hb]
    rfl
  rw [key]
  have hhom : Function.Bijective (homOf f M F U) :=
    ⟨homOf_injective f M F U, homOf_surjective f M F U⟩
  exact (b.constr ℤ).symm.bijective.comp (hlin.comp (hhom.comp hR))

/-- If `α : 𝒪_Y^r ⟶ f_* M` is an isomorphism on stalks at `y`, the combined evaluation morphism
at the global sections defining `α` is an isomorphism on stalks at `y`. -/
theorem isIso_stalk_evalSum (y : Y) {r : ℕ}
    (α : (show Y.Modules from SheafOfModules.free (ULift.{u} (Fin r))) ⟶
      (Scheme.Modules.pushforward f).obj M)
    (hα : IsIso ((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map α)) :
    IsIso ((Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      (evalSum f M F fun k =>
        (((Scheme.Modules.pushforward f).obj M).freeHomEquiv α (ULift.up k)).val (op ⊤))) := by
  obtain ⟨W, hyW, hW⟩ := exists_basis_near _ α y hα
  refine isIso_stalk_of_forall_exists_bijective _ y fun V hyV => ?_
  obtain ⟨g, hgV, hyg⟩ := W.2.exists_basicOpen_le ⟨y, hyV⟩ hyW
  refine ⟨Y.basicOpen g, hyg, hgV, ?_⟩
  obtain ⟨b, hb⟩ := hW (W.basicOpen g) (W.basicOpen_le g)
  exact bijective_evalSum_app f M F _ (W.basicOpen g) b hb

end Eval

end ChevalleyApprox

open ChevalleyApprox in
/-- **Generic coherent pushforward approximation** (Hartshorne III, Exercise 4.2(b)). Let
`f : X ⟶ Y` be a finite morphism with `Y` integral and Noetherian, `M` a coherent `𝒪_X`-module
and `α : 𝒪_Y^r ⟶ f_* M` an isomorphism at the generic point of `Y`. For every coherent
`𝒪_Y`-module `F` there are a coherent `𝒪_X`-module `G` and a morphism `f_* G ⟶ F^r` which is an
isomorphism at the generic point of `Y`. -/
theorem exists_genericCoherentApproximation {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [IsIntegral Y] [IsNoetherian Y] (M : X.Modules) (hM : IsCoherent M)
    (r : ℕ) (α : (SheafOfModules.free (ULift.{u} (Fin r)) : Y.Modules) ⟶
      (Scheme.Modules.pushforward f).obj M)
    (hα : IsIso ((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint Y)).map α))
    (F : Y.Modules) (hF : IsCoherent F) :
    ∃ (G : X.Modules) (_ : IsCoherent G)
      (β : (Scheme.Modules.pushforward f).obj G ⟶ ⨁ fun _ : Fin r => F),
      IsIso ((Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint Y)).map β) := by
  have hfM := isCoherent_pushforward_of_isFinite f hM
  have : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := hfM.isQuasicoherent
  have : F.IsQuasicoherent := hF.isQuasicoherent
  have hfin : ∀ U : Y.AffineZariskiSite,
      Module.Finite Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1) :=
    fun U => module_finite_pushforward_sections f hM ⟨U.1, U.2⟩
  have : ∀ U : Y.AffineZariskiSite, Module.Finite Γ(Y, U.1) Γ(F, U.1) :=
    fun U => (forall_affine_finite_of_isCoherent F hF ⟨U.1, U.2⟩).1
  have : ∀ U : Y.AffineZariskiSite,
      Module.FinitePresentation Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1) := by
    intro U
    have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
    have := hfin U
    exact Module.finitePresentation_of_finite _ _
  let m : Fin r → Γ((Scheme.Modules.pushforward f).obj M, ⊤) := fun k =>
    (((Scheme.Modules.pushforward f).obj M).freeHomEquiv α (ULift.up k)).val (op ⊤)
  refine ⟨approx f M F, isCoherent_approx f M F,
    (pushforwardApproxIso f M F).hom ≫ evalSum f M F m, ?_⟩
  have := isIso_stalk_evalSum f M F (genericPoint Y) α hα
  rw [Functor.map_comp]
  infer_instance

end Hartshorne
