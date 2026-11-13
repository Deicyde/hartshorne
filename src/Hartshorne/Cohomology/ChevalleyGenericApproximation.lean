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

end ChevalleyApprox

end Hartshorne
