/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentExtensionAffine
import Hartshorne.Scheme.CoherentFreeLocus
import Hartshorne.Scheme.FinitePushforwardCoherent
import Hartshorne.Scheme.CoherentPushforwardCounterexample
import Hartshorne.Scheme.Differentials.AffineSpaceDifferentials
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# A generic finite-module frame

Hartshorne, *Algebraic Geometry*, III, Exercise 4.2(a) (p. 222).

Let `f : X ⟶ Y` be a finite surjective morphism of Noetherian schemes, with `Y` integral. There
are a coherent `𝒪_X`-module `M`, an integer `r > 0` and a morphism `𝒪_Y^r ⟶ f_* M` which is an
isomorphism at the generic point of `Y` (`Hartshorne.exists_genericFiniteModuleFrame`).

## Proof

The coherent sheaf `f_* 𝒪_X` has a free stalk at the generic point `η` of `Y` (a vector space
over the function field), so it is free on an affine open `W = Spec A ∋ η`. Let
`B = Γ(f⁻¹ W, 𝒪_X)`, a free `A`-module with a basis `b₁, …, b_r`; `r > 0` as `f⁻¹ W ≠ ∅`.

The `bᵢ` are global sections of the quasi-coherent sheaf `E = j_* (𝒪_X|_{f⁻¹ W})`, where `j` is
the inclusion of `f⁻¹ W`. Their span `M ⊆ E` is coherent (`isCoherent_spanSheaf`), and has the
`bᵢ` as global sections; they give `α : 𝒪_Y^r ⟶ f_* M`. Over `W`, the sections of `f_* M` are
`M(f⁻¹ W) ⊆ E(f⁻¹ W) = B`. This inclusion is onto since it contains the basis, so the `bᵢ` form
an `A`-basis of `Γ(W, f_* M)`. A morphism from a free sheaf on `Spec A` to a quasi-coherent sheaf
given by a basis of the global sections is an isomorphism
(`freeHomEquiv_symm_isIso_of_basis`). Hence `α|_W` is an isomorphism, and so is its stalk at `η`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open AlgebraicGeometry.SpecKaehler (tildeSection app_toOpen)

namespace Hartshorne

namespace ChevalleyFrame

/-! ### Free sheaves on an affine scheme -/

/-- A morphism `M̃ ⟶ G` evaluated on the global section of `M̃` attached to `m`. -/
theorem app_top_toOpen {R : CommRingCat.{u}} {N : ModuleCat.{u} R} {G : (Spec R).Modules}
    (α : tilde N ⟶ G) (m : N) :
    α.val.app (op ⊤) ((tilde.toOpen N ⊤).hom m) = (tilde.adjunction.homEquiv N G α) m :=
  (ConcreteCategory.congr_hom (tilde.adjunction.homEquiv_unit _ _ α) m).symm

set_option backward.isDefEq.respectTransparency false in
/-- On `Spec R`, the morphism `𝒪^{(ι)} ⟶ Ñ` given by a basis of `N` is an isomorphism. -/
theorem tilde_freeHomEquiv_symm_isIso {R : CommRingCat.{u}} {N : ModuleCat.{u} R} {ι : Type u}
    (b : Module.Basis ι R N) :
    IsIso ((tilde N).freeHomEquiv.symm (fun i => tildeSection (b i))) := by
  let F : (Spec R).Modules := SheafOfModules.free ι
  let N' := (moduleSpecΓFunctor (R := R)).obj F
  let lin : N ⟶ N' :=
    ConcreteCategory.ofHom (C := ModuleCat R) (X := N) (Y := N')
      ((Finsupp.linearCombination R (M := N')
        (fun i => ((SheafOfModules.freeSection i : F.sections).val (op ⊤) : N'))) ∘ₗ
        b.repr.toLinearMap)
  have hlin : ∀ i, lin (b i) = (SheafOfModules.freeSection i : F.sections).val (op ⊤) := by
    intro i
    change Finsupp.linearCombination _ _ (b.repr (b i)) = _
    rw [b.repr_self, Finsupp.linearCombination_single, one_smul]
  let G := (tilde N).freeHomEquiv.symm (fun i => tildeSection (b i))
  let H : tilde N ⟶ F := (tilde.adjunction.homEquiv N F).symm lin
  have hH : ∀ (U : (Spec R).Opens) (m : N),
      H.val.app (op U) ((tilde.toOpen N U).hom m) = F.val.map U.leTop.op (lin m) := by
    intro U m
    refine (app_toOpen H U m).trans ?_
    rw [Equiv.apply_symm_apply]
  refine ⟨H, ?_, ?_⟩
  · apply F.freeHomEquiv.injective
    funext i
    rw [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
    refine PresheafOfModules.sections_ext _ _ fun U => ?_
    refine (hH U.unop _).trans ?_
    rw [hlin]
    exact PresheafOfModules.sections_property _ _
  · apply (tilde.adjunction.homEquiv N _).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    apply ModuleCat.hom_ext
    refine b.ext fun i => ?_
    change G.val.app (op ⊤) (lin _) = _
    rw [hlin, ← app_top_toOpen]
    exact congrArg (fun s => PresheafOfModules.sections.eval s (op ⊤))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection _ i)

set_option backward.isDefEq.respectTransparency false in
/-- On `Spec R`, a morphism `𝒪^{(ι)} ⟶ P` to a quasi-coherent module, given by global sections
`tᵢ` whose values form a basis of `Γ(P)`, is an isomorphism. -/
theorem freeHomEquiv_symm_isIso_of_basis {R : CommRingCat.{u}} (P : (Spec R).Modules)
    [IsIso P.fromTildeΓ] {ι : Type u} (t : ι → P.sections)
    (b : Module.Basis ι R ((moduleSpecΓFunctor (R := R)).obj P))
    (hb : ∀ i, b i = (t i).val (op ⊤)) :
    IsIso (P.freeHomEquiv.symm t) := by
  have := tilde_freeHomEquiv_symm_isIso b
  have h : P.freeHomEquiv.symm t =
      (tilde ((moduleSpecΓFunctor (R := R)).obj P)).freeHomEquiv.symm
        (fun i => tildeSection (b i)) ≫ P.fromTildeΓ := by
    rw [SheafOfModules.freeHomEquiv_symm_comp]
    congr 1
    funext i
    refine PresheafOfModules.sections_ext _ _ fun U => ?_
    have h1 := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app P U.unop) (b i)
    refine Eq.trans ?_ h1.symm
    rw [hb]
    exact (PresheafOfModules.sections_property _ _).symm
  rw [h]
  infer_instance

/-! ### A free affine chart for `f_* 𝒪_X` -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `f_* 𝒪_X`. -/
noncomputable abbrev pushStructure : Y.Modules :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)

/-- For a finite morphism to an integral Noetherian scheme, `f_* 𝒪_X` has finite free sections
over some affine open containing the generic point. -/
theorem exists_affine_free [IsFinite f] [IsIntegral Y] [IsNoetherian Y] [IsNoetherian X] :
    ∃ W : Y.affineOpens, genericPoint Y ∈ (W : Y.Opens) ∧
      Module.Free Γ(Y, (W : Y.Opens)) Γ(specRestriction (pushStructure f) W, ⊤) ∧
      Module.Finite Γ(Y, (W : Y.Opens)) Γ(specRestriction (pushStructure f) W, ⊤) := by
  have hF : IsCoherent (pushStructure f) :=
    isCoherent_pushforward_of_isFinite f (isCoherent_structureSheafModule X)
  have hx : Module.Free (Y.presheaf.stalk (genericPoint Y))
      ((pushStructure f).presheaf.stalk (genericPoint Y)) := by
    exact Module.Free.of_divisionRing Y.functionField _
  obtain ⟨V0, hη, I, ⟨β⟩⟩ := exists_isFree_restrict_of_free_stalk _ hF _ hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, hVV0⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hη V0.2
  replace hVV0 : V ≤ V0 := hVV0
  let W : Y.affineOpens := ⟨V, hV⟩
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let j : Spec Γ(Y, V) ⟶ V0 := hV.isoSpec.inv ≫ Y.homOfLE hVV0
  have hj : j ≫ V0.ι = hV.fromSpec := by simp [j]; rfl
  let β' : (pushStructure f).restrict hV.fromSpec ≅ SheafOfModules.free I :=
    (Scheme.Modules.restrictFunctorCongr hj).symm.app _ ≪≫
      (Scheme.Modules.restrictFunctorComp j V0.ι).app _ ≪≫
      (Scheme.Modules.restrictFunctor j).mapIso β ≪≫ Scheme.Modules.restrictFreeIso j I
  let e : Γ(specRestriction (pushStructure f) W, ⊤) ≃ₗ[Γ(Y, V)] (I →₀ Γ(Y, V)) :=
    (moduleSpecΓFunctor.mapIso (β' ≪≫ (tildeFinsupp I).symm) ≪≫
      (tilde.toTildeΓNatIso.app (ModuleCat.of Γ(Y, V) (I →₀ Γ(Y, V)))).symm).toLinearEquiv
  refine ⟨W, hηV, Module.Free.of_equiv e.symm, ?_⟩
  exact (finite_specRestriction_iff _ W).mpr (forall_affine_finite_of_isCoherent _ hF W).1

end ChevalleyFrame

end Hartshorne
