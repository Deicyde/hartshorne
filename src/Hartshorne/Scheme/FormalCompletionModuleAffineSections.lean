/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletionAffineSections
import Hartshorne.Scheme.FormalCompletionModule
import Hartshorne.Scheme.IdealPowerProduct
import Hartshorne.Scheme.Differentials.ImmersionConormalSheaf

/-!
# Affine sections of the levels of a completed module

Hartshorne, *Algebraic Geometry*, II.9, completion of a coherent sheaf (p. 194) and the proof of
Proposition 9.4 (pp. 195–196).

Let `I` be a quasi-coherent ideal subsheaf of `𝒪_X` cutting out `Y`, with infinitesimal
neighbourhoods `Y_(n+1)` cut out by `I ^ (n + 1)`, and let `F` be a quasi-coherent `𝒪_X`-module.
The `n`-th level of the completion `F̂` is `(F / I ^ (n + 1) F)|_Y`, the pullback of
`F / I ^ (n + 1) F` to `Y_(n+1)`. On an affine open `U = Spec A` of `X`, with `I(U) ⊆ A` the
ideal of `I`, its sections over `U ∩ |Y|` are `Γ(U, F) / I(U) ^ (n + 1) Γ(U, F)`.

* `Hartshorne.closedImmersion_unit_app_surjective`: for a closed immersion `i : Z ⟶ X`, a
  quasi-coherent `𝒪_X`-module `G` and an affine open `V`, the unit `G ⟶ i_* i^* G` is surjective
  on sections over `V`.
* `Hartshorne.closedImmersion_unit_app_injective`: it is injective on sections over `V` when the
  kernel of `Γ(V, 𝒪_X) → Γ(i⁻¹ V, 𝒪_Z)` kills `Γ(V, G)`. On `V`, the unit is `m ↦ 1 ⊗ m` from
  `Γ(V, G)` to `Γ(i⁻¹ V, 𝒪_Z) ⊗ Γ(V, G)`.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionSectionsMap I F n U`: the canonical map
  `Γ(U, F) ⟶ Γ(U ∩ |Y|, (F / I ^ (n + 1) F)|_Y)` (quotient map, then pullback of sections to
  `Y_(n+1)`), for every open `U` of `X`.
* `moduleCompletionSectionsMap_surjective`, `moduleCompletionSectionsMap_eq_zero_iff`: for `F`
  quasi-coherent and `U` affine it is surjective with kernel `I(U) ^ (n + 1) Γ(U, F)`.
* `Hartshorne.pullbackUnitTransition_app_unit`, `Hartshorne.pullbackUnitTransitionRestrict_val_app_unit`:
  the generic transition maps behind `moduleCompletionMap` (see `moduleCompletionMap_eq`) carry the
  pullback of a section `x` to the pullback of its image; `pullbackUnitTransitionRestrict_val_app`
  is the section formula for `pullbackUnitTransitionRestrict`, and
  `Hartshorne.pushforward_pullback_map_val_app_unit` the one for a pulled-back map `a^* u`.
* `pushforward_pullback_cokernelπ_comp_moduleCompletionMap`: the transition map composed with the
  pullback of `F ⟶ F / I ^ (n + 2) F` equals restriction from `Y_(n+2)` to `Y_(n+1)` followed by the
  pullback of `F ⟶ F / I ^ (n + 1) F` (a square of morphisms over the completed structure sheaf).

Hartshorne works with a coherent sheaf on a Noetherian scheme; the computation uses only
quasi-coherence.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

section ClosedImmersionUnit

open QuasicoherentAbelianAux PullbackQuasicoherent Scheme.Modules
open scoped TensorProduct

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (G : X.Modules) [G.IsQuasicoherent]
  (V : X.affineOpens)

/-- The `Γ(X, V)`-module `Γ(V, G)`, read on `Spec Γ(X, V)`. -/
private noncomputable abbrev affineSectionsModule : ModuleCat.{u} Γ(X, (V : X.Opens)) :=
  (modulesSpecToSheaf.obj (specRestriction G V)).presheaf.obj (op ⊤)

/-- `M̃ ≅ G|_V` for `M = Γ(V, G)`, the counit of the tilde–global sections adjunction. -/
private noncomputable def affineSectionsTildeIso :
    (tilde.functor Γ(X, (V : X.Opens))).obj (affineSectionsModule G V) ≅ specRestriction G V :=
  @asIso _ _ _ _ (specRestriction G V).fromTildeΓ
    (isIso_fromTildeΓ_iff.mpr ((isQuasicoherent_iff_forall_essImage _).mp inferInstance V))

set_option maxHeartbeats 1000000 in
-- The same computation as `closedImmersion_unit_toOpen` for the ideal sheaf; the unfolding of
-- the pullback isomorphisms needs the larger budget there too.
/-- On the affine open `i⁻¹ V`, the pullback `i^* s` of a section `s` of `G` over `V` is
`1 ⊗ s ∈ Γ(i⁻¹ V) ⊗_{Γ(V)} Γ(V, G)`. -/
private theorem unit_toOpen
    (s : Γ(G, (haveI := V.2.isOpenImmersion_fromSpec; V.2.fromSpec ''ᵁ ⊤)))
    (hT : haveI := V.2.isOpenImmersion_fromSpec
      haveI := (closedImmersionAffinePreimage i V).2.isOpenImmersion_fromSpec
      (closedImmersionAffinePreimage i V).2.fromSpec ''ᵁ ⊤ ≤ i ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤)) :
    haveI := V.2.isOpenImmersion_fromSpec
    (specRestrictionPullbackIso i G V (closedImmersionAffinePreimage i V) le_rfl
        (affineSectionsModule G V) (affineSectionsTildeIso G V)).inv.app ⊤
      (((Scheme.Modules.pullback i).obj G).presheaf.map (homOfLE hT).op
        (((pullbackPushforwardAdjunction i).unit.app G).app (V.2.fromSpec ''ᵁ ⊤) s)) =
      (tilde.toOpen ((ModuleCat.extendScalars (i.appLE V (closedImmersionAffinePreimage i V)
        le_rfl).hom).obj (affineSectionsModule G V)) ⊤).hom
        ((1 : Γ(Z, (closedImmersionAffinePreimage i V : Z.Opens))) ⊗ₜ[Γ(X, (V : X.Opens))]
          (show affineSectionsModule G V from s)) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have hT' : ⊤ ≤ Spec.map (i.appLE V (closedImmersionAffinePreimage i V) le_rfl) ⁻¹ᵁ
      (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤)) := by
    intro x _
    show (Spec.map _).base x ∈ V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤)
    rw [Scheme.Hom.preimage_image_eq]
    trivial
  refine (specRestrictionPullbackIso_inv_unit _ _ _ _ _ _ _ _ _ hT hT').trans ?_
  set N := specRestriction G V
  have r1 : (affineSectionsTildeIso G V).inv.app (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))
      (((restrictAdjunction V.2.fromSpec).unit.app G).app (V.2.fromSpec ''ᵁ ⊤) s) =
      (tilde.toOpen (affineSectionsModule G V) (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))).hom s := by
    have h1 := ConcreteCategory.congr_hom
      (Scheme.Modules.toOpen_fromTildeΓ_app N (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))) s
    have h2 : ∀ y, (affineSectionsTildeIso G V).inv.app (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))
        ((affineSectionsTildeIso G V).hom.app (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤)) y) = y :=
      fun y => ConcreteCategory.congr_hom
        (congrArg (fun φ => Hom.app φ _) (affineSectionsTildeIso G V).hom_inv_id) y
    refine Eq.trans ?_ (h2 _)
    refine congrArg _ ?_
    exact h1.symm
  rw [r1]
  refine Eq.trans ?_ (Hartshorne.tildePullbackIso_hom_unit_apply _ _ _)
  refine congrArg _ ?_
  have r3 : (tilde.toOpen (affineSectionsModule G V)
      (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))).hom s =
      ((tilde.functor _).obj (affineSectionsModule G V)).presheaf.map (homOfLE le_top).op
        ((tilde.toOpen (affineSectionsModule G V) ⊤).hom s) := rfl
  rw [r3]
  refine (congrArg _ (app_presheaf_map _ _ _)).trans ((presheaf_map_map _ _ _ (𝟙 _) _).trans ?_)
  exact (ConcreteCategory.congr_hom (CategoryTheory.Functor.map_id _ _) _).trans rfl

omit [G.IsQuasicoherent] in
/-- On sections over an affine open `V`, a function `k ∈ Γ(V)` acts on `Γ(V, G)` through its
restriction. -/
private theorem affineSectionsModule_smul (k : Γ(X, (V : X.Opens))) (y : affineSectionsModule G V)
    (hV : haveI := V.2.isOpenImmersion_fromSpec; V.2.fromSpec ''ᵁ ⊤ ≤ (V : X.Opens)) :
    haveI := V.2.isOpenImmersion_fromSpec
    (k • y : affineSectionsModule G V) =
      (show Γ(X, V.2.fromSpec ''ᵁ ⊤) from X.presheaf.map (homOfLE hV).op k) •
        (show Γ(G, V.2.fromSpec ''ᵁ ⊤) from y) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have e1 : (V.2.fromSpec.appIso ⊤).hom (X.presheaf.map (homOfLE hV).op k) =
      (Scheme.ΓSpecIso Γ(X, (V : X.Opens))).inv k := by
    refine (RelDiffLocal.fromSpec_appIso_hom_res V ⊤ hV k).trans ?_
    rw [show (⊤ : (Spec Γ(X, (V : X.Opens))).Opens).leTop = 𝟙 ⊤ from Subsingleton.elim _ _,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  have e2 : (V.2.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, (V : X.Opens))).inv k) =
      X.presheaf.map (homOfLE hV).op k := by
    rw [← e1]
    exact Iso.hom_inv_id_apply _ _
  change (show Γ(X, V.2.fromSpec ''ᵁ ⊤) from (V.2.fromSpec.appIso ⊤).inv
      ((Scheme.ΓSpecIso Γ(X, (V : X.Opens))).inv k)) •
      (show Γ(G, V.2.fromSpec ''ᵁ ⊤) from y) = _
  rw [e2]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Unfolding `specRestrictionPullbackIso` on sections, as in
-- `bijective_idealSheafSqQuotientToPushforward_app`.
/-- Surjectivity and the kernel of the unit `G ⟶ i_* i^* G` on sections over `V`, written over
the open `V.fromSpec '' ⊤`. -/
private theorem unit_app_fromSpec :
    haveI := V.2.isOpenImmersion_fromSpec
    Function.Surjective (((pullbackPushforwardAdjunction i).unit.app G).app
        (V.2.fromSpec ''ᵁ ⊤)) ∧
      ∀ s, ((pullbackPushforwardAdjunction i).unit.app G).app (V.2.fromSpec ''ᵁ ⊤) s = 0 →
        (show affineSectionsModule G V from s) ∈
          RingHom.ker (i.appLE V (closedImmersionAffinePreimage i V) le_rfl).hom •
            (⊤ : Submodule Γ(X, (V : X.Opens)) (affineSectionsModule G V)) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (closedImmersionAffinePreimage i V).2.fromSpec :=
    (closedImmersionAffinePreimage i V).2.isOpenImmersion_fromSpec
  have hρ : Function.Surjective (i.appLE V (closedImmersionAffinePreimage i V) le_rfl) := by
    have h := i.app_surjective (V : X.Opens) V.2
    rwa [Scheme.Hom.app_eq_appLE] at h
  have hTV : V.2.fromSpec ''ᵁ ⊤ = (V : X.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, V.2.opensRange_fromSpec]
  have hWT : (closedImmersionAffinePreimage i V).2.fromSpec ''ᵁ ⊤ =
      i ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤) := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      (closedImmersionAffinePreimage i V).2.opensRange_fromSpec, hTV]
  have hT := hWT.le
  let SR := specRestrictionPullbackIso i G V (closedImmersionAffinePreimage i V) le_rfl
    (affineSectionsModule G V) (affineSectionsTildeIso G V)
  have hR : IsIso (homOfLE hT) := ⟨⟨homOfLE hWT.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  have hSR : Function.Bijective (SR.inv.app ⊤) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨SR.hom.app ⊤, fun y => ?_, fun y => ?_⟩
    · exact ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ ⊤) SR.inv_hom_id) y
    · exact ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ ⊤) SR.hom_inv_id) y
  have hG := hSR.comp (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback i).obj G).presheaf.map (homOfLE hT).op))
  have hK := unit_toOpen i G V
  have htO := ConcreteCategory.bijective_of_isIso (tilde.toOpen ((ModuleCat.extendScalars
    (i.appLE V (closedImmersionAffinePreimage i V) le_rfl).hom).obj (affineSectionsModule G V)) ⊤)
  refine ⟨fun y => ?_, fun s hs => ?_⟩
  · obtain ⟨z, hz⟩ := htO.2 (SR.inv.app ⊤
      (((Scheme.Modules.pullback i).obj G).presheaf.map (homOfLE hT).op y))
    obtain ⟨m, rfl⟩ := exists_one_tmul _ hρ _ z
    exact ⟨m, hG.1 ((hK m hT).trans hz)⟩
  · have h1 : ((1 : Γ(Z, (closedImmersionAffinePreimage i V : Z.Opens))) ⊗ₜ[Γ(X, (V : X.Opens))]
        (show affineSectionsModule G V from s) : (ModuleCat.extendScalars
          (i.appLE V (closedImmersionAffinePreimage i V) le_rfl).hom).obj
            (affineSectionsModule G V)) = 0 := by
      refine htO.1 ((hK s hT).symm.trans ?_)
      rw [hs]
      exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    exact mem_ker_smul_top_of_one_tmul_eq_zero _ hρ _ _ h1

/-- For a closed immersion `i : Z ⟶ X`, a quasi-coherent `𝒪_X`-module `G` and an affine open `V`,
the unit `G ⟶ i_* i^* G` of the pullback–pushforward adjunction is surjective on sections over
`V`. -/
theorem closedImmersion_unit_app_surjective :
    Function.Surjective (((pullbackPushforwardAdjunction i).unit.app G).app V) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have hTV : V.2.fromSpec ''ᵁ ⊤ = (V : X.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, V.2.opensRange_fromSpec]
  have key := (unit_app_fromSpec i G V).1
  rw [hTV] at key
  exact key

/-- For a closed immersion `i : Z ⟶ X`, a quasi-coherent `𝒪_X`-module `G` and an affine open `V`
such that the kernel of `Γ(V, 𝒪_X) → Γ(i⁻¹ V, 𝒪_Z)` kills `Γ(V, G)`, the unit `G ⟶ i_* i^* G` is
injective on sections over `V`. -/
theorem closedImmersion_unit_app_injective
    (hG : ∀ a : Γ(X, (V : X.Opens)), i.app V a = 0 → ∀ s : Γ(G, V), a • s = 0) :
    Function.Injective (((pullbackPushforwardAdjunction i).unit.app G).app V) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have hTV : V.2.fromSpec ''ᵁ ⊤ = (V : X.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, V.2.opensRange_fromSpec]
  have hTW : i ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤) ≤ (closedImmersionAffinePreimage i V : Z.Opens) :=
    fun x hx => by rw [hTV] at hx; exact hx
  have hG' : ∀ a : Γ(X, V.2.fromSpec ''ᵁ ⊤), i.app (V.2.fromSpec ''ᵁ ⊤) a = 0 →
      ∀ s : Γ(G, V.2.fromSpec ''ᵁ ⊤), a • s = 0 := by
    rw [hTV]
    exact hG
  have key : Function.Injective (((pullbackPushforwardAdjunction i).unit.app G).app
      (V.2.fromSpec ''ᵁ ⊤)) := by
    refine (injective_iff_map_eq_zero
      (((pullbackPushforwardAdjunction i).unit.app G).app (V.2.fromSpec ''ᵁ ⊤)).hom).mpr
      fun s hs => ?_
    refine Submodule.smul_induction_on (p := fun x : affineSectionsModule G V =>
      (show Γ(G, V.2.fromSpec ''ᵁ ⊤) from x) = 0) ((unit_app_fromSpec i G V).2 s hs)
      (fun k hk y _ => ?_) (fun x y hx hy => ?_)
    · have hk0 : i.app (V.2.fromSpec ''ᵁ ⊤) (X.presheaf.map (homOfLE hTV.le).op k) = 0 := by
        have hmor : X.presheaf.map (homOfLE hTV.le).op ≫ i.app (V.2.fromSpec ''ᵁ ⊤) =
            i.appLE V (closedImmersionAffinePreimage i V) le_rfl ≫
              Z.presheaf.map (homOfLE hTW).op := by
          rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
        refine (ConcreteCategory.congr_hom hmor k).trans ?_
        change Z.presheaf.map (homOfLE hTW).op
          (i.appLE V (closedImmersionAffinePreimage i V) le_rfl k) = 0
        rw [RingHom.mem_ker.mp hk, map_zero]
      change (show Γ(G, V.2.fromSpec ''ᵁ ⊤) from (k • y : affineSectionsModule G V)) = 0
      rw [affineSectionsModule_smul G V k y hTV.le]
      exact hG' _ hk0 _
    · change (show Γ(G, V.2.fromSpec ''ᵁ ⊤) from x) + (show Γ(G, V.2.fromSpec ''ᵁ ⊤) from y) = 0
      rw [hx, hy, add_zero]
  rw [hTV] at key
  exact key

end ClosedImmersionUnit


section TransitionSections

variable {Z Y W : Scheme.{u}} (s : Z ⟶ Y) (a : Y ⟶ W) (b : Z ⟶ W) (h : s ≫ a = b)
  {C : Type*} [Category C] {J : GrothendieckTopology C} {F₁ : C ⥤ Opens Z} {F₂ : C ⥤ Opens Y}
  [F₁.IsContinuous J (Opens.grothendieckTopology Z)]
  [F₂.IsContinuous J (Opens.grothendieckTopology Y)]
  {T : Sheaf J RingCat.{u}} (α : F₁ ⟶ F₂ ⋙ Opens.map s.base)
  (φ₂ : T ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} _ _).obj Y.ringCatSheaf)
  (φ₁ : T ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} _ _).obj Z.ringCatSheaf)
  (hφ : ∀ (V : Cᵒᵖ) (r : T.obj.obj V),
    Z.ringCatSheaf.obj.map (α.app V.unop).op
        (s.toRingCatSheafHom.hom.app (op (F₂.obj V.unop)) (φ₂.hom.app V r)) = φ₁.hom.app V r)

/-- On sections, `pullbackUnitTransitionRestrict` is `pullbackUnitTransition` followed by
restriction along `α`. -/
lemma pullbackUnitTransitionRestrict_val_app {Q' Q : W.Modules} (q : Q' ⟶ Q) (V : Cᵒᵖ)
    (x : ((Scheme.Modules.pullback a).obj Q').val.obj (op (F₂.obj V.unop))) :
    (pullbackUnitTransitionRestrict s a b h α φ₂ φ₁ hφ q).val.app V x =
      ((Scheme.Modules.pullback b).obj Q).val.map (α.app V.unop).op
        ((pullbackUnitTransition s a b h q).val.app (op (F₂.obj V.unop)) x) :=
  rfl

end TransitionSections

section PullbackUnitTransitionSections

open Scheme.Modules

/-- Three successive restrictions of sections of a module sheaf compose to a restriction. -/
private lemma presheaf_map_map_map {X : Scheme.{u}} (M : X.Modules) {A B C D : X.Opens}
    (p : B ⟶ A) (q : C ⟶ B) (r : D ⟶ C) (t : D ⟶ A) (x : Γ(M, A)) :
    M.presheaf.map r.op (M.presheaf.map q.op (M.presheaf.map p.op x)) = M.presheaf.map t.op x := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

/-- On the restriction of a section `a^* x` pulled back along `a`, the transport along `φ₂` of the
pullback `a^* u` of a map `u : P ⟶ Q` is the restriction of `a^* (u x)`. -/
theorem pushforward_pullback_map_val_app_unit {Y W : Scheme.{u}} (a : Y ⟶ W) {C : Type*}
    [Category C] {J : GrothendieckTopology C} {F₂ : C ⥤ Opens Y}
    [F₂.IsContinuous J (Opens.grothendieckTopology Y)] {T : Sheaf J RingCat.{u}}
    (φ₂ : T ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} _ _).obj Y.ringCatSheaf)
    {P Q : W.Modules} (u : P ⟶ Q) (V : C) (U : W.Opens) (h₂ : F₂.obj V ≤ a ⁻¹ᵁ U) (x : Γ(P, U)) :
    ((SheafOfModules.pushforward.{u} φ₂).map ((Scheme.Modules.pullback a).map u)).val.app (op V)
        (((Scheme.Modules.pullback a).obj P).presheaf.map (homOfLE h₂).op
          (((pullbackPushforwardAdjunction a).unit.app P).app U x)) =
      ((Scheme.Modules.pullback a).obj Q).presheaf.map (homOfLE h₂).op
        (((pullbackPushforwardAdjunction a).unit.app Q).app U (u.app U x)) := by
  have e1 : ((Scheme.Modules.pullback a).map u).app (a ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction a).unit.app P).app U x) =
      ((pullbackPushforwardAdjunction a).unit.app Q).app U (u.app U x) :=
    (ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ U)
      ((pullbackPushforwardAdjunction a).unit.naturality u)) x).symm
  refine (app_presheaf_map ((Scheme.Modules.pullback a).map u) (homOfLE h₂) _).trans ?_
  rw [e1]

variable {Z Y W : Scheme.{u}} (s : Z ⟶ Y) (a : Y ⟶ W) (b : Z ⟶ W) (h : s ≫ a = b)

/-- On a section `a^* x` pulled back along `a`, the map `pullbackUnitTransition` induced by
`q : Q' ⟶ Q` is the section `b^* (q x)`, restricted to `s⁻¹ a⁻¹ U`. -/
theorem pullbackUnitTransition_app_unit {Q' Q : W.Modules} (q : Q' ⟶ Q) (U : W.Opens)
    (hle : s ⁻¹ᵁ (a ⁻¹ᵁ U) ≤ b ⁻¹ᵁ U) (x : Γ(Q', U)) :
    (pullbackUnitTransition s a b h q).app (a ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction a).unit.app Q').app U x) =
      ((Scheme.Modules.pullback b).obj Q).presheaf.map (homOfLE hle).op
        (((pullbackPushforwardAdjunction b).unit.app Q).app U (q.app U x)) := by
  subst h
  have e1 : ((Scheme.Modules.pullback a).map q).app (a ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction a).unit.app Q').app U x) =
      ((pullbackPushforwardAdjunction a).unit.app Q).app U (q.app U x) :=
    (ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ U)
      ((pullbackPushforwardAdjunction a).unit.naturality q)) x).symm
  have e2 := pullbackComp_hom_unit s a Q U (q.app U x)
  have e3 : ((Scheme.Modules.pullback (s ≫ a)).obj Q).presheaf.map (homOfLE hle).op
      (((pullbackPushforwardAdjunction (s ≫ a)).unit.app Q).app U (q.app U x)) =
      ((pullbackPushforwardAdjunction (s ≫ a)).unit.app Q).app U (q.app U x) := by
    exact (ConcreteCategory.congr_hom
      (((Scheme.Modules.pullback (s ≫ a)).obj Q).presheaf.map_id _) _).trans rfl
  rw [e3]
  unfold pullbackUnitTransition
  rw [Hom.comp_app, Hom.comp_app]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, e1]
  refine Eq.trans ?_ e2
  simp [pullbackCongr]
  rfl

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {F₁ : C ⥤ Opens Z} {F₂ : C ⥤ Opens Y}
  [F₁.IsContinuous J (Opens.grothendieckTopology Z)]
  [F₂.IsContinuous J (Opens.grothendieckTopology Y)]
  {T : Sheaf J RingCat.{u}} (α : F₁ ⟶ F₂ ⋙ Opens.map s.base)
  (φ₂ : T ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} _ _).obj Y.ringCatSheaf)
  (φ₁ : T ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} _ _).obj Z.ringCatSheaf)
  (hφ : ∀ (V : Cᵒᵖ) (r : T.obj.obj V),
    Z.ringCatSheaf.obj.map (α.app V.unop).op
        (s.toRingCatSheafHom.hom.app (op (F₂.obj V.unop)) (φ₂.hom.app V r)) = φ₁.hom.app V r)

/-- On the restriction of a section `a^* x` pulled back along `a`, the map
`pullbackUnitTransitionRestrict` induced by `q : Q' ⟶ Q` is the restriction of `b^* (q x)`. -/
theorem pullbackUnitTransitionRestrict_val_app_unit {Q' Q : W.Modules} (q : Q' ⟶ Q) (V : C)
    (U : W.Opens) (h₂ : F₂.obj V ≤ a ⁻¹ᵁ U) (h₁ : F₁.obj V ≤ b ⁻¹ᵁ U) (x : Γ(Q', U)) :
    (pullbackUnitTransitionRestrict s a b h α φ₂ φ₁ hφ q).val.app (op V)
        (((Scheme.Modules.pullback a).obj Q').presheaf.map (homOfLE h₂).op
          (((pullbackPushforwardAdjunction a).unit.app Q').app U x)) =
      ((Scheme.Modules.pullback b).obj Q).presheaf.map (homOfLE h₁).op
        (((pullbackPushforwardAdjunction b).unit.app Q).app U (q.app U x)) := by
  have hle : s ⁻¹ᵁ (a ⁻¹ᵁ U) ≤ b ⁻¹ᵁ U := by subst h; exact le_rfl
  have e1 := app_presheaf_map (pullbackUnitTransition s a b h q) (homOfLE h₂)
    (((pullbackPushforwardAdjunction a).unit.app Q').app U x)
  rw [pullbackUnitTransition_app_unit s a b h q U hle] at e1
  refine (pullbackUnitTransitionRestrict_val_app s a b h α φ₂ φ₁ hφ q (op V) _).trans ?_
  erw [e1]
  exact presheaf_map_map_map _ _ _ _ _ _

end PullbackUnitTransitionSections

namespace QuasicoherentIdealSubsheaf

open ArtinReesKernelSheaf Scheme.Modules QuasicoherentAbelianAux

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X) (F : X.Modules)

/-- **The canonical map `Γ(U, F) ⟶ Γ(U ∩ |Y|, (F / I ^ (n + 1) F)|_Y)`**, for an open `U` of `X`:
the quotient map to `F / I ^ (n + 1) F`, then the pullback of sections to `Y_(n+1)`, then
restriction to the open of `Y_(n+1)` corresponding to `U ∩ |Y|` (equal to the preimage of `U`).
Its target is the type of sections of `moduleCompletionObj I F n` over `U ∩ |Y|`. -/
def moduleCompletionSectionsMap (n : ℕ) (U : X.Opens) :
    Γ(F, U) ⟶ Γ(I.moduleCompletionNeighborhood F n,
      (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj
        (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ U)) :=
  (cokernel.π (I.powSmulι F n)).app U ≫
    ((pullbackPushforwardAdjunction (I.infinitesimalNeighborhoodι (n + 1))).unit.app
      (I.moduleCompletionQuotient F n)).app U ≫
    (I.moduleCompletionNeighborhood F n).presheaf.map
      (homOfLE (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le).op

lemma moduleCompletionSectionsMap_apply (n : ℕ) (U : X.Opens) (s : Γ(F, U)) :
    I.moduleCompletionSectionsMap F n U s =
      (I.moduleCompletionNeighborhood F n).presheaf.map
        (homOfLE (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le).op
        (((pullbackPushforwardAdjunction (I.infinitesimalNeighborhoodι (n + 1))).unit.app
          (I.moduleCompletionQuotient F n)).app U ((cokernel.π (I.powSmulι F n)).app U s)) :=
  rfl

/-- **The transition maps at the morphism level.** Pulling `F ⟶ F / I ^ (n + 2) F` back to
`Y_(n+2)` and then applying the transition map is the same as restricting the pullback of `F`
from `Y_(n+2)` to `Y_(n+1)` and then pulling back `F ⟶ F / I ^ (n + 1) F`, as maps of modules over
the completed structure sheaf on `|Y|`. -/
lemma pushforward_pullback_cokernelπ_comp_moduleCompletionMap (n : ℕ) :
    (SheafOfModules.pushforward.{u} (I.formalCompletionRingCatSheafπ (n + 1))).map
        ((Scheme.Modules.pullback (I.infinitesimalNeighborhoodι (n + 1 + 1))).map
          (cokernel.π (I.powSmulι F (n + 1)))) ≫
      I.moduleCompletionMap F n =
    pullbackUnitTransitionRestrict (I.infinitesimalNeighborhoodSucc n)
        (I.infinitesimalNeighborhoodι (n + 1 + 1)) (I.infinitesimalNeighborhoodι (n + 1))
        (Scheme.IdealSheafData.inclusion_subschemeι _)
        (I.functorToPreimageInfinitesimalNeighborhoodSucc n)
        (I.formalCompletionRingCatSheafπ (n + 1)) (I.formalCompletionRingCatSheafπ n)
        (fun V r => I.formalCompletionSheafMap_limit_π_apply n V.unop r) (𝟙 F) ≫
      (SheafOfModules.pushforward.{u} (I.formalCompletionRingCatSheafπ n)).map
        ((Scheme.Modules.pullback (I.infinitesimalNeighborhoodι (n + 1))).map
          (cokernel.π (I.powSmulι F n))) := by
  rw [moduleCompletionMap_eq]
  exact pullbackUnitTransitionRestrict_naturality (I.infinitesimalNeighborhoodSucc n)
    (I.infinitesimalNeighborhoodι (n + 1 + 1)) (I.infinitesimalNeighborhoodι (n + 1))
    (Scheme.IdealSheafData.inclusion_subschemeι _)
    (I.functorToPreimageInfinitesimalNeighborhoodSucc n)
    (I.formalCompletionRingCatSheafπ (n + 1)) (I.formalCompletionRingCatSheafπ n)
    (fun V r => I.formalCompletionSheafMap_limit_π_apply n V.unop r)
    (𝟙 F) (I.moduleCompletionQuotientMap F n)
    (cokernel.π (I.powSmulι F (n + 1))) (cokernel.π (I.powSmulι F n))
    ((Category.id_comp _).trans (I.π_moduleCompletionQuotientMap F n).symm)

/-- Restriction between equal opens is bijective on sections. -/
private lemma bijective_presheaf_map_of_eq {Y : Scheme.{u}} (P : Y.Modules) {V W : Y.Opens}
    (h : W = V) (i : W ⟶ V) : Function.Bijective (P.presheaf.map i.op) := by
  have : IsIso i := ⟨⟨eqToHom h.symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  exact ConcreteCategory.bijective_of_isIso _

/-- A section of `F` is killed by `F ⟶ F / I ^ (n + 1) F` exactly when it lies in
`I ^ (n + 1) F`. -/
lemma cokernel_π_powSmulι_app_eq_zero_iff (n : ℕ) (U : X.Opens) (s : Γ(F, U)) :
    (cokernel.π (I.powSmulι F n)).app U s = 0 ↔
      s ∈ sub (powSmul (quasicoherentIdealSubsheafEquiv I) (n + 1) (⊤ : F.val.Submodule)) U := by
  constructor
  · intro hs
    let S := ShortComplex.mk (I.powSmulι F n) (cokernel.π (I.powSmulι F n))
      (cokernel.condition _)
    have : Mono S.f := by
      refine (SheafOfModules.forget _).mono_of_mono_map ?_
      exact PresheafOfModules.mono_of_injective fun V x y hxy => Subtype.ext hxy
    obtain ⟨t, rfl⟩ := modules_sections_exact (S := S)
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) s hs
    exact t.2
  · intro hs
    exact ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ U)
      (cokernel.condition (I.powSmulι F n))) ⟨s, hs⟩

/-- On an affine open `U`, the kernel of `Γ(U, 𝒪_X) → Γ(U ∩ |Y_(n+1)|, 𝒪_{Y_(n+1)})` is
`I(U) ^ (n + 1)`. -/
private lemma ker_infinitesimalNeighborhoodι_app (n : ℕ) (U : X.affineOpens) :
    RingHom.ker ((I.infinitesimalNeighborhoodι (n + 1)).app U).hom = I.ideal U ^ (n + 1) :=
  (Scheme.IdealSheafData.ker_subschemeι_app _ U).trans (I.ideal_pow (n + 1) U)

variable [F.IsQuasicoherent]

include F in
private lemma isQuasicoherent_powSmul_top (n : ℕ) :
    (ArtinReesKernelSheaf.toModules
      (powSmul (quasicoherentIdealSubsheafEquiv I) (n + 1) (⊤ : F.val.Submodule))
      (isLocal_powSmul _ _ _)).IsQuasicoherent := by
  have := isQuasicoherent_top (E := F)
  exact isQuasicoherent_powSmul _ _ isLocal_top

/-- `F / I ^ (n + 1) F` is quasi-coherent when `F` is. -/
lemma isQuasicoherent_moduleCompletionQuotient (n : ℕ) :
    (I.moduleCompletionQuotient F n).IsQuasicoherent := by
  have := isQuasicoherent_powSmul_top I F n
  exact isQuasicoherent_cokernel _

/-- On an affine open `U`, the sections of `I ^ (n + 1) F` are `I(U) ^ (n + 1) Γ(U, F)`. -/
lemma sub_powSmul_top_eq (n : ℕ) (U : X.affineOpens) :
    sub (powSmul (quasicoherentIdealSubsheafEquiv I) (n + 1) (⊤ : F.val.Submodule)) U =
      I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, U)) := by
  have := isQuasicoherent_top (E := F)
  exact sub_powSmul_eq _ (n + 1) isLocal_top U

/-- On an affine open, `F ⟶ F / I ^ (n + 1) F` is surjective on sections. -/
lemma surjective_cokernel_π_powSmulι_app (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((cokernel.π (I.powSmulι F n)).app U) := by
  have := isQuasicoherent_powSmul_top I F n
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hTV : U.2.fromSpec ''ᵁ ⊤ = (U : X.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  have key := surjective_cokernel_π_app (I.powSmulι F n) U
  rw [hTV] at key
  exact key

/-- **Surjectivity on affine sections.** For `F` quasi-coherent and `U` affine,
`Γ(U, F) ⟶ Γ(U ∩ |Y|, (F / I ^ (n + 1) F)|_Y)` is surjective. -/
theorem moduleCompletionSectionsMap_surjective (n : ℕ) (U : X.affineOpens) :
    Function.Surjective (I.moduleCompletionSectionsMap F n U) := by
  have := I.isQuasicoherent_moduleCompletionQuotient F n
  have h1 := I.surjective_cokernel_π_powSmulι_app F n U
  have h2 := closedImmersion_unit_app_surjective (I.infinitesimalNeighborhoodι (n + 1))
    (I.moduleCompletionQuotient F n) U
  have h3 := bijective_presheaf_map_of_eq (I.moduleCompletionNeighborhood F n)
    (I.functor_obj_preimage_infinitesimalNeighborhoodι n U)
    (homOfLE (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le)
  intro y
  obtain ⟨z, rfl⟩ := h3.2 y
  obtain ⟨w, rfl⟩ := h2 z
  obtain ⟨s, rfl⟩ := h1 w
  exact ⟨s, rfl⟩

/-- **The kernel on affine sections.** For `F` quasi-coherent and `U` affine, a section of `F`
over `U` maps to zero in `Γ(U ∩ |Y|, (F / I ^ (n + 1) F)|_Y)` exactly when it lies in
`I(U) ^ (n + 1) Γ(U, F)`. -/
theorem moduleCompletionSectionsMap_eq_zero_iff (n : ℕ) (U : X.affineOpens) (s : Γ(F, U)) :
    I.moduleCompletionSectionsMap F n U s = 0 ↔
      s ∈ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, U)) := by
  have := I.isQuasicoherent_moduleCompletionQuotient F n
  have h3 := bijective_presheaf_map_of_eq (I.moduleCompletionNeighborhood F n)
    (I.functor_obj_preimage_infinitesimalNeighborhoodι n U)
    (homOfLE (I.functor_obj_preimage_infinitesimalNeighborhoodι n U).le)
  have hinj := closedImmersion_unit_app_injective (I.infinitesimalNeighborhoodι (n + 1))
    (I.moduleCompletionQuotient F n) U (fun a ha t => by
      obtain ⟨s', rfl⟩ := I.surjective_cokernel_π_powSmulι_app F n U t
      refine (Hom.app_smul (cokernel.π (I.powSmulι F n)) a s').symm.trans ?_
      refine (I.cokernel_π_powSmulι_app_eq_zero_iff F n U _).2 ?_
      rw [I.sub_powSmul_top_eq F n U]
      have ha' : a ∈ I.ideal U ^ (n + 1) := by
        rw [← I.ker_infinitesimalNeighborhoodι_app n U]
        exact ha
      exact Submodule.smul_mem_smul ha' Submodule.mem_top)
  rw [← I.sub_powSmul_top_eq F n U, ← I.cokernel_π_powSmulι_app_eq_zero_iff F n U s,
    moduleCompletionSectionsMap_apply]
  constructor
  · intro hs
    exact hinj (h3.1 (hs.trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm))
  · intro hs
    exact (congrArg _ ((congrArg _ hs).trans (map_zero _))).trans (map_zero _)

end QuasicoherentIdealSubsheaf

end Hartshorne

