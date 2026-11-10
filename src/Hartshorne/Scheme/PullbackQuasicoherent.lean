/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AffineTildeChangeOfRings
import Hartshorne.Scheme.CoherentAffineLocalCriterion

/-!
# Pullback preserves quasi-coherence and coherence

Hartshorne II, Proposition 5.8(a,b): for a morphism of schemes `f : X ⟶ Y`, the pullback
`f^*` sends quasi-coherent `𝒪_Y`-modules to quasi-coherent `𝒪_X`-modules, and coherent ones to
coherent ones.

Locally, if `V ⊆ f⁻¹ U` are affine opens and `F|_U ≅ M̃`, then `(f^*F)|_V ≅ (Γ(V) ⊗ M)~`.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

namespace PullbackQuasicoherent

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If `V ⊆ f⁻¹ U` are affine opens and `F|_U ≅ M̃`, then `(f^*F)|_V ≅ (Γ(V) ⊗_{Γ(U)} M)~`. -/
def specRestrictionPullbackIso (F : Y.Modules) (U : Y.affineOpens) (V : X.affineOpens)
    (h : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) (M : ModuleCat.{u} Γ(Y, (U : Y.Opens)))
    (e : (tilde.functor Γ(Y, (U : Y.Opens))).obj M ≅ specRestriction F U) :
    (tilde.functor Γ(X, (V : X.Opens))).obj
        ((ModuleCat.extendScalars.{u} (f.appLE U V h).hom).obj M) ≅
      specRestriction ((Scheme.Modules.pullback f).obj F) V :=
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  letI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  ((tildePullbackIso (f.appLE U V h)).app M).symm ≪≫
    (Scheme.Modules.pullback (Spec.map (f.appLE U V h))).mapIso
      (e ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.2.fromSpec).app F) ≪≫
    (Scheme.Modules.pullbackComp _ _).app F ≪≫
    (Scheme.Modules.pullbackCongr (IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 h)).app F ≪≫
    ((Scheme.Modules.pullbackComp _ _).app F).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback V.2.fromSpec).app _).symm

/-- Pairs `(i, V)` of an index `i` and an affine open `V ⊆ f⁻¹ Uᵢ` of `X`. -/
abbrev Refinement {ι : Type*} (U : ι → Y.affineOpens) : Type _ :=
  {p : ι × X.affineOpens // (p.2 : X.Opens) ≤ f ⁻¹ᵁ (U p.1 : Y.Opens)}

/-- Given an affine open cover `Uᵢ` of `Y`, the affine opens `V` of `X` lying in some `f⁻¹ Uᵢ`
cover `X`. -/
theorem iSup_refinement_eq_top {ι : Type*} (U : ι → Y.affineOpens)
    (hU : (⨆ i, (U i : Y.Opens)) = ⊤) :
    (⨆ p : Refinement f U, (p.1.2 : X.Opens)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx : f.base x ∈ (⨆ i, (U i : Y.Opens)) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨W, hW, hxW, hWU⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ (U i : Y.Opens)) (x := x) hi
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(i, ⟨W, hW⟩), hWU⟩, hxW⟩

end PullbackQuasicoherent

open PullbackQuasicoherent

/-- **Hartshorne II, Proposition 5.8(a).** For a morphism of schemes `f : X ⟶ Y`, the pullback of
a quasi-coherent `𝒪_Y`-module is a quasi-coherent `𝒪_X`-module. -/
theorem isQuasicoherent_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback f).obj F).IsQuasicoherent := by
  obtain ⟨ι, U, hU, hF⟩ := (quasicoherent_affine_local_tfae F).out 0 1 |>.mp ‹_›
  refine ((quasicoherent_affine_local_tfae _).out 1 0).mp ?_
  refine ⟨Refinement f U, fun p => p.1.2, iSup_refinement_eq_top f U hU, fun p => ?_⟩
  obtain ⟨M, ⟨e⟩⟩ := hF p.1.1
  exact ⟨_, ⟨specRestrictionPullbackIso f F (U p.1.1) p.1.2 p.2 M e⟩⟩

/-- **Hartshorne II, Proposition 5.8(b).** For a morphism of schemes `f : X ⟶ Y`, the pullback of
a coherent `𝒪_Y`-module is a coherent `𝒪_X`-module. Hartshorne assumes `X` and `Y` noetherian;
the proof doesn't use it. -/
theorem isCoherent_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {F : Y.Modules} (hF : IsCoherent F) :
    IsCoherent ((Scheme.Modules.pullback f).obj F) := by
  obtain ⟨ι, U, hU, hF⟩ := hF
  refine ⟨Refinement f U, fun p => p.1.2, iSup_refinement_eq_top f U hU, fun p => ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hF p.1.1
  refine ⟨(ModuleCat.extendScalars.{u} (f.appLE _ _ p.2).hom).obj M, ?_,
    ⟨specRestrictionPullbackIso f F (U p.1.1) p.1.2 p.2 M e⟩⟩
  algebraize [(f.appLE (U p.1.1 : Y.Opens) (p.1.2 : X.Opens) p.2).hom]
  exact inferInstanceAs (Module.Finite Γ(X, (p.1.2 : X.Opens))
    (TensorProduct Γ(Y, (U p.1.1 : Y.Opens)) Γ(X, (p.1.2 : X.Opens)) M))

end

end Hartshorne
