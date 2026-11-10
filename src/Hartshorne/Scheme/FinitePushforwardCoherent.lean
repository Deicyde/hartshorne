/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QcqsPushforwardQuasicoherent
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Finite pushforward preserves coherence

Hartshorne II, Exercise 5.5(c): for a finite morphism `f : X ⟶ Y`, the pushforward of a coherent
`𝒪_X`-module is coherent. On an affine open `V = Spec A` of `Y`, `f⁻¹ V = Spec B` with `B` finite
over `A`, and a finite `B`-module is finite over `A`.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

/-- For a finite morphism `f : X ⟶ Y` and a coherent `𝒪_X`-module `F`, the sections of `f_* F`
over an affine open `U` of `Y` form a finite `Γ(Y, U)`-module. -/
theorem module_finite_pushforward_sections {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {F : X.Modules} (hF : IsCoherent F) (U : Y.affineOpens) :
    Module.Finite Γ(Y, (U : Y.Opens)) Γ((Scheme.Modules.pushforward f).obj F, (U : Y.Opens)) := by
  let := (f.app (U : Y.Opens)).hom.toAlgebra
  have hB : Module.Finite Γ(Y, (U : Y.Opens)) Γ(X, f ⁻¹ᵁ (U : Y.Opens)) :=
    f.finite_app _ U.2
  have hM : Module.Finite Γ(X, f ⁻¹ᵁ (U : Y.Opens)) Γ(F, f ⁻¹ᵁ (U : Y.Opens)) :=
    (forall_affine_finite_of_isCoherent F hF ⟨_, U.2.preimage f⟩).1
  let : Module Γ(Y, (U : Y.Opens)) Γ(F, f ⁻¹ᵁ (U : Y.Opens)) :=
    Module.compHom _ (f.app (U : Y.Opens)).hom
  have : IsScalarTower Γ(Y, (U : Y.Opens)) Γ(X, f ⁻¹ᵁ (U : Y.Opens))
      Γ(F, f ⁻¹ᵁ (U : Y.Opens)) :=
    ⟨fun r b m => mul_smul ((f.app (U : Y.Opens)).hom r) b m⟩
  have : Module.Finite Γ(Y, (U : Y.Opens)) Γ(F, f ⁻¹ᵁ (U : Y.Opens)) :=
    Module.Finite.trans Γ(X, f ⁻¹ᵁ (U : Y.Opens)) _
  let e : Γ(F, f ⁻¹ᵁ (U : Y.Opens)) ≃ₗ[Γ(Y, (U : Y.Opens))]
      Γ((Scheme.Modules.pushforward f).obj F, (U : Y.Opens)) :=
    { AddEquiv.refl _ with map_smul' := fun _ _ => rfl }
  exact Module.Finite.equiv e

/-- **Finite pushforward preserves coherence** (Hartshorne II, Exercise 5.5(c)). For a finite
morphism `f : X ⟶ Y` and a coherent `𝒪_X`-module `F`, `f_* F` is coherent. Hartshorne assumes
`X` and `Y` locally Noetherian; the proof doesn't use it. -/
theorem isCoherent_pushforward_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {F : X.Modules} (hF : IsCoherent F) : IsCoherent ((Scheme.Modules.pushforward f).obj F) := by
  have hqc : F.IsQuasicoherent := by
    obtain ⟨ι, U, hU, h⟩ := hF
    choose M hM e using h
    refine ((quasicoherent_affine_local_tfae F).out 1 0).mp ?_
    exact ⟨ι, U, hU, fun i ↦ ⟨M i, e i⟩⟩
  have : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs f F
  have hiso := ((quasicoherent_affine_local_tfae ((Scheme.Modules.pushforward f).obj F)).out 0 2).mp
    this
  refine ⟨Y.affineOpens, id, iSup_affineOpens_eq_top Y, fun U ↦ ?_⟩
  exact ⟨moduleSpecΓFunctor.obj (specRestriction ((Scheme.Modules.pushforward f).obj F) U),
    (finite_specRestriction_iff _ U).mpr (module_finite_pushforward_sections f hF U),
    ⟨@asIso _ _ _ _ (specRestriction ((Scheme.Modules.pushforward f).obj F) U).fromTildeΓ
      (hiso U)⟩⟩

end

end Hartshorne
