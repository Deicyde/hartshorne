/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The affine-morphism criterion

A morphism of schemes is affine if this can be checked on one affine open
cover of its target, equivalently if the inverse image of every affine target
open is affine.  We also record the standard immediate consequences used in
Hartshorne, Exercise II.5.17.
-/

open CategoryTheory TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- A morphism is affine on one affine open cover of its target if and only if
the inverse image of every affine target open is affine. -/
theorem exists_affine_open_cover_iff_forall_isAffineOpen_preimage
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∃ (ι : Type u) (U : ι → Y.affineOpens),
      (⨆ i, (U i : Y.Opens)) = ⊤ ∧
        ∀ i, IsAffineOpen (f ⁻¹ᵁ (U i : Y.Opens))) ↔
      ∀ V : Y.Opens, IsAffineOpen V → IsAffineOpen (f ⁻¹ᵁ V) := by
  rw [← isAffineHom_iff]
  constructor
  · rintro ⟨ι, U, hU, hfU⟩
    apply isAffineHom_of_forall_exists_isAffineOpen f
    intro y
    have hy : y ∈ (⨆ i, (U i : Y.Opens)) := by simp [hU]
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact ⟨U i, hi, (U i).2, hfU i⟩
  · intro hf
    refine ⟨Y.affineOpens, id, iSup_affineOpens_eq_top Y, ?_⟩
    intro U
    exact hf.isAffine_preimage U U.2

/-- Every affine morphism is quasi-compact. -/
theorem quasiCompact_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] : QuasiCompact f :=
  inferInstance

/-- Every affine morphism is separated. -/
theorem isSeparated_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] : IsSeparated f :=
  inferInstance

/-- Every finite morphism is affine. -/
theorem isAffineHom_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] : IsAffineHom f :=
  inferInstance

end Hartshorne
