/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AbsoluteNormalization

/-!
# Dominance of the normalization morphism

Hartshorne, *Algebraic Geometry*, Exercise II.3.8, p. 91.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

private theorem absoluteNormalizationGenericMap_isDominant
    (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (absoluteNormalizationGenericMap X) := by
  constructor
  change Dense (Set.range (absoluteNormalizationGenericMap X))
  rw [dense_iff_inter_open]
  intro U hU hUne
  let V : X.Opens := ⟨U, hU⟩
  let _ : Nonempty V := ⟨⟨hUne.choose, hUne.choose_spec⟩⟩
  let _ : Unique (Spec X.functionField) :=
    inferInstanceAs (Unique (Spec (.of (X.functionField : Type u))))
  let x : Spec X.functionField := default
  have hx : x ∈ absoluteNormalizationGenericMap X ⁻¹ᵁ V := by
    rw [absoluteNormalizationGenericMap_preimage_eq_top]
    trivial
  exact ⟨absoluteNormalizationGenericMap X x,
    hx, Set.mem_range_self x⟩

/-- The normalization morphism of an integral scheme has dense image. -/
theorem absoluteNormalizationMap_isDominant
    (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (absoluteNormalizationMap X) := by
  let g := absoluteNormalizationGenericMap X
  have hg : IsDominant g := absoluteNormalizationGenericMap_isDominant X
  have hcomp : IsDominant (g.toNormalization ≫ g.fromNormalization) := by
    rw [g.toNormalization_fromNormalization]
    exact hg
  change IsDominant g.fromNormalization
  exact IsDominant.of_comp g.toNormalization g.fromNormalization (H := hcomp)

end Hartshorne
