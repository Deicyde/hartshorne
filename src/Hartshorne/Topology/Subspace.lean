/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Irreducible
import Mathlib.Topology.KrullDimension

/-!
# Irreducible closed subsets of a closed subspace

General topology, not specific to Hartshorne, but needed for his Proposition
1.7: the dimension of a variety is the Krull dimension of its coordinate ring.

For a closed `Y ⊆ X`, the irreducible closed subsets of `Y` with its subspace
topology correspond order-isomorphically to the irreducible closed subsets of
`X` contained in `Y`. Mathlib has neither this correspondence nor the resulting
computation of `topologicalKrullDim ↥Y` inside `X`.

Closedness of `Y` is what makes `Subtype.val` a closed map, so the image of a
closed subset of `↥Y` is closed in `X` and not merely closed in `Y`.

## Main results

* `IrreducibleCloseds.subtypeOrderIso`
* `topologicalKrullDim_subtype_eq`
-/

open TopologicalSpace Topology

variable {X : Type*} [TopologicalSpace X] {Y : Set X}

/-- Pulling an irreducible subset of a closed `Y` back along `Subtype.val`
leaves it irreducible. The covering argument is run with images, which are
closed in `X` precisely because `Y` is. -/
theorem isClosed_image_val (hY : IsClosed Y) {z : Set Y} (hz : IsClosed z) :
    IsClosed (Subtype.val '' z) := by
  obtain ⟨c, hc, hcz⟩ := hz.image_val
  rw [hcz]
  exact hc.inter hY

/-- Pulling an irreducible subset of a closed `Y` back along `Subtype.val`
leaves it irreducible. The covering argument is run with images, which are
closed in `X` precisely because `Y` is. -/
theorem isIrreducible_preimage_val (hY : IsClosed Y) {Z : Set X}
    (hZ : IsIrreducible Z) (hZY : Z ⊆ Y) :
    IsIrreducible (Subtype.val ⁻¹' Z : Set Y) := by
  have him : ∀ {z : Set Y}, IsClosed z → IsClosed (Subtype.val '' z) :=
    fun hz => isClosed_image_val hY hz
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hZ.nonempty
    exact ⟨⟨x, hZY hx⟩, hx⟩
  · rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z₁ z₂ hz₁ hz₂ hcov
    have hZcov : Z ⊆ Subtype.val '' z₁ ∪ Subtype.val '' z₂ := by
      intro x hx
      rcases hcov (show (⟨x, hZY hx⟩ : Y) ∈ Subtype.val ⁻¹' Z from hx) with h | h
      · exact Or.inl ⟨⟨x, hZY hx⟩, h, rfl⟩
      · exact Or.inr ⟨⟨x, hZY hx⟩, h, rfl⟩
    have pull : ∀ {z : Set Y}, Z ⊆ Subtype.val '' z → (Subtype.val ⁻¹' Z : Set Y) ⊆ z := by
      intro z hz x hx
      obtain ⟨y, hy, hxy⟩ := hz hx
      rwa [Subtype.val_injective hxy] at hy
    rcases isPreirreducible_iff_isClosed_union_isClosed.1 hZ.2 _ _ (him hz₁) (him hz₂)
      hZcov with h | h
    · exact Or.inl (pull h)
    · exact Or.inr (pull h)

namespace IrreducibleCloseds

/-- For `Y` closed, the irreducible closed subsets of the subspace `Y`
correspond to the irreducible closed subsets of `X` lying inside `Y`. -/
def subtypeOrderIso (hY : IsClosed Y) :
    IrreducibleCloseds Y ≃o {Z : IrreducibleCloseds X // (Z : Set X) ⊆ Y} where
  toFun S :=
    ⟨⟨Subtype.val '' S,
      S.isIrreducible.image _ continuous_subtype_val.continuousOn,
      isClosed_image_val hY S.isClosed⟩,
      Subtype.coe_image_subset _ _⟩
  invFun Z :=
    ⟨Subtype.val ⁻¹' (Z.1 : Set X),
      isIrreducible_preimage_val hY Z.1.isIrreducible Z.2,
      Z.1.isClosed.preimage continuous_subtype_val⟩
  left_inv S := by
    apply IrreducibleCloseds.ext
    exact Subtype.val_injective.preimage_image _
  right_inv Z := by
    apply Subtype.ext
    apply IrreducibleCloseds.ext
    exact (Subtype.image_preimage_coe _ _).trans (Set.inter_eq_right.2 Z.2)
  map_rel_iff' := by
    intro S T
    exact Set.image_subset_image_iff Subtype.val_injective

/-- The Krull dimension of a closed subspace, computed inside the ambient
space. -/
theorem _root_.topologicalKrullDim_subtype_eq (hY : IsClosed Y) :
    topologicalKrullDim Y
      = Order.krullDim {Z : IrreducibleCloseds X // (Z : Set X) ⊆ Y} :=
  Order.krullDim_eq_of_orderIso (subtypeOrderIso hY)

end IrreducibleCloseds
