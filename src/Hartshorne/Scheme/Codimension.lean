/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.KrullDimension

/-!
# Codimension in a scheme

Hartshorne, *Algebraic Geometry*, II.3 (p. 86).

The codimension of a closed subset is the infimum of the coheights of the
irreducible closed subsets it contains. The definition is made for every
subset of a topological space; for the empty subset, the infimum is over an
empty family and hence equals `⊤` in `ℕ∞`.
-/

namespace Hartshorne

/-- The codimension of `Y` in `X`, defined as the infimum of the coheights of
the irreducible closed subsets of `X` contained in `Y`.

This is intended for closed subsets of schemes, but the same formula makes
sense for any subset of a topological space. -/
noncomputable def codim {X : Type*} [TopologicalSpace X] (Y : Set X) : ℕ∞ :=
  ⨅ (Z : TopologicalSpace.IrreducibleCloseds X) (_ : (Z : Set X) ⊆ Y), Order.coheight Z

/-- In a quasi-sober `T₀` space (for instance a scheme), the codimension of the closure of a point
is the coheight of the point for the specialization preorder (`x ≤ y` when `y ⤳ x`), which is the
order used on the points of a scheme. -/
theorem codim_closure_singleton_eq_coheight {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] (x : X) :
    codim (closure ({x} : Set X)) = @Order.coheight X (specializationPreorder X) x := by
  let _ : PartialOrder X := specializationOrder X
  change codim (closure ({x} : Set X)) = Order.coheight x
  let e : TopologicalSpace.IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints
  have he : ((e.symm x : TopologicalSpace.IrreducibleCloseds X) : Set X) = closure {x} :=
    coe_irreducibleEquivPoints_symm_apply x
  apply le_antisymm
  · calc codim (closure ({x} : Set X)) ≤ Order.coheight (e.symm x) :=
          iInf₂_le (f := fun (W : TopologicalSpace.IrreducibleCloseds X)
            (_ : (W : Set X) ⊆ closure {x}) ↦ Order.coheight W) _ he.le
      _ = Order.coheight x := Order.coheight_orderIso _ _
  · rw [← Order.coheight_orderIso e.symm x]
    refine le_iInf₂ fun W hW ↦ Order.coheight_anti ?_
    change (W : Set X) ⊆ (e.symm x : Set X)
    rw [he]
    exact hW

end Hartshorne
