/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Codimension
import Hartshorne.Scheme.FiniteType
import Mathlib.AlgebraicGeometry.Properties

/-!
# Codimension as an infimum of local dimensions

Hartshorne, *Algebraic Geometry*, Exercise II.3.20(c) (pp. 94–95).

For a nonempty closed subset of an integral scheme of finite type over a field,
codimension is the infimum of the Krull dimensions of the local rings at its
points.
-/

namespace Hartshorne

open CategoryTheory AlgebraicGeometry Set TopologicalSpace

universe u

/-- The codimension of a nonempty closed subset of an integral scheme of finite
type over a field is the infimum of the dimensions of the local rings at its
points. -/
theorem codim_eq_iInf_ringKrullDim_stalk
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (_hf : FiniteType f)
    {Y : Set X} (_hY : Y.Nonempty) (hYc : IsClosed Y) :
    (codim Y : WithBot ℕ∞) =
      ⨅ P : Y, ringKrullDim (X.presheaf.stalk P.1) := by
  change (↑(⨅ (Z : IrreducibleCloseds X) (_ : (Z : Set X) ⊆ Y),
    Order.coheight Z) : WithBot ℕ∞) = _
  rw [WithBot.coe_iInf _ (OrderBot.bddBelow _)]
  simp_rw [WithBot.coe_iInf _ (OrderBot.bddBelow _)]
  let e : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints
  apply le_antisymm
  · refine le_iInf fun P => ?_
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
    refine iInf_le_of_le (e.symm P.1) ?_
    refine iInf_le_of_le ?_ ?_
    · simpa [e] using closure_minimal (Set.singleton_subset_iff.mpr P.2) hYc
    · rw [Order.coheight_orderIso e.symm]
  · refine le_iInf fun Z => ?_
    refine le_iInf fun hZY => ?_
    let P : Y := ⟨e Z, hZY (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem⟩
    calc
      (⨅ P : Y, ringKrullDim (X.presheaf.stalk P.1)) ≤
          ringKrullDim (X.presheaf.stalk P.1) := iInf_le _ P
      _ = (Order.coheight (e Z) : WithBot ℕ∞) :=
        AlgebraicGeometry.ringKrullDim_stalk_eq_coheight _
      _ = (Order.coheight Z : WithBot ℕ∞) := by
        rw [Order.coheight_orderIso e]

end Hartshorne
