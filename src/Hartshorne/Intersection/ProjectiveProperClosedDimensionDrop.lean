/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ProjSpaceDimension

/-!
# Proper closed subsets of projective varieties have smaller dimension

The dimension of a projective variety is a natural number, as may be seen on
any nonempty standard affine chart.  A chain of irreducible closed subsets of
a proper closed subset can then be extended by the ambient irreducible closed
subset, so its dimension is strictly smaller.

## Main results

* `Hartshorne.exists_projDim_eq_nat_of_isProjVariety`
* `Hartshorne.projDim_lt_of_closed_ssubset_isProjVariety`
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u

private theorem topologicalKrullDim_eq_height_of_irreducible_closed
    {X : Type*} [TopologicalSpace X] {Y : Set X}
    (hirr : IsIrreducible Y) (hclosed : IsClosed Y) :
    topologicalKrullDim Y =
      (Order.height
        (⟨Y, hirr, hclosed⟩ : IrreducibleCloseds X) : WithBot ℕ∞) := by
  rw [topologicalKrullDim_subtype_eq hclosed]
  change Order.krullDim
      (Set.Iic (⟨Y, hirr, hclosed⟩ : IrreducibleCloseds X)) = _
  rw [← Order.height_eq_krullDim_Iic]

/-- The dimension of a projective variety is represented by a natural number. -/
theorem exists_projDim_eq_nat_of_isProjVariety
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type} [Finite σ] [Nonempty σ]
    {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y) :
    ∃ r : ℕ, projDim Y = (r : WithBot ℕ∞) := by
  classical
  obtain ⟨P, hPY⟩ := hY.1.nonempty
  obtain ⟨i, hi⟩ := exists_mem_standardChart P
  have hne : (Y ∩ standardChart i).Nonempty := ⟨P, hPY, hi⟩
  have hA : IsAffineVariety (chartMap i '' (Y ∩ standardChart i)) :=
    isAffineVariety_chartMap_image i hY hne
  have : IsDomain (coordinateRing (chartMap i '' (Y ∩ standardChart i))) :=
    isDomain_coordinateRing hA
  obtain ⟨r, hr⟩ := exists_ringKrullDim_eq_natCast k
    (coordinateRing (chartMap i '' (Y ∩ standardChart i)))
  refine ⟨r, ?_⟩
  rw [projDim_eq_dim_chart hY i hne,
    dim_eq_ringKrullDim_coordinateRing hA.isAlgebraicSet, hr]

/-- A proper closed subset of an irreducible projective algebraic set has
strictly smaller dimension. -/
theorem projDim_lt_of_closed_ssubset_isProjVariety
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type} [Finite σ] [Nonempty σ]
    {Y Z : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y)
    (hZ : IsClosed Z) (hZY : Z ⊂ Y) : projDim Z < projDim Y := by
  classical
  let VY : IrreducibleCloseds (ProjectiveSpace k σ) := ⟨Y, hY.1, hY.2⟩
  have hdimY : projDim Y = (Order.height VY : WithBot ℕ∞) := by
    rw [projDim_def,
      topologicalKrullDim_eq_height_of_irreducible_closed hY.1 hY.2]
  obtain ⟨n, hn⟩ := exists_projDim_eq_nat_of_isProjVariety hY
  have hheight : Order.height VY = (n : ℕ∞) := by
    exact_mod_cast hdimY.symm.trans hn
  change topologicalKrullDim Z < projDim Y
  rw [topologicalKrullDim_subtype_eq hZ, hdimY, hheight]
  change Order.krullDim
    {T : IrreducibleCloseds (ProjectiveSpace k σ) // (T : Set _) ⊆ Z} <
      (n : WithBot ℕ∞)
  rw [Order.krullDim_lt_coe_iff]
  intro p
  let q : LTSeries (IrreducibleCloseds (ProjectiveSpace k σ)) :=
    p.map (fun T => T.1) (fun _ _ h => h)
  have hqY : q.last < VY := by
    change ((q.last : IrreducibleCloseds (ProjectiveSpace k σ)) : Set _) ⊂ Y
    exact Set.ssubset_of_subset_of_ssubset p.last.2 hZY
  have hlen := Order.length_le_height_last (p := q.snoc VY hqY)
  have hlenV : ((q.snoc VY hqY).length : ℕ∞) ≤ Order.height VY := by
    simpa using hlen
  rw [hheight] at hlenV
  have hlen' : p.length + 1 ≤ n := by
    simp [q] at hlenV
    exact_mod_cast hlenV
  omega

end

end Hartshorne
