/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.AffineDimensionTheorem
import Hartshorne.Intersection.ProjectiveIntersectionChart
import Hartshorne.Projective.ProjSpaceDimension

/-!
# The projective dimension theorem

Hartshorne, *Algebraic Geometry*, I.7, Theorem 7.2 (pp. 48–49), dimension
bound for each irreducible component.

## Main result

* `Hartshorne.projective_dimension_theorem`
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {σ : Type} [Finite σ] [DecidableEq σ]

/-- **Theorem I.7.2, dimension clause.** Every irreducible component `W` of
the intersection of two projective varieties satisfies
`dim Y + dim Z ≤ dim W + dim ℙⁿ`.  Since `σ` indexes homogeneous
coordinates, `dim ℙⁿ = Nat.card σ - 1`. -/
theorem projective_dimension_theorem
    {Y Z : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) (hZ : IsProjVariety Z)
    (W : irreducibleComponents ↥(Y ∩ Z)) :
    projDim Y + projDim Z ≤
      projDim (projectiveComponentCarrier W.1) +
        ((Nat.card σ - 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨w, hwW⟩ := W.2.1.nonempty
  obtain ⟨i, hwi⟩ := exists_mem_standardChart w.1
  have hi : (projectiveComponentCarrier W.1 ∩ standardChart i).Nonempty :=
    ⟨w.1, ⟨w, hwW, rfl⟩, hwi⟩
  obtain ⟨C, hC, hYdim, hZdim, hWdim⟩ :=
    projectiveIntersectionComponent_chart hY hZ W i hi
  have hYne : (Y ∩ standardChart i).Nonempty :=
    ⟨w.1, w.2.1, hwi⟩
  have hZne : (Z ∩ standardChart i).Nonempty :=
    ⟨w.1, w.2.2, hwi⟩
  have hYaff : IsAffineVariety (chartMap i '' (Y ∩ standardChart i)) :=
    isAffineVariety_chartMap_image i hY hYne
  have hZaff : IsAffineVariety (chartMap i '' (Z ∩ standardChart i)) :=
    isAffineVariety_chartMap_image i hZ hZne
  have haff := affine_dimension_theorem hYaff hZaff C
  have hCdim : dim (affineComponentCarrier C.1) =
      projDim (projectiveComponentCarrier W.1) := by
    rw [affineComponentCarrier, hC, ← hWdim]
  have hcard : Nat.card {j : σ // j ≠ i} = Nat.card σ - 1 := by
    have hadd := card_subtype_ne_add_one (σ := σ) i
    omega
  calc
    projDim Y + projDim Z =
        dim (chartMap i '' (Y ∩ standardChart i)) +
          dim (chartMap i '' (Z ∩ standardChart i)) := by
      rw [hYdim, hZdim]
    _ ≤ dim (affineComponentCarrier C.1) + Nat.card {j : σ // j ≠ i} := haff
    _ = projDim (projectiveComponentCarrier W.1) +
        ((Nat.card σ - 1 : ℕ) : WithBot ℕ∞) := by
      rw [hCdim, hcard]

end

end Hartshorne
