/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.PureProjectiveCurveDegree
import Hartshorne.Intersection.ReduciblePlaneCurveMultiplicity

/-!
# Bézout's theorem for reducible plane curves

Hartshorne, *Algebraic Geometry*, Remark I.7.8.2 (p. 54).
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u

/-- **Hartshorne I.7.8.2 (Bézout for reducible plane curves).** If two pure
one-dimensional projective plane algebraic sets have no common irreducible
component, then the sum of their pointwise intersection multiplicities is the
product of their degrees. -/
theorem reducible_plane_curve_bezout
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y Z : Set (ProjectiveSpace k (Fin 3))}
    (hY : IsProjAlgebraicSet Y) (hZ : IsProjAlgebraicSet Z)
    (hYdim : projDim Y = (1 : WithBot ℕ∞))
    (hZdim : projDim Z = (1 : WithBot ℕ∞))
    (hYpure : ∀ C : irreducibleComponents ↥Y,
      projDim (projectiveComponentCarrier C.1) = (1 : WithBot ℕ∞))
    (hZpure : ∀ D : irreducibleComponents ↥Z,
      projDim (projectiveComponentCarrier D.1) = (1 : WithBot ℕ∞))
    (hYZ : ∀ (C : irreducibleComponents ↥Y)
      (D : irreducibleComponents ↥Z),
      projectiveComponentCarrier C.1 ≠ projectiveComponentCarrier D.1) :
    ∑ P ∈ (reduciblePlaneCurve_intersection_finite
        hY hZ hYdim hZdim hYpure hZpure hYZ).toFinset,
        (reduciblePlaneCurveIntersectionMultiplicity
          hY hZ hYdim hZdim hYpure hZpure hYZ P : ℚ) =
      projectiveDegree Y * projectiveDegree Z := by
  classical
  have hsumNat := sum_reduciblePlaneCurveIntersectionMultiplicity
    hY hZ hYdim hZdim hYpure hZpure hYZ
  have hsumQ :
      ∑ P ∈ (reduciblePlaneCurve_intersection_finite
          hY hZ hYdim hZdim hYpure hZpure hYZ).toFinset,
          (reduciblePlaneCurveIntersectionMultiplicity
            hY hZ hYdim hZdim hYpure hZpure hYZ P : ℚ) =
        ∑ C ∈ projectiveComponents Y,
          ∑ D ∈ projectiveComponents Z,
            ∑ W ∈ projectiveComponents
                (projectiveComponentCarrier C.1 ∩
                  projectiveComponentCarrier D.1),
              (projectiveIntersectionMultiplicity
                (isProjVariety_projectiveComponentCarrier
                  (isClosed_iff_isProjAlgebraicSet.2 hY) C)
                (isProjVariety_projectiveComponentCarrier
                  (isClosed_iff_isProjAlgebraicSet.2 hZ) D).isProjAlgebraicSet
                W : ℚ) := by
    exact_mod_cast hsumNat
  calc
    _ = ∑ C ∈ projectiveComponents Y,
          ∑ D ∈ projectiveComponents Z,
            ∑ W ∈ projectiveComponents
                (projectiveComponentCarrier C.1 ∩
                  projectiveComponentCarrier D.1),
              (projectiveIntersectionMultiplicity
                (isProjVariety_projectiveComponentCarrier
                  (isClosed_iff_isProjAlgebraicSet.2 hY) C)
                (isProjVariety_projectiveComponentCarrier
                  (isClosed_iff_isProjAlgebraicSet.2 hZ) D).isProjAlgebraicSet
                W : ℚ) := hsumQ
    _ = ∑ C ∈ projectiveComponents Y,
          ∑ D ∈ projectiveComponents Z,
            projectiveDegree (projectiveComponentCarrier C.1) *
              projectiveDegree (projectiveComponentCarrier D.1) := by
      apply Finset.sum_congr rfl
      intro C hC
      apply Finset.sum_congr rfl
      intro D hD
      exact (plane_curve_bezout
        (isProjVariety_projectiveComponentCarrier
          (isClosed_iff_isProjAlgebraicSet.2 hY) C)
        (isProjVariety_projectiveComponentCarrier
          (isClosed_iff_isProjAlgebraicSet.2 hZ) D)
        (hYpure C) (hZpure D) (hYZ C D)).2
    _ = (∑ C ∈ projectiveComponents Y,
            projectiveDegree (projectiveComponentCarrier C.1)) *
          (∑ D ∈ projectiveComponents Z,
            projectiveDegree (projectiveComponentCarrier D.1)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro C hC
      rw [Finset.mul_sum]
    _ = projectiveDegree Y * projectiveDegree Z := by
      rw [← projectiveDegree_eq_sum_projectiveComponents hY hYdim hYpure,
        ← projectiveDegree_eq_sum_projectiveComponents hZ hZdim hZpure]

end

end Hartshorne
