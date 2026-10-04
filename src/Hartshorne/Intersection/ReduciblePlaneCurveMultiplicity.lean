/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.PlaneCurveBezout
import Hartshorne.Intersection.ProjectiveComponents

/-!
# Pointwise multiplicity for reducible plane curves

Hartshorne, *Algebraic Geometry*, Remark I.7.8.2 (p. 54).

For pure one-dimensional projective algebraic sets with no common irreducible
component, the pointwise intersection multiplicity is the sum of the
multiplicities of all pairs of irreducible components through the point.
-/

namespace Hartshorne

open MvPolynomial Set TopologicalSpace

noncomputable section

universe u

/-- The pointwise intersection multiplicity of two pure reducible plane
curves.  It is the sum, over pairs of irreducible components, of the
intersection multiplicities of the point components supported at `P`.

The dimension and disjoint-component assumptions are part of the source
contract.  They are used by the finiteness and total-sum theorems below. -/
noncomputable def reduciblePlaneCurveIntersectionMultiplicity
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y Z : Set (ProjectiveSpace k (Fin 3))}
    (hY : IsProjAlgebraicSet Y) (hZ : IsProjAlgebraicSet Z)
    (_hYdim : projDim Y = (1 : WithBot ℕ∞))
    (_hZdim : projDim Z = (1 : WithBot ℕ∞))
    (_hYpure : ∀ C : irreducibleComponents ↥Y,
      projDim (projectiveComponentCarrier C.1) = (1 : WithBot ℕ∞))
    (_hZpure : ∀ D : irreducibleComponents ↥Z,
      projDim (projectiveComponentCarrier D.1) = (1 : WithBot ℕ∞))
    (_hYZ : ∀ (C : irreducibleComponents ↥Y)
      (D : irreducibleComponents ↥Z),
      projectiveComponentCarrier C.1 ≠ projectiveComponentCarrier D.1)
    (P : ProjectiveSpace k (Fin 3)) : ℕ := by
  classical
  exact
    ∑ C ∈ projectiveComponents Y,
      ∑ D ∈ projectiveComponents Z,
        ∑ W ∈ projectiveComponents
            (projectiveComponentCarrier C.1 ∩ projectiveComponentCarrier D.1),
          if P ∈ projectiveComponentCarrier W.1 then
            projectiveIntersectionMultiplicity
              (isProjVariety_projectiveComponentCarrier
                (isClosed_iff_isProjAlgebraicSet.2 hY) C)
              (isProjVariety_projectiveComponentCarrier
                (isClosed_iff_isProjAlgebraicSet.2 hZ) D).isProjAlgebraicSet
              W
          else 0

/-- An irreducible component of the intersection of distinct irreducible
projective plane curves is a single point. -/
private theorem planeCurveIntersectionComponent_eq_singleton
    {k : Type u} [Field k] [IsAlgClosed k]
    {A B : Set (ProjectiveSpace k (Fin 3))}
    (hA : IsProjVariety A) (hB : IsProjVariety B)
    (hAdim : projDim A = (1 : WithBot ℕ∞))
    (hBdim : projDim B = (1 : WithBot ℕ∞))
    (hAB : A ≠ B) (W : irreducibleComponents ↥(A ∩ B)) :
    ∃ P : ProjectiveSpace k (Fin 3),
      projectiveComponentCarrier W.1 = {P} := by
  obtain ⟨f, d, hd, hf, hfirr, hBeq⟩ :=
    (projective_codimension_one_iff_hypersurface (n := 2) hB (by omega)).1
      (by simpa using hBdim)
  have hproperB : ¬A ⊆ B := by
    intro hsub
    have hssub : A ⊂ B := Set.ssubset_iff_subset_ne.mpr ⟨hsub, hAB⟩
    have hlt :=
      projDim_lt_of_closed_ssubset_isProjVariety hB hA.2 hssub
    rw [hAdim, hBdim] at hlt
    exact (lt_irrefl _) hlt
  have hproper :
      ¬A ⊆ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k)) := by
    rwa [← hBeq]
  subst B
  have hWdim : projDim (projectiveComponentCarrier W.1) = 0 := by
    simpa using
      (projectiveHypersurfaceSectionComponent_projDim_eq
        (n := 2) (r := 1) (d := d) (by omega) (by omega) hd
        hA hAdim f hf hfirr hproper W)
  exact
    (isProjVariety_projectiveComponentCarrier
      (hA.2.inter hB.2) W).eq_singleton_of_projDim_eq_zero hWdim

/-- Every component in the pairwise sum defining reducible-curve
intersection multiplicity has singleton carrier. -/
theorem reduciblePlaneCurveComponent_eq_singleton
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y Z : Set (ProjectiveSpace k (Fin 3))}
    (hY : IsProjAlgebraicSet Y) (hZ : IsProjAlgebraicSet Z)
    (_hYdim : projDim Y = (1 : WithBot ℕ∞))
    (_hZdim : projDim Z = (1 : WithBot ℕ∞))
    (hYpure : ∀ C : irreducibleComponents ↥Y,
      projDim (projectiveComponentCarrier C.1) = (1 : WithBot ℕ∞))
    (hZpure : ∀ D : irreducibleComponents ↥Z,
      projDim (projectiveComponentCarrier D.1) = (1 : WithBot ℕ∞))
    (hYZ : ∀ (C : irreducibleComponents ↥Y)
      (D : irreducibleComponents ↥Z),
      projectiveComponentCarrier C.1 ≠ projectiveComponentCarrier D.1)
    (C : irreducibleComponents ↥Y) (D : irreducibleComponents ↥Z)
    (W : irreducibleComponents
      ↥(projectiveComponentCarrier C.1 ∩ projectiveComponentCarrier D.1)) :
    ∃ P : ProjectiveSpace k (Fin 3),
      projectiveComponentCarrier W.1 = {P} := by
  exact planeCurveIntersectionComponent_eq_singleton
    (isProjVariety_projectiveComponentCarrier
      (isClosed_iff_isProjAlgebraicSet.2 hY) C)
    (isProjVariety_projectiveComponentCarrier
      (isClosed_iff_isProjAlgebraicSet.2 hZ) D)
    (hYpure C) (hZpure D) (hYZ C D) W

/-- Pure reducible projective plane curves with no common irreducible
component have finite intersection. -/
theorem reduciblePlaneCurve_intersection_finite
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y Z : Set (ProjectiveSpace k (Fin 3))}
    (hY : IsProjAlgebraicSet Y) (hZ : IsProjAlgebraicSet Z)
    (_hYdim : projDim Y = (1 : WithBot ℕ∞))
    (_hZdim : projDim Z = (1 : WithBot ℕ∞))
    (hYpure : ∀ C : irreducibleComponents ↥Y,
      projDim (projectiveComponentCarrier C.1) = (1 : WithBot ℕ∞))
    (hZpure : ∀ D : irreducibleComponents ↥Z,
      projDim (projectiveComponentCarrier D.1) = (1 : WithBot ℕ∞))
    (hYZ : ∀ (C : irreducibleComponents ↥Y)
      (D : irreducibleComponents ↥Z),
      projectiveComponentCarrier C.1 ≠ projectiveComponentCarrier D.1) :
    (Y ∩ Z).Finite := by
  classical
  let _ : Fintype (irreducibleComponents ↥Y) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.fintype
  let _ : Fintype (irreducibleComponents ↥Z) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.fintype
  have hpair (C : irreducibleComponents ↥Y)
      (D : irreducibleComponents ↥Z) :
      (projectiveComponentCarrier C.1 ∩
        projectiveComponentCarrier D.1).Finite := by
    exact (plane_curve_bezout
      (isProjVariety_projectiveComponentCarrier
        (isClosed_iff_isProjAlgebraicSet.2 hY) C)
      (isProjVariety_projectiveComponentCarrier
        (isClosed_iff_isProjAlgebraicSet.2 hZ) D)
      (hYpure C) (hZpure D) (hYZ C D)).1
  have hunion :
      (⋃ C : irreducibleComponents ↥Y,
        ⋃ D : irreducibleComponents ↥Z,
          projectiveComponentCarrier C.1 ∩
            projectiveComponentCarrier D.1).Finite := by
    apply Set.finite_iUnion
    intro C
    apply Set.finite_iUnion
    exact hpair C
  apply hunion.subset
  rintro P ⟨hPY, hPZ⟩
  have hPY' :
      P ∈ ⋃ C : irreducibleComponents ↥Y,
        projectiveComponentCarrier C.1 := by
    rw [iUnion_projectiveComponentCarrier_eq Y]
    exact hPY
  have hPZ' :
      P ∈ ⋃ D : irreducibleComponents ↥Z,
        projectiveComponentCarrier D.1 := by
    rw [iUnion_projectiveComponentCarrier_eq Z]
    exact hPZ
  obtain ⟨C, hPC⟩ := Set.mem_iUnion.mp hPY'
  obtain ⟨D, hPD⟩ := Set.mem_iUnion.mp hPZ'
  exact Set.mem_iUnion.2 ⟨C, Set.mem_iUnion.2 ⟨D, hPC, hPD⟩⟩

/-- Summing the pointwise multiplicities over the finite intersection removes
the point-support indicators and recovers the sum of the component-pair
intersection multiplicities. -/
theorem sum_reduciblePlaneCurveIntersectionMultiplicity
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
        reduciblePlaneCurveIntersectionMultiplicity
          hY hZ hYdim hZdim hYpure hZpure hYZ P =
      ∑ C ∈ projectiveComponents Y,
        ∑ D ∈ projectiveComponents Z,
          ∑ W ∈ projectiveComponents
              (projectiveComponentCarrier C.1 ∩
                projectiveComponentCarrier D.1),
            projectiveIntersectionMultiplicity
              (isProjVariety_projectiveComponentCarrier
                (isClosed_iff_isProjAlgebraicSet.2 hY) C)
              (isProjVariety_projectiveComponentCarrier
                (isClosed_iff_isProjAlgebraicSet.2 hZ) D).isProjAlgebraicSet
              W := by
  classical
  let hfinite : (Y ∩ Z).Finite :=
    reduciblePlaneCurve_intersection_finite
      hY hZ hYdim hZdim hYpure hZpure hYZ
  have hpoint
      (C : irreducibleComponents ↥Y)
      (D : irreducibleComponents ↥Z)
      (W : irreducibleComponents
        ↥(projectiveComponentCarrier C.1 ∩
          projectiveComponentCarrier D.1)) :
      (∑ P ∈ hfinite.toFinset,
          if P ∈ projectiveComponentCarrier W.1 then
            projectiveIntersectionMultiplicity
              (isProjVariety_projectiveComponentCarrier
                (isClosed_iff_isProjAlgebraicSet.2 hY) C)
              (isProjVariety_projectiveComponentCarrier
                (isClosed_iff_isProjAlgebraicSet.2 hZ) D).isProjAlgebraicSet
              W
          else 0) =
        projectiveIntersectionMultiplicity
          (isProjVariety_projectiveComponentCarrier
            (isClosed_iff_isProjAlgebraicSet.2 hY) C)
          (isProjVariety_projectiveComponentCarrier
            (isClosed_iff_isProjAlgebraicSet.2 hZ) D).isProjAlgebraicSet
          W := by
    obtain ⟨Q, hW⟩ := reduciblePlaneCurveComponent_eq_singleton
      hY hZ hYdim hZdim hYpure hZpure hYZ C D W
    have hQW : Q ∈ projectiveComponentCarrier W.1 := by
      rw [hW]
      exact Set.mem_singleton Q
    have hWsub :
        projectiveComponentCarrier W.1 ⊆
          projectiveComponentCarrier C.1 ∩
            projectiveComponentCarrier D.1 := by
      rintro P ⟨p, hp, rfl⟩
      exact p.2
    have hCsub : projectiveComponentCarrier C.1 ⊆ Y := by
      rintro P ⟨p, hp, rfl⟩
      exact p.2
    have hDsub : projectiveComponentCarrier D.1 ⊆ Z := by
      rintro P ⟨p, hp, rfl⟩
      exact p.2
    have hQYZ : Q ∈ Y ∩ Z := by
      exact ⟨hCsub (hWsub hQW).1, hDsub (hWsub hQW).2⟩
    have hQfinite : Q ∈ hfinite.toFinset := by
      simpa using hQYZ
    rw [hW]
    simp [hQfinite]
  change
    (∑ P ∈ hfinite.toFinset,
      ∑ C ∈ projectiveComponents Y,
        ∑ D ∈ projectiveComponents Z,
          ∑ W ∈ projectiveComponents
              (projectiveComponentCarrier C.1 ∩
                projectiveComponentCarrier D.1),
            if P ∈ projectiveComponentCarrier W.1 then
              projectiveIntersectionMultiplicity
                (isProjVariety_projectiveComponentCarrier
                  (isClosed_iff_isProjAlgebraicSet.2 hY) C)
                (isProjVariety_projectiveComponentCarrier
                  (isClosed_iff_isProjAlgebraicSet.2 hZ) D).isProjAlgebraicSet
                W
            else 0) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W hW
  exact hpoint C D W

end

end Hartshorne
