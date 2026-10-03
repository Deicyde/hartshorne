/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ProjectiveHypersurfaceBezout
import Hartshorne.Intersection.ProjectiveZeroDimensionalVarietyPoint

/-!
# Bézout's theorem for distinct plane curves

Hartshorne, *Algebraic Geometry*, Corollary I.7.8 (p. 54).
-/

namespace Hartshorne

open MvPolynomial Set TopologicalSpace

noncomputable section

universe u

/-- **Hartshorne I.7.8 (Bézout for plane curves).** The intersection of two
distinct irreducible projective plane curves is finite, and the sum of their
projective intersection multiplicities is the product of their degrees. -/
theorem plane_curve_bezout
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y Z : Set (ProjectiveSpace k (Fin 3))}
    (hY : IsProjVariety Y) (hZ : IsProjVariety Z)
    (hYdim : projDim Y = (1 : WithBot ℕ∞))
    (hZdim : projDim Z = (1 : WithBot ℕ∞))
    (hYZ : Y ≠ Z) :
    (Y ∩ Z).Finite ∧
      ∑ W ∈ projectiveIntersectionComponents Y Z,
          (projectiveIntersectionMultiplicity hY hZ.isProjAlgebraicSet W : ℚ) =
        projectiveDegree Y * projectiveDegree Z := by
  classical
  obtain ⟨f, d, hd, hf, hfirr, hZeq⟩ :=
    (projective_codimension_one_iff_hypersurface (n := 2) hZ (by omega)).1
      (by simpa using hZdim)
  have hproperZ : ¬Y ⊆ Z := by
    intro hsub
    have hssub : Y ⊂ Z :=
      Set.ssubset_iff_subset_ne.mpr ⟨hsub, hYZ⟩
    have hlt :=
      projDim_lt_of_closed_ssubset_isProjVariety hZ hY.2 hssub
    rw [hYdim, hZdim] at hlt
    exact (lt_irrefl _) hlt
  have hproper :
      ¬Y ⊆ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k)) := by
    rwa [← hZeq]
  subst Z
  have hWdim
      (W : irreducibleComponents
        ↥(Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k)))) :
      projDim (projectiveComponentCarrier W.1) = 0 := by
    simpa using
      (projectiveHypersurfaceSectionComponent_projDim_eq
        (n := 2) (r := 1) (d := d) (by omega) (by omega) hd
        hY hYdim f hf hfirr hproper W)
  have hWsingle
      (W : irreducibleComponents
        ↥(Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k)))) :
      ∃ P : ProjectiveSpace k (Fin 3),
        projectiveComponentCarrier W.1 = {P} :=
    (isProjVariety_projectiveComponentCarrier
        (hY.2.inter hZ.2) W).eq_singleton_of_projDim_eq_zero (hWdim W)
  have hWdeg
      (W : irreducibleComponents
        ↥(Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k)))) :
      projectiveDegree (projectiveComponentCarrier W.1) = 1 := by
    obtain ⟨P, hP⟩ := hWsingle W
    rw [hP]
    exact (projectivePoint_hilbertPolynomial_and_degree P).2
  letI : Fintype
      (irreducibleComponents
        ↥(Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k)))) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.fintype
  have hfiniteUnion :
      (⋃ W : irreducibleComponents
          ↥(Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k))),
        projectiveComponentCarrier W.1).Finite := by
    apply Set.finite_iUnion
    intro W
    obtain ⟨P, hP⟩ := hWsingle W
    rw [hP]
    exact Set.finite_singleton P
  have hsub :
      Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k)) ⊆
        ⋃ W : irreducibleComponents
            ↥(Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k))),
          projectiveComponentCarrier W.1 := by
    intro P hP
    let p : ↥(Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k))) :=
      ⟨P, hP⟩
    let W : irreducibleComponents
        ↥(Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k))) :=
      ⟨irreducibleComponent p,
        irreducibleComponent_mem_irreducibleComponents p⟩
    apply Set.mem_iUnion.2
    refine ⟨W, ?_⟩
    exact ⟨p, mem_irreducibleComponent, rfl⟩
  have hinterFinite :
      (Y ∩ projZeroSet ({f} : Set (MvPolynomial (Fin 3) k))).Finite :=
    hfiniteUnion.subset hsub
  have hbezout := projective_hypersurface_bezout
    (n := 2) (d := d) (r := 1) hd (by omega)
    Y hY hYdim f hf hfirr hproper
  simp_rw [hWdeg, mul_one] at hbezout
  exact ⟨hinterFinite, hbezout⟩

end

end Hartshorne
