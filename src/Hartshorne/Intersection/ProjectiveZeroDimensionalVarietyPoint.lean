/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ProjectivePointDegree
import Hartshorne.Intersection.ProjectiveProperClosedDimensionDrop
import Hartshorne.Projective.LinearSeparation

/-!
# Zero-dimensional projective varieties

A zero-dimensional projective variety consists of a single point.  This is the
closed-point bridge used in Hartshorne I.7, Corollary 7.8.
-/

namespace Hartshorne

open Set

noncomputable section

universe u

/-- Points are closed in projective space with its Zariski topology. -/
private theorem isClosed_singleton_projectiveSpace
    {k : Type u} [Field k] {n : ℕ} (P : ProjectiveSpace k (Fin (n + 1))) :
    IsClosed ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) := by
  rw [isClosed_iff_isProjAlgebraicSet]
  refine ⟨homogeneousVanishingSet {P},
    isHomogeneousSet_homogeneousVanishingSet {P},
    Set.Subset.antisymm (subset_projZeroSet_homogeneousVanishingSet {P}) ?_⟩
  intro Q hQ
  by_contra hQP
  have hPQ : P ≠ Q := by
    simpa [Set.mem_singleton_iff, eq_comm] using hQP
  obtain ⟨_, h, _, hh, _, _, hhP, hhQ⟩ :=
    exists_linear_forms_separating_projective_points hPQ
  apply hhQ
  exact hQ h ⟨⟨1, hh⟩, by
    intro R hRP
    rw [Set.mem_singleton_iff] at hRP
    simpa [hRP] using hhP⟩

/-- A zero-dimensional projective variety is a single projective point. -/
theorem IsProjVariety.eq_singleton_of_projDim_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {Y : Set (ProjectiveSpace k (Fin (n + 1)))} (hY : IsProjVariety Y)
    (hdim : projDim Y = 0) :
    ∃ P : ProjectiveSpace k (Fin (n + 1)), Y = {P} := by
  obtain ⟨P, hPY⟩ := hY.1.nonempty
  have hPclosed : IsClosed ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) :=
    isClosed_singleton_projectiveSpace P
  have hPalg : IsProjAlgebraicSet ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) :=
    isClosed_iff_isProjAlgebraicSet.1 hPclosed
  have hPvar : IsProjVariety ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) :=
    ⟨(isIrreducible_iff_isPrime_homogeneousVanishingIdeal hPalg).2
        (isPrime_homogeneousVanishingIdeal_singleton P),
      hPclosed⟩
  have hPdim : projDim ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) = 0 := by
    rw [← projectiveHilbertPolynomial_degree hPalg,
      (projectivePoint_hilbertPolynomial_and_degree P).1]
    simp [hilbertPolynomialDegree]
  refine ⟨P, Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 hPY)⟩
  by_contra hnot
  have hproper : ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) ⊂ Y :=
    Set.ssubset_iff_subset_ne.2
      ⟨Set.singleton_subset_iff.2 hPY, fun h => hnot (le_of_eq h.symm)⟩
  have hlt := projDim_lt_of_closed_ssubset_isProjVariety hY hPvar.2 hproper
  rw [hPdim, hdim] at hlt
  exact (lt_irrefl 0) hlt

end

end Hartshorne
