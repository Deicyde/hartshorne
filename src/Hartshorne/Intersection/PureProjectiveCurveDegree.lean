/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.DegreeUnion
import Hartshorne.Intersection.ProjectiveComponents
import Hartshorne.Intersection.ProjectiveProperClosedDimensionDrop

/-!
# Degree of a pure projective curve

For a pure one-dimensional projective algebraic set, degree is the sum of the
degrees of its irreducible components.
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u

private noncomputable def projectiveComponentUnion
    {k : Type u} [Field k]
    {Y : Set (ProjectiveSpace k (Fin 3))}
    (s : Finset (irreducibleComponents ↥Y)) :
    Set (ProjectiveSpace k (Fin 3)) :=
  ⋃ W ∈ s, projectiveComponentCarrier W.1

private theorem projectiveComponentUnion_insert
    {k : Type u} [Field k]
    {Y : Set (ProjectiveSpace k (Fin 3))}
    (W : irreducibleComponents ↥Y)
    (s : Finset (irreducibleComponents ↥Y)) :
    projectiveComponentUnion (insert W s) =
      projectiveComponentCarrier W.1 ∪ projectiveComponentUnion s := by
  simp [projectiveComponentUnion]

private theorem projectiveComponentUnion_subset
    {k : Type u} [Field k]
    {Y : Set (ProjectiveSpace k (Fin 3))}
    (s : Finset (irreducibleComponents ↥Y)) :
    projectiveComponentUnion s ⊆ Y := by
  rintro P hP
  simp only [projectiveComponentUnion, Set.mem_iUnion, exists_prop] at hP
  obtain ⟨W, _, p, _, rfl⟩ := hP
  exact p.2

private theorem isProjAlgebraicSet_projectiveComponentUnion
    {k : Type u} [Field k]
    {Y : Set (ProjectiveSpace k (Fin 3))} (hY : IsProjAlgebraicSet Y)
    (s : Finset (irreducibleComponents ↥Y)) :
    IsProjAlgebraicSet (projectiveComponentUnion s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa [projectiveComponentUnion] using
        (isProjAlgebraicSet_empty (k := k) (σ := Fin 3))
  | @insert W s hWs ih =>
      have hWalg : IsProjAlgebraicSet (projectiveComponentCarrier W.1) :=
        (isProjVariety_projectiveComponentCarrier
          (isClosed_iff_isProjAlgebraicSet.2 hY) W).isProjAlgebraicSet
      rw [projectiveComponentUnion_insert]
      exact hWalg.union ih

private theorem projDim_projectiveComponentUnion_eq_one
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Set (ProjectiveSpace k (Fin 3))}
    (hYdim : projDim Y = (1 : WithBot ℕ∞))
    (hpure : ∀ W : irreducibleComponents ↥Y,
      projDim (projectiveComponentCarrier W.1) = (1 : WithBot ℕ∞))
    {s : Finset (irreducibleComponents ↥Y)} (hs : s.Nonempty) :
    projDim (projectiveComponentUnion s) = (1 : WithBot ℕ∞) := by
  obtain ⟨W, hWs⟩ := hs
  have hWU : projectiveComponentCarrier W.1 ⊆ projectiveComponentUnion s := by
    intro P hP
    simp only [projectiveComponentUnion, Set.mem_iUnion, exists_prop]
    exact ⟨W, hWs, hP⟩
  have hUY : projectiveComponentUnion s ⊆ Y :=
    projectiveComponentUnion_subset s
  have hlower : projDim (projectiveComponentCarrier W.1) ≤
      projDim (projectiveComponentUnion s) :=
    (Topology.IsEmbedding.inclusion hWU).isInducing.topologicalKrullDim_le
  have hupper : projDim (projectiveComponentUnion s) ≤ projDim Y :=
    (Topology.IsEmbedding.inclusion hUY).isInducing.topologicalKrullDim_le
  rw [hpure W] at hlower
  rw [hYdim] at hupper
  exact le_antisymm hupper hlower

private theorem projDim_inter_projectiveComponentUnion_lt_one
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Set (ProjectiveSpace k (Fin 3))} (hY : IsProjAlgebraicSet Y)
    (hpure : ∀ W : irreducibleComponents ↥Y,
      projDim (projectiveComponentCarrier W.1) = (1 : WithBot ℕ∞))
    (W : irreducibleComponents ↥Y)
    (s : Finset (irreducibleComponents ↥Y)) (hWs : W ∉ s) :
    projDim (projectiveComponentCarrier W.1 ∩ projectiveComponentUnion s) <
      (1 : WithBot ℕ∞) := by
  classical
  let C := projectiveComponentCarrier W.1
  let U := projectiveComponentUnion s
  have hCvar : IsProjVariety C :=
    isProjVariety_projectiveComponentCarrier
      (isClosed_iff_isProjAlgebraicSet.2 hY) W
  have hUalg : IsProjAlgebraicSet U :=
    isProjAlgebraicSet_projectiveComponentUnion hY s
  have hInterClosed : IsClosed (C ∩ U) :=
    hCvar.2.inter (isClosed_iff_isProjAlgebraicSet.2 hUalg)
  have hproper : C ∩ U ⊂ C := by
    refine Set.ssubset_iff_subset_ne.2 ⟨Set.inter_subset_left, ?_⟩
    intro heq
    have hCU : C ⊆ U := by
      intro P hPC
      have hPI : P ∈ C ∩ U := by
        rw [heq]
        exact hPC
      exact hPI.2
    let carriers : Finset (Set (ProjectiveSpace k (Fin 3))) :=
      s.image (fun V ↦ projectiveComponentCarrier V.1)
    have hclosed : ∀ D ∈ carriers, IsClosed D := by
      intro D hD
      obtain ⟨V, hVs, rfl⟩ := Finset.mem_image.mp hD
      exact (isProjVariety_projectiveComponentCarrier
        (isClosed_iff_isProjAlgebraicSet.2 hY) V).2
    have hCU' : C ⊆ ⋃ D ∈ carriers, D := by
      simpa [C, U, carriers, projectiveComponentUnion] using hCU
    obtain ⟨D, hD, hCD⟩ :=
      IsIrreducible.exists_mem_subset_of_subset_biUnion
        hCvar.1 carriers hclosed hCU'
    obtain ⟨V, hVs, hDV⟩ := Finset.mem_image.mp hD
    subst D
    have hWV : W.1 ⊆ V.1 := by
      intro w hw
      obtain ⟨v, hv, hvw⟩ := hCD ⟨w, hw, rfl⟩
      have hv_eq : v = w := Subtype.ext hvw
      simpa [hv_eq] using hv
    have hVW : V.1 ⊆ W.1 := W.2.2 V.2.1 hWV
    have hWVeq : W = V := by
      apply Subtype.ext
      exact Set.Subset.antisymm hWV hVW
    exact hWs (hWVeq ▸ hVs)
  have hlt :=
    projDim_lt_of_closed_ssubset_isProjVariety hCvar hInterClosed hproper
  simpa [C, U, hpure W] using hlt

private theorem projDim_empty_projective
    {k : Type u} [Field k] :
    projDim (∅ : Set (ProjectiveSpace k (Fin 3))) = ⊥ := by
  unfold projDim topologicalKrullDim
  let _ : IsEmpty
      (TopologicalSpace.IrreducibleCloseds
        (↥(∅ : Set (ProjectiveSpace k (Fin 3))))) :=
    ⟨fun Z ↦ Z.2.1.nonempty.elim fun x ↦ x.2⟩
  exact Order.krullDim_eq_bot

private theorem projectiveDegree_empty
    {k : Type u} [Field k] [IsAlgClosed k] :
    projectiveDegree (∅ : Set (ProjectiveSpace k (Fin 3))) = 0 := by
  have hdegree := projectiveHilbertPolynomial_degree
    (isProjAlgebraicSet_empty (k := k) (σ := Fin 3))
  rw [projDim_empty_projective] at hdegree
  have hpoly :
      projectiveHilbertPolynomial
        (∅ : Set (ProjectiveSpace k (Fin 3))) = 0 := by
    by_contra hne
    simp [hilbertPolynomialDegree, hne] at hdegree
  simp [projectiveDegree, hpoly]

/-- The degree of a pure projective plane curve is the sum of the degrees of
its irreducible components. -/
theorem projectiveDegree_eq_sum_projectiveComponents
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Set (ProjectiveSpace k (Fin 3))} (hY : IsProjAlgebraicSet Y)
    (hYdim : projDim Y = (1 : WithBot ℕ∞))
    (hpure : ∀ W : irreducibleComponents ↥Y,
      projDim (projectiveComponentCarrier W.1) = (1 : WithBot ℕ∞)) :
    projectiveDegree Y =
      ∑ W ∈ projectiveComponents Y,
        projectiveDegree (projectiveComponentCarrier W.1) := by
  classical
  have hsum : ∀ s : Finset (irreducibleComponents ↥Y),
      projectiveDegree (projectiveComponentUnion s) =
        ∑ W ∈ s, projectiveDegree (projectiveComponentCarrier W.1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa [projectiveComponentUnion] using (projectiveDegree_empty (k := k))
    | @insert W s hWs ih =>
        by_cases hs : s = ∅
        · subst s
          simp [projectiveComponentUnion]
        · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.2 hs
          have hWalg : IsProjAlgebraicSet (projectiveComponentCarrier W.1) :=
            (isProjVariety_projectiveComponentCarrier
              (isClosed_iff_isProjAlgebraicSet.2 hY) W).isProjAlgebraicSet
          have hUalg : IsProjAlgebraicSet (projectiveComponentUnion s) :=
            isProjAlgebraicSet_projectiveComponentUnion hY s
          have hUdim : projDim (projectiveComponentUnion s) =
              (1 : WithBot ℕ∞) :=
            projDim_projectiveComponentUnion_eq_one hYdim hpure hsne
          have hInterDim :
              projDim (projectiveComponentCarrier W.1 ∩
                projectiveComponentUnion s) < (1 : WithBot ℕ∞) :=
            projDim_inter_projectiveComponentUnion_lt_one hY hpure W s hWs
          rw [projectiveComponentUnion_insert]
          rw [projectiveDegree_union hWalg hUalg (hpure W) hUdim hInterDim]
          rw [ih]
          simp [hWs]
  have hcover :
      projectiveComponentUnion (projectiveComponents Y) = Y :=
    iUnion_projectiveComponents_eq Y
  exact (congrArg projectiveDegree hcover).symm.trans
    (hsum (projectiveComponents Y))

end

end Hartshorne
