/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.Basic
import Hartshorne.Projective.LinearSeparation
import Hartshorne.Projective.Variety
import Mathlib.Topology.NoetherianSpace

/-!
# The topology of a quasi-projective curve

Hartshorne, *Algebraic Geometry*, I.4, Exercise 4.8(a) (p. 31), and I.6
(p. 42).

A quasi-projective curve has infinitely many points, and its proper closed
subsets are finite. Thus its Zariski topology is the cofinite topology.
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

universe u v

/-- A T₁ space of topological Krull dimension one is infinite. -/
theorem infinite_of_topologicalKrullDim_eq_one
    (X : Type*) [TopologicalSpace X] [T1Space X]
    (hdim : topologicalKrullDim X = 1) : Infinite X := by
  rw [← not_finite_iff_infinite]
  intro hfinite
  let _ : Finite X := hfinite
  have hzero := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at hzero
  exact (not_le_of_gt (zero_lt_one : (0 : WithBot ℕ∞) < 1)) hzero

/-- In an irreducible Noetherian T₁ space of dimension one, every proper
closed subset is finite. -/
theorem finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_eq_one
    {X : Type*} [TopologicalSpace X] [T1Space X] [IrreducibleSpace X]
    [NoetherianSpace X] (hdim : topologicalKrullDim X = 1)
    {Z : Set X} (hZclosed : IsClosed Z) (hZproper : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨S, hSfinite, hSclosed, hSirreducible, hZ⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZclosed
  rw [hZ]
  refine hSfinite.sUnion fun C hCS => ?_
  have hCZ : C ⊆ Z := by
    rw [hZ]
    exact Set.subset_sUnion_of_mem hCS
  have hCproper : C ≠ Set.univ := by
    intro hC
    apply hZproper
    exact Set.eq_univ_of_univ_subset (by simpa [hC] using hCZ)
  let C' : IrreducibleCloseds X :=
    ⟨C, hSirreducible C hCS, hSclosed C hCS⟩
  let X' : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hCX : C' < X' := by
    refine lt_of_le_of_ne (Set.subset_univ C) ?_
    intro h
    apply hCproper
    simpa [C', X'] using
      congrArg (fun W : IrreducibleCloseds X => (W : Set X)) h
  have hdim' : Order.krullDim (IrreducibleCloseds X) ≤ 1 := by
    simpa [topologicalKrullDim] using hdim.le
  have hCmin : IsMin C' :=
    (Order.krullDim_le_one_iff.mp hdim' C').resolve_right
      (fun hCmax => hCmax.not_lt hCX)
  obtain ⟨x, hxC⟩ := (hSirreducible C hCS).nonempty
  let x' : IrreducibleCloseds X := {x}
  have hxC' : x' ≤ C' := by
    intro y hy
    have hyx : y = x := by simpa [x'] using hy
    change y ∈ C
    simpa [hyx] using hxC
  have hxCeq : x' = C' := hCmin.eq_of_le hxC'
  have hC : C = {x} := by
    simpa [x', C'] using
      congrArg (fun W : IrreducibleCloseds X => (W : Set X)) hxCeq.symm
  rw [hC]
  exact Set.finite_singleton x

/-- Points are closed in projective space with its Zariski topology. -/
private theorem isClosed_singleton_projectiveSpace
    {k : Type u} [Field k] {σ : Type v} (P : ProjectiveSpace k σ) :
    IsClosed ({P} : Set (ProjectiveSpace k σ)) := by
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

/-- A quasi-projective curve has infinitely many points, and its closed sets
are exactly the whole space and the finite subsets. -/
theorem IsQuasiProjVariety.isCurve_infinite_and_isClosed_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type v} [Finite σ] {Y : Set (ProjectiveSpace k σ)}
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve) :
    Infinite Y ∧ ∀ Z : Set Y, IsClosed Z ↔ Z = Set.univ ∨ Z.Finite := by
  let _ : T1Space (ProjectiveSpace k σ) :=
    ⟨isClosed_singleton_projectiveSpace⟩
  let _ : IrreducibleSpace Y := irreducibleSpace_of_isQuasiProjVariety hY
  have hdim : topologicalKrullDim Y = 1 := hcurve
  refine ⟨infinite_of_topologicalKrullDim_eq_one Y hdim, fun Z => ?_⟩
  constructor
  · intro hZclosed
    by_cases hZproper : Z = Set.univ
    · exact Or.inl hZproper
    · exact Or.inr
        (finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_eq_one
          hdim hZclosed hZproper)
  · rintro (rfl | hZfinite)
    · exact isClosed_univ
    · exact hZfinite.isClosed

end Hartshorne
