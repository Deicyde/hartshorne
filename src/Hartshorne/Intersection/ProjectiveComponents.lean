/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ProjectiveIntersectionChart

/-!
# Finite projective component decompositions

The irreducible components of a projective algebraic set, packaged as a finite
indexing set with their carriers viewed in the ambient projective space.
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u

/-- The finite set of irreducible components of a subset of projective space. -/
noncomputable def projectiveComponents
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    (Y : Set (ProjectiveSpace k σ)) :
    Finset (irreducibleComponents ↥Y) := by
  classical
  letI : Fintype (irreducibleComponents ↥Y) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.fintype
  exact Finset.univ

@[simp]
theorem mem_projectiveComponents
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    (Y : Set (ProjectiveSpace k σ)) (W : irreducibleComponents ↥Y) :
    W ∈ projectiveComponents Y := by
  classical
  unfold projectiveComponents
  simp

/-- A subset of projective space is the union of the ambient carriers of all
its irreducible components. -/
theorem iUnion_projectiveComponentCarrier_eq
    {k : Type u} [Field k] {σ : Type}
    (Y : Set (ProjectiveSpace k σ)) :
    (⋃ W : irreducibleComponents ↥Y, projectiveComponentCarrier W.1) = Y := by
  apply Set.Subset.antisymm
  · rintro P hP
    obtain ⟨W, hP⟩ := Set.mem_iUnion.mp hP
    obtain ⟨p, _, rfl⟩ := hP
    exact p.2
  · intro P hPY
    let p : ↥Y := ⟨P, hPY⟩
    have hp : p ∈ ⋃₀ irreducibleComponents ↥Y := by
      rw [sUnion_irreducibleComponents]
      trivial
    obtain ⟨W, hW, hpW⟩ := Set.mem_sUnion.mp hp
    apply Set.mem_iUnion.2
    exact ⟨⟨W, hW⟩, ⟨p, hpW, rfl⟩⟩

/-- The same component-cover equality, indexed by the finite projective
component package. -/
theorem iUnion_projectiveComponents_eq
    {k : Type u} [Field k] {σ : Type} [Finite σ]
    (Y : Set (ProjectiveSpace k σ)) :
    (⋃ W ∈ projectiveComponents Y, projectiveComponentCarrier W.1) = Y := by
  simpa only [mem_projectiveComponents, iUnion_true] using
    iUnion_projectiveComponentCarrier_eq Y

end

end Hartshorne
