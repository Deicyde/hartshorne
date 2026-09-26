/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.FunctionFieldDVR
import Hartshorne.Projective.Basic

/-!
# A projective coordinate pivot at a function-field DVR

Hartshorne, *Algebraic Geometry*, I.6, Proposition 6.8 (pp. 43--44).

A finite nonzero family of homogeneous coordinates can be normalized at a
function-field DVR by dividing by a coordinate of extremal valuation.  Every
normalized coordinate then belongs to the valuation ring, while the pivot
coordinate is one.  In particular, applying a residue map leaves a nonzero
coordinate vector.
-/

namespace Hartshorne

universe u v w

namespace FunctionFieldDVR

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- A finite nonzero family of homogeneous coordinates has a pivot whose
normalized coordinates all belong to a given function-field DVR.  The pivot
itself is nonzero and normalizes to one, which supplies the nonvanishing
coordinate after residue evaluation. -/
theorem exists_projective_pivot {ι : Type w} [Finite ι]
    (R : FunctionFieldDVR k K) (f : ι → K) (hf : f ≠ 0) :
    ∃ j : ι, f j ≠ 0 ∧
      (∀ i : ι, f i / f j ∈ R.toValuationSubring) ∧
      f j / f j = 1 := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
  let _ : Nonempty ι := ⟨i⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
    (fun a ↦ R.toValuationSubring.valuation (f a)) Finset.univ_nonempty
  have hfj : f j ≠ 0 := by
    intro hzero
    have hle := hj i (Finset.mem_univ i)
    rw [hzero, map_zero] at hle
    exact hi ((map_eq_zero R.toValuationSubring.valuation).mp
      (le_antisymm hle zero_le))
  refine ⟨j, hfj, ?_, div_self hfj⟩
  intro a
  rw [← R.toValuationSubring.valuation_le_one_iff,
    R.toValuationSubring.valuation.map_div,
    div_le_one₀ (pos_iff_ne_zero.mpr
      ((map_eq_zero R.toValuationSubring.valuation).not.mpr hfj))]
  exact hj a (Finset.mem_univ a)

end FunctionFieldDVR

end Hartshorne
