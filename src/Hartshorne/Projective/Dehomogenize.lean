/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Chart

/-!
# Dehomogenisation

Hartshorne, *Algebraic Geometry*, I.2, the map `α` in the proof of
Proposition 2.2 (p. 10).

`α` sets `xᵢ = 1`, sending a polynomial in `x₀,…,xₙ` to one in the remaining
variables. Unlike its partner `β`, it is an algebra homomorphism, so it is the
easy half of Proposition 2.2 and gives continuity of `φᵢ⁻¹` on its own.

## Main definitions

* `Hartshorne.dehomogenize`

## Main results

* `Hartshorne.chartInv_preimage_projZeroSet` : preimages of projective algebraic
  sets under `φᵢ⁻¹` are affine algebraic sets.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- Hartshorne's `α`: substitute `1` for `xᵢ`, and keep the other variables.

This is an algebra homomorphism, which its partner `β` is not, because
homogenising has to multiply by a power of `xᵢ` depending on the degree. -/
noncomputable def dehomogenize (i : σ) :
    MvPolynomial σ k →ₐ[k] MvPolynomial {j : σ // j ≠ i} k :=
  aeval fun j => if h : j = i then 1 else X ⟨j, h⟩

@[simp]
theorem dehomogenize_X_self (i : σ) : dehomogenize (k := k) i (X i) = 1 := by
  simp [dehomogenize]

theorem dehomogenize_X_of_ne {i j : σ} (hj : j ≠ i) :
    dehomogenize (k := k) i (X j) = X ⟨j, hj⟩ := by
  simp [dehomogenize, hj]

/-- Evaluating a dehomogenised polynomial at `y` is the same as evaluating the
original at the vector with `1` in slot `i`. This is the whole point of `α`. -/
theorem eval_dehomogenize (i : σ) (y : {j : σ // j ≠ i} → k) (f : MvPolynomial σ k) :
    eval y (dehomogenize i f) = eval (chartInvVec i y) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dehomogenize]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      by_cases hj : j = i
      · subst hj
        simp [hp, chartInvVec_self]
      · rw [map_mul, map_mul, map_mul, hp, dehomogenize_X_of_ne hj]
        simp [chartInvVec_of_ne y hj]

/-- The preimage of a projective algebraic set under `φᵢ⁻¹` is cut out by the
dehomogenisations, hence is an affine algebraic set. -/
theorem chartInv_preimage_projZeroSet (i : σ) {T : Set (MvPolynomial σ k)}
    (hT : IsHomogeneousSet T) :
    chartInv i ⁻¹' projZeroSet T = zeroSet (dehomogenize i '' T) := by
  ext y
  simp only [Set.mem_preimage, mem_projZeroSet_iff, mem_zeroSet_iff, Set.mem_image]
  constructor
  · rintro h _ ⟨f, hf, rfl⟩
    rw [eval_dehomogenize]
    obtain ⟨n, hn⟩ := hT f hf
    exact (homogeneousVanish_iff_of_isHomogeneous hn (chartInvVec_ne_zero i y)).1 (h f hf)
  · intro h f hf
    obtain ⟨n, hn⟩ := hT f hf
    refine (homogeneousVanish_iff_of_isHomogeneous hn (chartInvVec_ne_zero i y)).2 ?_
    rw [← eval_dehomogenize]
    exact h _ ⟨f, hf, rfl⟩

/-- `φᵢ⁻¹ : 𝔸ⁿ → ℙⁿ` is continuous. -/
theorem continuous_chartInv (i : σ) : Continuous (chartInv (k := k) i) := by
  rw [continuous_iff_isClosed]
  intro Y hY
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_isProjAlgebraicSet.1 hY
  rw [chartInv_preimage_projZeroSet i hT]
  exact isClosed_iff_isAlgebraicSet.2 (isAlgebraicSet_zeroSet _)

end Hartshorne
