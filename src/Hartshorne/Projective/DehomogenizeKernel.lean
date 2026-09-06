/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Dehomogenize

/-!
# The kernel of dehomogenisation

Toward Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.6 (pp. 11-12).

`α` sets `xᵢ = 1`, and the only thing it forgets is exactly that: its kernel is
the principal ideal `(xᵢ − 1)`.

The proof is one induction. Setting `xᵢ = 1` and then renaming the surviving
variables back into `S` is an endomorphism `ρ` of `S`, and `g − ρ(g)` always lies
in `(xᵢ − 1)`: true on constants, additive, and multiplicative because
`gh − ρ(g)ρ(h) = (g − ρ(g))h + ρ(g)(h − ρ(h))`. A polynomial in the kernel has
`ρ(g) = 0`, so it *is* `g − ρ(g)`.

This is what makes `xᵢ − 1` visible as a hypersurface section of the affine cone:
`S(Y)/(xᵢ − 1) ≅ A(Yᵢ)`, and Krull's principal ideal theorem then says the
dimension drops by exactly one.

## Main results

* `Hartshorne.ker_dehomogenize`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- Setting `xᵢ = 1`, then reading the answer back inside `S`. -/
noncomputable def dehomogenizeRetract (i : σ) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  (rename Subtype.val).comp (dehomogenize i)

@[simp]
theorem dehomogenizeRetract_X_self (i : σ) :
    dehomogenizeRetract (k := k) i (X i) = 1 := by
  simp [dehomogenizeRetract]

theorem dehomogenizeRetract_X_of_ne {i j : σ} (hj : j ≠ i) :
    dehomogenizeRetract (k := k) i (X j) = X j := by
  simp [dehomogenizeRetract, dehomogenize_X_of_ne hj]

/-- `ρ` is trivial exactly on the polynomials `α` kills. -/
theorem dehomogenizeRetract_eq_zero_iff (i : σ) {g : MvPolynomial σ k} :
    dehomogenizeRetract i g = 0 ↔ dehomogenize i g = 0 := by
  rw [dehomogenizeRetract, AlgHom.comp_apply]
  exact ⟨fun h => rename_injective _ Subtype.val_injective (by simpa using h),
    fun h => by rw [h, map_zero]⟩

/-- **Setting `xᵢ = 1` changes a polynomial only by a multiple of `xᵢ − 1`.**

Both sides are additive and the difference is multiplicative up to terms already
of that shape, so the induction only has to check the variables. -/
theorem sub_dehomogenizeRetract_mem_span (i : σ) (g : MvPolynomial σ k) :
    g - dehomogenizeRetract i g ∈ Ideal.span {(X i - 1 : MvPolynomial σ k)} := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [dehomogenizeRetract]
  | add p q hp hq =>
      have hsplit : p + q - dehomogenizeRetract i (p + q)
          = (p - dehomogenizeRetract i p) + (q - dehomogenizeRetract i q) := by
        rw [map_add]; ring
      rw [hsplit]
      exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
      have hsplit : p * X j - dehomogenizeRetract i (p * X j)
          = (p - dehomogenizeRetract i p) * X j
            + dehomogenizeRetract i p * (X j - dehomogenizeRetract i (X j)) := by
        rw [map_mul]; ring
      rw [hsplit]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
      by_cases hj : j = i
      · subst hj
        rw [dehomogenizeRetract_X_self]
        exact Ideal.mem_span_singleton_self _
      · rw [dehomogenizeRetract_X_of_ne hj, sub_self]
        exact Ideal.zero_mem _

/-- **The kernel of `α` is `(xᵢ − 1)`.** -/
theorem ker_dehomogenize (i : σ) :
    RingHom.ker (dehomogenize (k := k) i).toRingHom
      = Ideal.span {(X i - 1 : MvPolynomial σ k)} := by
  refine le_antisymm (fun g hg => ?_) ?_
  · have h := sub_dehomogenizeRetract_mem_span i g
    rw [(dehomogenizeRetract_eq_zero_iff i).2 hg, sub_zero] at h
    exact h
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    simp

end Hartshorne
