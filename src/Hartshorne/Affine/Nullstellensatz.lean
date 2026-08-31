/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.VanishingIdeal

/-!
# Hilbert's Nullstellensatz

Hartshorne, *Algebraic Geometry*, I.1, Theorem 1.3A and Proposition 1.2(d)
(pp. 3-4).

Hartshorne quotes this without proof. Mathlib proves it as
`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, in the greater generality
where the ideal has coefficients in a field `k` and the points range over an
algebraically closed extension `K`, subject to `[Finite σ]`. Hartshorne's
statement is the special case `K = k` with `k` itself algebraically closed.

This file records that specialisation and restates the theorem in Hartshorne's
"vanishes on `Z(𝔞)` implies some power lies in `𝔞`" form. It proves nothing new.

## Main results

* `Hartshorne.vanishingIdeal_zeroSet_eq_radical` : `I(Z(𝔞)) = √𝔞`.
* `Hartshorne.exists_pow_mem_of_forall_eval_eq_zero` : Hartshorne's phrasing.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ]

/-- **Hilbert's Nullstellensatz**, Hartshorne 1.3A in the form of his
Proposition 1.2(d): the ideal of the zero set of `𝔞` is the radical of `𝔞`. -/
theorem vanishingIdeal_zeroSet_eq_radical (I : Ideal (MvPolynomial σ k)) :
    vanishingIdeal k (zeroSet (I : Set (MvPolynomial σ k))) = I.radical := by
  rw [← zeroLocus_eq_zeroSet]
  exact MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

/-- Hartshorne's phrasing of 1.3A: a polynomial vanishing at every point of
`Z(𝔞)` has a positive power in `𝔞`. -/
theorem exists_pow_mem_of_forall_eval_eq_zero {I : Ideal (MvPolynomial σ k)}
    {f : MvPolynomial σ k} (hf : ∀ x ∈ zeroLocus k I, eval x f = 0) :
    ∃ r : ℕ, 0 < r ∧ f ^ r ∈ I := by
  have hmem : f ∈ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I]
    intro x hx
    simpa using hf x hx
  obtain ⟨r, hr⟩ := Ideal.mem_radical_iff.1 hmem
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · -- `f ^ 0 = 1 ∈ I` forces `I = ⊤`, so `f` itself lies in `I`.
    have hI : I = ⊤ := (Ideal.eq_top_iff_one I).2 (by simpa using hr)
    exact ⟨1, one_pos, by rw [pow_one, hI]; exact Submodule.mem_top⟩
  · exact ⟨r, hpos, hr⟩

end Hartshorne
