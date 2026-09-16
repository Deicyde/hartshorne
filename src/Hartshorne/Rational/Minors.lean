/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Chart

/-!
# Two points of `ℙⁿ` agree when their minors vanish

Toward Hartshorne, *Algebraic Geometry*, I.4, Lemma 4.1 (p. 24).

`P = Q` in `ℙⁿ` exactly when every `2 × 2` minor `P_l Q_m − P_m Q_l` of the pair
of coordinate vectors vanishes.

These are the equations cutting out the diagonal of `ℙⁿ × ℙⁿ` inside its Segre
image, which is how Hartshorne proves Lemma 4.1. Isolating them here means the
lemma can be proved without constructing the product variety: what the
agreement locus is cut out by is a family of equations in the *chart
coordinates* of the two maps, and this is the statement that those equations say
what they should.

## Main results

* `Hartshorne.eq_of_minors_eq_zero`
* `Hartshorne.minors_eq_zero_of_eq`
* `Hartshorne.div_minor_eq_zero_iff`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- **The minors detect equality.**

One coordinate of `P` is assumed nonzero, which is no assumption at all — some
coordinate of a point of `ℙⁿ` is — but naming it is what lets the scalar be
written down. -/
theorem eq_of_minors_eq_zero {P Q : ProjectiveSpace k σ} {i : σ} (hi : P.rep i ≠ 0)
    (h : ∀ l m : σ, P.rep l * Q.rep m = P.rep m * Q.rep l) : P = Q := by
  classical
  -- If the `i`-th coordinate of `Q` vanished, every coordinate of `Q` would.
  have hQi : Q.rep i ≠ 0 := by
    intro hz
    refine Q.rep_nonzero (funext fun m => ?_)
    have := h i m
    rw [hz, mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hi
  set a : k := Q.rep i / P.rep i with ha
  have hane : a ≠ 0 := div_ne_zero hQi hi
  have hsmul : a • P.rep = Q.rep := by
    funext m
    have hm : P.rep i * Q.rep m = P.rep m * Q.rep i := h i m
    show a * P.rep m = Q.rep m
    rw [ha, div_mul_eq_mul_div, div_eq_iff hi]
    linear_combination -hm
  have hmk : Projectivization.mk k Q.rep Q.rep_nonzero
      = Projectivization.mk k P.rep P.rep_nonzero :=
    (Projectivization.mk_eq_mk_iff k _ _ Q.rep_nonzero P.rep_nonzero).2
      ⟨Units.mk0 a hane, by simpa using hsmul⟩
  rw [P.mk_rep, Q.mk_rep] at hmk
  exact hmk.symm

/-- The converse, which is the easy direction: equal points have proportional
coordinate vectors, so every minor vanishes. -/
theorem minors_eq_zero_of_eq {P Q : ProjectiveSpace k σ} (hPQ : P = Q) (l m : σ) :
    P.rep l * Q.rep m = P.rep m * Q.rep l := by
  subst hPQ
  ring

/-- A minor, divided through by the two chosen denominators, is the same
expression over a common denominator. This is what turns the minors — which are
expressions in homogeneous coordinates and so not functions on `ℙⁿ` — into a
difference of products of chart coordinates, which are. -/
theorem div_minor {a b c d p q : k} (hp : p ≠ 0) (hq : q ≠ 0) :
    (a / p) * (d / q) - (c / p) * (b / q) = (a * d - c * b) / (p * q) := by
  field_simp

/-- So the normalised minor vanishes exactly when the minor does. -/
theorem div_minor_eq_zero_iff {a b c d p q : k} (hp : p ≠ 0) (hq : q ≠ 0) :
    (a / p) * (d / q) - (c / p) * (b / q) = 0 ↔ a * d = c * b := by
  rw [div_minor hp hq, div_eq_zero_iff, sub_eq_zero,
    or_iff_left (mul_ne_zero hp hq)]

end Hartshorne
