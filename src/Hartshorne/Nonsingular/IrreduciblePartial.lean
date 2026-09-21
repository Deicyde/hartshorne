/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# An irreducible polynomial has a nonzero partial derivative

Hartshorne, *Algebraic Geometry*, I.5, proof of Theorem 5.3 (p. 33).

Over a perfect field, an irreducible multivariate polynomial has a nonzero
partial derivative.  In characteristic zero, vanishing of all partials forces
the polynomial to be constant.  In characteristic `p`, it forces every
monomial exponent to be divisible by `p`; perfectness of the coefficient field
then makes the polynomial a `p`th power.

The algebraically closed case used by Hartshorne follows because algebraically
closed fields are perfect.

## Main result

* `Hartshorne.exists_pderiv_ne_zero_of_irreducible`: an irreducible polynomial
  over an algebraically closed field has a nonzero partial derivative.
-/

open scoped BigOperators
open Finsupp

namespace Hartshorne

/-- If all partial derivatives vanish in characteristic `p`, every exponent of
every monomial in the support is divisible by `p`. -/
private lemma exponent_dvd_of_forall_pderiv_eq_zero
    {k σ : Type*} [Field k] {p : ℕ} [CharP k p]
    {f : MvPolynomial σ k} (h : ∀ i, MvPolynomial.pderiv i f = 0)
    {m : σ →₀ ℕ} (hm : m ∈ f.support) (i : σ) : p ∣ m i := by
  by_contra hdvd
  have hi : m i ≠ 0 := by
    intro hi
    exact hdvd (by simp [hi])
  have hcoeff : MvPolynomial.coeff m f ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using hm
  have hcast : (m i : k) ≠ 0 :=
    (CharP.cast_eq_zero_iff k p (m i)).not.mpr hdvd
  let d : σ →₀ ℕ := m - single i 1
  have heq := congrArg (MvPolynomial.coeff d) (h i)
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero,
    show d + single i 1 = m from Finsupp.sub_add_single_one_cancel hi] at heq
  have hnat : d i + 1 = m i := by
    simp [d]
    omega
  have hexp : ((d i : k) + 1) = (m i : k) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ ↦ (n : k)) hnat
  rw [hexp] at heq
  exact hcoeff (mul_eq_zero.mp heq |>.resolve_right hcast)

/-- In positive characteristic over a perfect field, a polynomial whose
partials all vanish is a power of exponent equal to the characteristic. -/
private lemma exists_pow_eq_of_forall_pderiv_eq_zero
    {k σ : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [PerfectRing k p] {f : MvPolynomial σ k}
    (h : ∀ i, MvPolynomial.pderiv i f = 0) :
    ∃ g : MvPolynomial σ k, g ^ p = f := by
  let rootIndex : (σ →₀ ℕ) → (σ →₀ ℕ) := fun m ↦
    m.mapRange (fun n ↦ n / p) (Nat.zero_div p)
  let g : MvPolynomial σ k := ∑ m ∈ f.support,
    MvPolynomial.monomial (rootIndex m)
      ((frobeniusEquiv k p).symm (MvPolynomial.coeff m f))
  refine ⟨g, ?_⟩
  rw [← MvPolynomial.map_frobenius_expand p]
  simp only [g, map_sum, MvPolynomial.map_monomial,
    MvPolynomial.expand_monomial]
  calc
    _ = ∑ m ∈ f.support,
        MvPolynomial.monomial m (MvPolynomial.coeff m f) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hindex : p • rootIndex m = m := by
        ext i
        simp only [rootIndex, smul_eq_mul, Finsupp.smul_apply,
          Finsupp.mapRange_apply]
        exact Nat.mul_div_cancel'
          (exponent_dvd_of_forall_pderiv_eq_zero h hm i)
      rw [hindex, frobenius_apply_frobeniusEquiv_symm]
    _ = f := f.as_sum.symm

/-- Over a perfect field, every irreducible multivariate polynomial has a
nonzero partial derivative. -/
theorem exists_pderiv_ne_zero_of_irreducible_of_perfectField
    {k σ : Type*} [Field k] [PerfectField k] {f : MvPolynomial σ k}
    (hf : Irreducible f) : ∃ i, MvPolynomial.pderiv i f ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · let _ : CharZero k := hzero
    have hsupp : ∀ m ∈ f.support, m = 0 := by
      intro m hm
      ext i
      exact Nat.eq_zero_of_zero_dvd
        (exponent_dvd_of_forall_pderiv_eq_zero hn hm i)
    have hconst : f = MvPolynomial.C (MvPolynomial.coeff 0 f) := by
      simpa using MvPolynomial.eq_monomial_of_support_subset_singleton hsupp
    apply hf.not_isUnit
    rw [hconst]
    apply IsUnit.map
    apply isUnit_iff_ne_zero.mpr
    intro hc
    apply hf.ne_zero
    rw [hconst, hc, MvPolynomial.C_0]
  · let _ : Fact p.Prime := hp
    let _ : CharP k p := hchar
    obtain ⟨g, hg⟩ := exists_pow_eq_of_forall_pderiv_eq_zero p hn
    rw [← hg] at hf
    exact not_irreducible_pow hp.out.ne_one hf

/-- **Hartshorne I.5, proof of Theorem 5.3.** An irreducible polynomial over
an algebraically closed field has a nonzero partial derivative. -/
theorem exists_pderiv_ne_zero_of_irreducible
    {k σ : Type*} [Field k] [IsAlgClosed k] {f : MvPolynomial σ k}
    (hf : Irreducible f) : ∃ i, MvPolynomial.pderiv i f ≠ 0 :=
  exists_pderiv_ne_zero_of_irreducible_of_perfectField hf

end Hartshorne
