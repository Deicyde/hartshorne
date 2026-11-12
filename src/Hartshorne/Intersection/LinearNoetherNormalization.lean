/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Hartshorne.Scheme.ProjectiveSpaceChart

/-!
# A linear form of Noether normalization

Let `k` be an infinite field and `f` a nonzero polynomial in the variables `x_i` (`i ∈ τ`) and
`t`. For `c : τ → k` the linear change of coordinates `x_i ↦ x_i + c_i t`, `t ↦ t`
(`optionShear c`) is a `k`-algebra automorphism of `k[x, t]`. If `d` is the total degree of `f`
and `f_d` its top homogeneous component, then `f(x + c t, t)`, as a polynomial in `t` over
`k[x]`, has degree at most `d` and coefficient `f_d(c, 1)` in degree `d`. Since `k` is infinite,
`f_d(c, 1) ≠ 0` for some `c`, and then `f(x + c t, t)` is a nonzero constant times a polynomial
monic in `t` (`exists_optionShear_leadingCoeff_eq_C`).
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {τ : Type*}

/-- The `k`-algebra endomorphism `x_i ↦ x_i + c_i t`, `t ↦ t` of `k[x_i : i ∈ τ][t]`, written on
`MvPolynomial (Option τ) k` with `t = X none`. -/
noncomputable def optionShearHom (c : τ → k) :
    MvPolynomial (Option τ) k →ₐ[k] MvPolynomial (Option τ) k :=
  aeval fun o => Option.elim o (X none) fun i => X (some i) + C (c i) * X none

@[simp]
theorem optionShearHom_X_none (c : τ → k) : optionShearHom c (X none) = X none := by
  simp [optionShearHom]

@[simp]
theorem optionShearHom_X_some (c : τ → k) (i : τ) :
    optionShearHom c (X (some i)) = X (some i) + C (c i) * X none := by
  simp [optionShearHom]

theorem optionShearHom_comp_neg (c : τ → k) :
    (optionShearHom c).comp (optionShearHom (-c)) = AlgHom.id k _ := by
  ext o : 1
  cases o with
  | none => simp
  | some i =>
    simp only [AlgHom.comp_apply, optionShearHom_X_some, Pi.neg_apply, map_add, map_mul,
      optionShearHom_X_none, AlgHom.id_apply]
    rw [show (optionShearHom c) (C (-c i)) = C (-c i) from (optionShearHom c).commutes _, C_neg]
    ring

/-- **The linear change of coordinates** `x_i ↦ x_i + c_i t`, `t ↦ t`, a `k`-algebra
automorphism of `k[x_i : i ∈ τ][t]` with inverse `x_i ↦ x_i - c_i t`. -/
noncomputable def optionShear (c : τ → k) :
    MvPolynomial (Option τ) k ≃ₐ[k] MvPolynomial (Option τ) k :=
  AlgEquiv.ofAlgHom (optionShearHom c) (optionShearHom (-c)) (optionShearHom_comp_neg c)
    (by simpa using optionShearHom_comp_neg (-c))

theorem optionShear_apply (c : τ → k) (f : MvPolynomial (Option τ) k) :
    optionShear c f = optionShearHom c f :=
  rfl

section Degree

variable (c : τ → k)

/-- The sheared polynomial as a polynomial in `t` over `k[x]`. -/
private noncomputable abbrev shearPoly :
    MvPolynomial (Option τ) k →ₐ[k] Polynomial (MvPolynomial τ k) :=
  (optionEquivLeft k τ).toAlgHom.comp (optionShearHom c)

/-- The point `(c, 1)`. -/
private def shearPoint : Option τ → k := fun o => Option.elim o 1 c

private theorem shearPoly_X (o : Option τ) :
    (shearPoly c (X o)).natDegree ≤ 1 ∧
      (shearPoly c (X o)).coeff 1 = C (shearPoint c o) := by
  cases o with
  | none =>
    have h : shearPoly c (X none) = Polynomial.X := by
      change optionEquivLeft k τ (optionShearHom c (X none)) = _
      rw [optionShearHom_X_none, optionEquivLeft_X_none]
    rw [h]
    exact ⟨Polynomial.natDegree_X_le, by simp [shearPoint]⟩
  | some i =>
    have h : shearPoly c (X (some i)) =
        Polynomial.C (C (c i)) * Polynomial.X + Polynomial.C (X i) := by
      change optionEquivLeft k τ (optionShearHom c (X (some i))) = _
      rw [optionShearHom_X_some, map_add, map_mul, optionEquivLeft_X_some,
        optionEquivLeft_X_none, optionEquivLeft_C]
      ring
    rw [h]
    refine ⟨Polynomial.natDegree_linear_le, ?_⟩
    simp [shearPoint, Polynomial.coeff_C]

private theorem natDegree_mul_le_and_coeff {R : Type*} [CommRing R] {p q : Polynomial R}
    {e e' : ℕ} (hp : p.natDegree ≤ e) (hq : q.natDegree ≤ e') :
    (p * q).natDegree ≤ e + e' ∧ (p * q).coeff (e + e') = p.coeff e * q.coeff e' :=
  ⟨Polynomial.natDegree_mul_le.trans (add_le_add hp hq),
    Polynomial.coeff_mul_add_eq_of_natDegree_le hp hq⟩

private theorem shearPoly_prod (m : Option τ →₀ ℕ) (s : Finset (Option τ)) :
    (∏ o ∈ s, shearPoly c (X o) ^ m o).natDegree ≤ ∑ o ∈ s, m o ∧
      (∏ o ∈ s, shearPoly c (X o) ^ m o).coeff (∑ o ∈ s, m o) =
        C (∏ o ∈ s, shearPoint c o ^ m o) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert o s ho ih =>
    rw [Finset.prod_insert ho, Finset.sum_insert ho, Finset.prod_insert ho]
    have hpow : (shearPoly c (X o) ^ m o).natDegree ≤ m o * 1 ∧
        (shearPoly c (X o) ^ m o).coeff (m o * 1) =
          (shearPoly c (X o)).coeff 1 ^ m o :=
      ⟨Polynomial.natDegree_pow_le_of_le _ (shearPoly_X c o).1,
        Polynomial.coeff_pow_of_natDegree_le (shearPoly_X c o).1⟩
    rw [mul_one] at hpow
    obtain ⟨h1, h2⟩ := natDegree_mul_le_and_coeff hpow.1 ih.1
    refine ⟨h1, ?_⟩
    rw [h2, hpow.2, ih.2, (shearPoly_X c o).2, ← map_pow, ← map_mul]

private theorem shearPoly_monomial (m : Option τ →₀ ℕ) (a : k) :
    (shearPoly c (monomial m a)).natDegree ≤ m.degree ∧
      (shearPoly c (monomial m a)).coeff m.degree =
        C (eval (shearPoint c) (monomial m a)) := by
  have hdeg : m.degree = ∑ o ∈ m.support, m o := rfl
  rw [monomial_eq, map_mul, map_finsuppProd, eval_mul, eval_C, Finsupp.prod, Finsupp.prod,
    map_prod, hdeg]
  simp only [map_pow]
  obtain ⟨h1, h2⟩ := shearPoly_prod c m m.support
  have hC : shearPoly c (C a) = Polynomial.C (C a) := by
    change optionEquivLeft k τ (optionShearHom c (C a)) = _
    rw [show (optionShearHom c) (C a) = C a from (optionShearHom c).commutes _, optionEquivLeft_C]
  rw [hC]
  refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans h1, ?_⟩
  rw [Polynomial.coeff_C_mul, h2, ← map_mul]
  simp [eval_X]

/-- The sheared polynomial has degree at most `d = deg f` in `t`, with coefficient `f_d(c, 1)`
in degree `d`. -/
private theorem shearPoly_natDegree_le_and_coeff (f : MvPolynomial (Option τ) k) :
    (shearPoly c f).natDegree ≤ f.totalDegree ∧
      (shearPoly c f).coeff f.totalDegree =
        C (eval (shearPoint c) (homogeneousComponent f.totalDegree f)) := by
  classical
  have hf : shearPoly c f = ∑ m ∈ f.support, shearPoly c (monomial m (coeff m f)) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
  rw [hf]
  constructor
  · refine (Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_)
    exact (shearPoly_monomial c m _).1.trans (le_totalDegree hm)
  · rw [Polynomial.finsetSum_coeff, homogeneousComponent_apply]
    simp only [map_sum]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    split_ifs with h
    · rw [← h]
      exact (shearPoly_monomial c m _).2
    · have hlt : m.degree < f.totalDegree := lt_of_le_of_ne (le_totalDegree hm) h
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((shearPoly_monomial c m _).1.trans_lt hlt)]

end Degree

/-- A nonzero homogeneous polynomial over an infinite field does not vanish at some point with
last coordinate `1`. -/
theorem exists_eval_option_elim_ne_zero [Infinite k] {h : MvPolynomial (Option τ) k} {d : ℕ}
    (hh : h.IsHomogeneous d) (h0 : h ≠ 0) :
    ∃ c : τ → k, eval (fun o => Option.elim o 1 c) h ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h0
  have hmul : h * X none = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero, eval_mul, eval_X]
    by_cases hx : x none = 0
    · rw [hx, mul_zero]
    · have hscale : x = fun o => x none * Option.elim o 1 (fun i => x (some i) / x none) := by
        funext o
        cases o with
        | none => simp
        | some i => simp [mul_div_cancel₀ _ hx]
      have := isHomogeneous_eval₂_mul_left hh (RingHom.id k)
        (fun o => Option.elim o 1 (fun i => x (some i) / x none)) (x none)
      rw [← hscale] at this
      change eval x h = _ at this
      rw [this, show eval₂ (RingHom.id k) _ h = eval _ h from rfl, hc, mul_zero, zero_mul]
  exact (mul_eq_zero.mp hmul).resolve_right (X_ne_zero _)

/-- **Linear Noether normalization.** Let `k` be infinite and `f ≠ 0` in `k[x_i : i ∈ τ][t]`.
For some `c : τ → k`, the polynomial `f(x + c t, t)`, viewed as a polynomial in `t` over `k[x]`,
has a nonzero constant leading coefficient. -/
theorem exists_optionShear_leadingCoeff_eq_C [Infinite k] {f : MvPolynomial (Option τ) k}
    (hf : f ≠ 0) : ∃ (c : τ → k) (u : k), u ≠ 0 ∧
      (optionEquivLeft k τ (optionShear c f)).leadingCoeff = C u := by
  classical
  set d := f.totalDegree
  have hhom : homogeneousComponent d f ≠ 0 := by
    obtain ⟨m, hm, hmd⟩ : ∃ m ∈ f.support, m.degree = d := by
      obtain ⟨m, hm, h⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
        (fun s => s.sum fun _ e => e)
      exact ⟨m, hm, h.symm⟩
    intro h0
    have := congrArg (coeff m) h0
    rw [coeff_homogeneousComponent, if_pos hmd, coeff_zero] at this
    exact (mem_support_iff.mp hm) this
  obtain ⟨c, hc⟩ := exists_eval_option_elim_ne_zero (homogeneousComponent_isHomogeneous d f) hhom
  refine ⟨c, _, hc, ?_⟩
  obtain ⟨h1, h2⟩ := shearPoly_natDegree_le_and_coeff c f
  have hne : (shearPoly c f).coeff d ≠ 0 := by
    rw [h2, Ne, C_eq_zero]
    exact hc
  change (shearPoly c f).leadingCoeff = _
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero h1 hne, h2]
  rfl

end Hartshorne
