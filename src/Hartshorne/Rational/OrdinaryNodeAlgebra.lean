/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Hartshorne.Projective.Basic

/-!
# Polynomial algebra for the blow-up of a plane double point

Toward Hartshorne, *Algebraic Geometry*, I, Exercise 5.6(b).

Let `g ∈ k[x₀, x₁]` have no constant and no linear term, and a nonzero
quadratic term.  On the blow-up chart in which the `j`-th direction coordinate
is `1`, the points over a point `x` of the plane are written `x = t • w(u)`,
where `w(u)` has `j`-th coordinate `1` and other coordinate `u`.  Then
`g(t • w(u)) = t² · g̃ⱼ(t, u)`, where

`g̃ⱼ(t, u) = ∑_{d ≥ 2} t^{d-2} g_d(w(u))`

and `g_d` is the degree-`d` homogeneous component of `g`.  This file proves
the polynomial facts about `g̃ⱼ` used for the blow-up of a node:

* the identity `g(t • w(u)) = t² g̃ⱼ(t, u)` and the restriction
  `g̃ⱼ(0, u) = g₂(w(u))`;
* if `g` is irreducible, so is `g̃ⱼ`;
* nonzero binary quadratic forms over an algebraically closed field are
  products of two linear forms, and the zeros of linear forms behave as
  expected.
-/

namespace Hartshorne

namespace OrdinaryNode

open MvPolynomial

universe u

variable {k : Type u} [Field k]

/-! ## Evaluation helpers -/

theorem eval_aeval_eq {σ τ : Type*} (x : τ → k) (s : σ → MvPolynomial τ k)
    (p : MvPolynomial σ k) :
    eval x (aeval s p) = eval (fun i => eval x (s i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The other index of `Fin 2`. -/
theorem fin_two_eq_or_eq_rev (i j : Fin 2) : i = j ∨ i = j.rev := by
  fin_cases i <;> fin_cases j <;> simp

theorem fin_two_rev_ne (j : Fin 2) : j.rev ≠ j := by
  fin_cases j <;> decide

/-- The direction vector of the `j`-th blow-up chart: coordinate `j` is `1`
and the other coordinate is `u`. -/
def chartVec (j : Fin 2) (u : k) : Fin 2 → k :=
  fun i => if i = j then 1 else u

/-- The polynomial version of `chartVec`, with `u = X 1`. -/
noncomputable def chartPoly (j : Fin 2) : Fin 2 → MvPolynomial (Fin 2) k :=
  fun i => if i = j then 1 else X 1

@[simp]
theorem chartVec_self (j : Fin 2) (u : k) : chartVec j u j = 1 := by
  simp [chartVec]

@[simp]
theorem chartVec_rev (j : Fin 2) (u : k) : chartVec j u j.rev = u := by
  simp [chartVec, fin_two_rev_ne j]

theorem chartVec_ne_zero (j : Fin 2) (u : k) : chartVec j u ≠ 0 := by
  intro h
  have := congrFun h j
  simp at this

theorem eval_chartPoly (v : Fin 2 → k) (j i : Fin 2) :
    eval v (chartPoly j i) = chartVec j (v 1) i := by
  unfold chartPoly chartVec
  split_ifs <;> simp

/-- Every vector with nonzero `j`-th coordinate is a multiple of a chart
vector. -/
theorem eq_smul_chartVec (x : Fin 2 → k) {j : Fin 2} (hx : x j ≠ 0) :
    x = x j • chartVec j (x j.rev / x j) := by
  funext i
  rcases fin_two_eq_or_eq_rev i j with rfl | rfl
  · simp
  · simp only [Pi.smul_apply, smul_eq_mul, chartVec_rev]
    field_simp

/-! ## Homogeneous components -/

theorem sum_Ico_eq_sum_range {M : Type*} [AddCommMonoid M] (h : ℕ → M)
    (h0 : h 0 = 0) (h1 : h 1 = 0) (N : ℕ) :
    ∑ d ∈ Finset.Ico 2 N, h d = ∑ d ∈ Finset.range N, h d := by
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    simp only [Finset.mem_Ico] at hd
    simpa using hd.2
  · intro d hd hnot
    simp only [Finset.mem_range] at hd
    simp only [Finset.mem_Ico, not_and, not_lt] at hnot
    have : d < 2 := by
      by_contra hge
      exact absurd (hnot (by omega)) (by omega)
    interval_cases d
    · exact h0
    · exact h1

theorem eval_eq_sum_Ico (g : MvPolynomial (Fin 2) k)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (x : Fin 2 → k) :
    eval x g = ∑ d ∈ Finset.Ico 2 (g.totalDegree + 1),
      eval x (homogeneousComponent d g) := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [map_sum]
  exact (sum_Ico_eq_sum_range (fun d => eval x (homogeneousComponent d g))
    (by simp [hg0]) (by simp [hg1]) _).symm

theorem two_le_totalDegree (g : MvPolynomial (Fin 2) k)
    (hg2 : homogeneousComponent 2 g ≠ 0) : 2 ≤ g.totalDegree := by
  by_contra h
  exact hg2 (homogeneousComponent_eq_zero 2 g (by omega))

/-! ## The chart equation -/

/-- The equation `g̃ⱼ` of the strict transform of `g = 0` on the `j`-th
blow-up chart, in coordinates `(t, u) = (X 0, X 1)`. -/
noncomputable def chartEq (j : Fin 2) (g : MvPolynomial (Fin 2) k) :
    MvPolynomial (Fin 2) k :=
  ∑ d ∈ Finset.Ico 2 (g.totalDegree + 1),
    X 0 ^ (d - 2) * aeval (chartPoly j) (homogeneousComponent d g)

theorem eval_chartEq (j : Fin 2) (g : MvPolynomial (Fin 2) k) (v : Fin 2 → k) :
    eval v (chartEq j g) = ∑ d ∈ Finset.Ico 2 (g.totalDegree + 1),
      v 0 ^ (d - 2) * eval (chartVec j (v 1)) (homogeneousComponent d g) := by
  simp only [chartEq, map_sum, map_mul, map_pow, eval_X, eval_aeval_eq,
    eval_chartPoly]

/-- `g(t • w(u)) = t² g̃ⱼ(t, u)`. -/
theorem eval_smul_chartVec (j : Fin 2) (g : MvPolynomial (Fin 2) k)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (v : Fin 2 → k) :
    eval (v 0 • chartVec j (v 1)) g = v 0 ^ 2 * eval v (chartEq j g) := by
  rw [eval_eq_sum_Ico g hg0 hg1, eval_chartEq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd2 : 2 ≤ d := (Finset.mem_Ico.1 hd).1
  rw [(homogeneousComponent_isHomogeneous d g).eval_smul]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd2
  simp only [Nat.add_sub_cancel_left, pow_add]
  ring

/-- `g̃ⱼ(0, u) = g₂(w(u))`. -/
theorem eval_chartEq_of_eq_zero (j : Fin 2) (g : MvPolynomial (Fin 2) k)
    (v : Fin 2 → k) (hv : v 0 = 0) :
    eval v (chartEq j g) =
      eval (chartVec j (v 1)) (homogeneousComponent 2 g) := by
  rw [eval_chartEq, hv]
  by_cases hN : 2 ≤ g.totalDegree
  · rw [Finset.sum_eq_single 2]
    · simp
    · intro d hd hne
      have : 2 < d := lt_of_le_of_ne (Finset.mem_Ico.1 hd).1 (Ne.symm hne)
      rw [zero_pow (by omega), zero_mul]
    · intro h
      exact absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) h
  · rw [homogeneousComponent_eq_zero 2 g (by omega), map_zero]
    apply Finset.sum_eq_zero
    intro d hd
    have := Finset.mem_Ico.1 hd
    omega

/-- The chart substitution `x_j ↦ t`, `x_{j'} ↦ t u`. -/
noncomputable def chartSubst (j : Fin 2) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval fun i => X 0 * chartPoly j i

theorem eval_chartSubst (j : Fin 2) (p : MvPolynomial (Fin 2) k) (v : Fin 2 → k) :
    eval v (chartSubst j p) = eval (v 0 • chartVec j (v 1)) p := by
  rw [chartSubst, eval_aeval_eq]
  congr 2
  funext i
  simp [eval_chartPoly]

@[simp]
theorem chartSubst_X_self (j : Fin 2) :
    chartSubst (k := k) j (X j) = X 0 := by
  simp [chartSubst, chartPoly]

@[simp]
theorem chartSubst_X_rev (j : Fin 2) :
    chartSubst (k := k) j (X j.rev) = X 0 * X 1 := by
  simp [chartSubst, chartPoly, fin_two_rev_ne j]

section Infinite

variable [Infinite k]

theorem chartSubst_eq (j : Fin 2) (g : MvPolynomial (Fin 2) k)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0) :
    chartSubst j g = X 0 ^ 2 * chartEq j g := by
  apply MvPolynomial.funext
  intro v
  rw [eval_chartSubst, eval_smul_chartVec j g hg0 hg1]
  simp

/-- A polynomial vanishing wherever the `j`-th coordinate is nonzero is zero. -/
theorem eq_zero_of_eval_eq_zero_of_ne (j : Fin 2) (p : MvPolynomial (Fin 2) k)
    (h : ∀ x : Fin 2 → k, x j ≠ 0 → eval x p = 0) : p = 0 := by
  have hXp : X j * p = 0 := by
    apply MvPolynomial.funext
    intro x
    by_cases hx : x j = 0
    · simp [hx]
    · simp [h x hx]
  rcases mul_eq_zero.1 hXp with hX | hp
  · exact absurd hX (X_ne_zero j)
  · exact hp

theorem chartSubst_injective (j : Fin 2) :
    Function.Injective (chartSubst (k := k) j) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  apply eq_zero_of_eval_eq_zero_of_ne j p
  intro x hx
  have h := congrArg (eval ![x j, x j.rev / x j]) hp
  rw [eval_chartSubst, map_zero] at h
  simpa [← eq_smul_chartVec x hx] using h

/-- A homogeneous polynomial vanishing at every chart vector is zero. -/
theorem eq_zero_of_eval_chartVec {n : ℕ} (j : Fin 2) {q : MvPolynomial (Fin 2) k}
    (hq : q.IsHomogeneous n) (h : ∀ u : k, eval (chartVec j u) q = 0) : q = 0 := by
  apply eq_zero_of_eval_eq_zero_of_ne j q
  intro x hx
  rw [eq_smul_chartVec x hx, hq.eval_smul, h, mul_zero]

end Infinite

theorem exists_chartSubst_eq (j : Fin 2) (a : MvPolynomial (Fin 2) k) :
    ∃ (n : ℕ) (A : MvPolynomial (Fin 2) k), chartSubst j A = X 0 ^ n * a := by
  induction a using MvPolynomial.induction_on with
  | C c => exact ⟨0, C c, by simp [chartSubst]⟩
  | add a b ha hb =>
      obtain ⟨n, A, hA⟩ := ha
      obtain ⟨m, B, hB⟩ := hb
      refine ⟨n + m, X j ^ m * A + X j ^ n * B, ?_⟩
      simp only [map_add, map_mul, map_pow, chartSubst_X_self, hA, hB]
      ring
  | mul_X a i ha =>
      obtain ⟨n, A, hA⟩ := ha
      fin_cases i
      · refine ⟨n, A * X j, ?_⟩
        simp only [map_mul, chartSubst_X_self, hA]
        simp only [Fin.zero_eta]
        ring
      · refine ⟨n + 1, A * X j.rev, ?_⟩
        simp only [map_mul, chartSubst_X_rev, hA]
        simp only [Fin.mk_one]
        ring

section Irreducible

variable [IsAlgClosed k]

theorem chartEq_ne_zero (j : Fin 2) (g : MvPolynomial (Fin 2) k)
    (hg2 : homogeneousComponent 2 g ≠ 0) : chartEq j g ≠ 0 := by
  intro h
  apply hg2
  apply eq_zero_of_eval_chartVec j (homogeneousComponent_isHomogeneous 2 g)
  intro u
  have := congrArg (eval ![0, u]) h
  rw [eval_chartEq_of_eq_zero j g _ (by simp), map_zero] at this
  simpa using this

theorem not_X_zero_dvd_chartEq (j : Fin 2) (g : MvPolynomial (Fin 2) k)
    (hg2 : homogeneousComponent 2 g ≠ 0) : ¬ (X 0 ∣ chartEq j g) := by
  rintro ⟨c, hc⟩
  apply hg2
  apply eq_zero_of_eval_chartVec j (homogeneousComponent_isHomogeneous 2 g)
  intro u
  have := congrArg (eval ![0, u]) hc
  rw [eval_chartEq_of_eq_zero j g _ (by simp)] at this
  simpa using this

/-- **The chart equation of an irreducible double point is irreducible.** -/
theorem irreducible_chartEq (j : Fin 2) {g : MvPolynomial (Fin 2) k}
    (hg : Irreducible g)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (hg2 : homogeneousComponent 2 g ≠ 0) : Irreducible (chartEq j g) := by
  have hE := chartSubst_eq j g hg0 hg1
  have hEne := chartEq_ne_zero j g hg2
  have hgprime : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.1 hg
  have hdeg : 2 ≤ g.totalDegree := two_le_totalDegree g hg2
  -- `g` does not divide the coordinate `x_j`.
  have hgXj : ¬ g ∣ X j := by
    rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc
    have := congrArg totalDegree hc
    rw [totalDegree_mul_of_isDomain hg.ne_zero hc0, totalDegree_X] at this
    omega
  -- A factor of the chart equation dividing a power of `t` is a unit.
  have hunit_of_dvd : ∀ b : MvPolynomial (Fin 2) k, b ∣ chartEq j g →
      ∀ n : ℕ, b ∣ X 0 ^ n → IsUnit b := by
    intro b hb n hbn
    obtain ⟨i, -, hi⟩ := (dvd_prime_pow (X_prime (σ := Fin 2) (R := k) (i := 0)) n).1 hbn
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using hi.isUnit_iff.2 isUnit_one
    · exfalso
      apply not_X_zero_dvd_chartEq j g hg2
      refine dvd_trans ?_ hb
      exact (dvd_pow_self (X 0) hpos.ne').trans hi.symm.dvd
  -- The key cancellation, for a factor whose complementary lift is divisible by `g`.
  have hkey : ∀ a b : MvPolynomial (Fin 2) k, chartEq j g = a * b →
      ∀ (n : ℕ) (A : MvPolynomial (Fin 2) k), chartSubst j A = X 0 ^ n * a →
      g ∣ A → IsUnit b := by
    intro a b hab n A hA hgA
    obtain ⟨A', rfl⟩ := hgA
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hEne (by simp [hab])
    rw [map_mul, hE, hab] at hA
    have hcancel : a * (X 0 ^ 2 * b * chartSubst j A') = a * X 0 ^ n := by
      linear_combination hA
    have hb' := mul_left_cancel₀ ha0 hcancel
    exact hunit_of_dvd b ⟨a, by rw [hab]; ring⟩ n
      ⟨X 0 ^ 2 * chartSubst j A', by rw [← hb']; ring⟩
  refine ⟨?_, ?_⟩
  · -- Not a unit: otherwise `g` would be a constant multiple of `x_j²`.
    intro hunit
    obtain ⟨c, -, hc⟩ := (isUnit_iff_eq_C_of_isReduced (P := chartEq j g)).1 hunit
    have hlift : chartSubst j g = chartSubst j (C c * X j * X j) := by
      rw [hE, hc]
      simp only [map_mul, chartSubst_X_self, algHom_C, algebraMap_eq]
      ring
    have hg' := chartSubst_injective j hlift
    have hXj : ¬ IsUnit (X j : MvPolynomial (Fin 2) k) := (X_prime (i := j)).not_isUnit
    rcases hg.isUnit_or_isUnit hg' with h | h
    · exact hXj (isUnit_of_mul_isUnit_right h)
    · exact hXj h
  · intro a b hab
    obtain ⟨n, A, hA⟩ := exists_chartSubst_eq j a
    obtain ⟨m, B, hB⟩ := exists_chartSubst_eq j b
    have hlift : chartSubst j (X j ^ (n + m) * g) = chartSubst j (X j ^ 2 * A * B) := by
      simp only [map_mul, map_pow, chartSubst_X_self, hE, hA, hB, hab]
      ring
    have hrel := chartSubst_injective j hlift
    have hdvd : g ∣ X j ^ 2 * A * B := ⟨X j ^ (n + m), by rw [← hrel]; ring⟩
    rcases hgprime.dvd_or_dvd hdvd with h | hB'
    · rcases hgprime.dvd_or_dvd h with h' | hA'
      · exact absurd (hgprime.dvd_of_dvd_pow h') hgXj
      · exact Or.inr (hkey a b hab n A hA hA')
    · exact Or.inl (hkey b a (by rw [hab, mul_comm]) m B hB hB')

end Irreducible

/-! ## Binary linear and quadratic forms -/

theorem fin_two_finsupp_eq (m : Fin 2 →₀ ℕ) :
    m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
  ext i
  fin_cases i <;> simp

theorem fin_two_degree (m : Fin 2 →₀ ℕ) : m.degree = m 0 + m 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem isHomogeneous_coeff_ne_zero {p : MvPolynomial (Fin 2) k} {n : ℕ}
    (hp : p.IsHomogeneous n) {m : Fin 2 →₀ ℕ} (hm : coeff m p ≠ 0) :
    m 0 + m 1 = n := by
  have := hp hm
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this

/-- A binary linear form in explicit coordinates. -/
theorem eq_linear_of_isHomogeneous_one {l : MvPolynomial (Fin 2) k}
    (hl : l.IsHomogeneous 1) :
    l = C (coeff (Finsupp.single 0 1) l) * X 0 +
      C (coeff (Finsupp.single 1 1) l) * X 1 := by
  ext m
  simp only [coeff_add, coeff_C_mul, coeff_X]
  by_cases h0 : Finsupp.single 0 1 = m
  · subst h0
    have : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
      intro h
      have := congrArg (fun f => f 0) h
      simp at this
    simp [this]
  by_cases h1 : Finsupp.single 1 1 = m
  · subst h1
    simp [h0]
  simp only [h0, h1, if_false, mul_zero, add_zero]
  by_contra hne
  have hdeg := isHomogeneous_coeff_ne_zero hl hne
  rw [fin_two_finsupp_eq m] at h0 h1
  rcases Nat.eq_zero_or_pos (m 0) with h | h
  · rw [h] at hdeg h1
    simp only [zero_add] at hdeg
    rw [hdeg] at h1
    simp at h1
  · have : m 0 = 1 := by omega
    have hm1 : m 1 = 0 := by omega
    rw [this, hm1] at h0
    simp at h0

theorem eval_linear (a b : k) (y : Fin 2 → k) :
    eval y (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) k) = a * y 0 + b * y 1 := by
  simp

theorem isHomogeneous_linear (a b : k) :
    (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) k).IsHomogeneous 1 := by
  have h0 : (C a * X 0 : MvPolynomial (Fin 2) k).IsHomogeneous 1 := by
    simpa using (isHomogeneous_C (Fin 2) a).mul (isHomogeneous_X k (0 : Fin 2))
  have h1 : (C b * X 1 : MvPolynomial (Fin 2) k).IsHomogeneous 1 := by
    simpa using (isHomogeneous_C (Fin 2) b).mul (isHomogeneous_X k (1 : Fin 2))
  exact h0.add h1

/-- A binary quadratic form in explicit coordinates. -/
theorem eq_quadratic_of_isHomogeneous_two {q : MvPolynomial (Fin 2) k}
    (hq : q.IsHomogeneous 2) :
    q = C (coeff (Finsupp.single 0 2) q) * X 0 ^ 2 +
      C (coeff (Finsupp.single 0 1 + Finsupp.single 1 1) q) * (X 0 * X 1) +
      C (coeff (Finsupp.single 1 2) q) * X 1 ^ 2 := by
  have hX2 : ∀ i : Fin 2, (X i ^ 2 : MvPolynomial (Fin 2) k) =
      monomial (Finsupp.single i 2) 1 := fun i => by
    rw [X_pow_eq_monomial]
  have hXX : (X 0 * X 1 : MvPolynomial (Fin 2) k) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [X, X, monomial_mul, one_mul]
  rw [hX2, hX2, hXX]
  ext m
  simp only [coeff_add, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero]
  have key : ∀ s : Fin 2 →₀ ℕ,
      (if s = m then coeff s q else 0) = if s = m then coeff m q else 0 := by
    intro s
    split_ifs with h
    · rw [h]
    · rfl
  rw [key, key, key]
  have hm := fin_two_finsupp_eq m
  by_cases hc : coeff m q = 0
  · simp [hc]
  · have hdeg := isHomogeneous_coeff_ne_zero hq hc
    have hcases : (m 0 = 2 ∧ m 1 = 0) ∨ (m 0 = 1 ∧ m 1 = 1) ∨ (m 0 = 0 ∧ m 1 = 2) := by
      omega
    rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h0, h1] at hm
      simp only [Finsupp.single_zero, add_zero] at hm
      subst hm
      simp [Finsupp.ext_iff, Fin.forall_fin_two]
    · rw [h0, h1] at hm
      subst hm
      simp [Finsupp.ext_iff, Fin.forall_fin_two]
    · rw [h0, h1] at hm
      simp only [Finsupp.single_zero, zero_add] at hm
      subst hm
      simp [Finsupp.ext_iff, Fin.forall_fin_two]

/-- Over an algebraically closed field every binary quadratic form is a product
of two linear forms. -/
theorem exists_linear_factors [IsAlgClosed k] {q : MvPolynomial (Fin 2) k}
    (hq : q.IsHomogeneous 2) :
    ∃ l₁ l₂ : MvPolynomial (Fin 2) k,
      l₁.IsHomogeneous 1 ∧ l₂.IsHomogeneous 1 ∧ q = l₁ * l₂ := by
  have hq' := eq_quadratic_of_isHomogeneous_two hq
  generalize coeff (Finsupp.single 0 2) q = a at hq'
  generalize coeff (Finsupp.single 0 1 + Finsupp.single 1 1) q = b at hq'
  generalize coeff (Finsupp.single 1 2) q = c at hq'
  by_cases ha : a = 0
  · refine ⟨C 0 * X 0 + C 1 * X 1, C b * X 0 + C c * X 1,
      isHomogeneous_linear _ _, isHomogeneous_linear _ _, ?_⟩
    rw [hq', ha]
    simp only [map_zero, map_one]
    ring
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root
      (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c)
      (by rw [Polynomial.degree_quadratic ha]; decide)
    have hr' : a * r ^ 2 + b * r + c = 0 := by
      simpa [Polynomial.IsRoot] using hr
    refine ⟨C 1 * X 0 + C (-r) * X 1, C a * X 0 + C (b + a * r) * X 1,
      isHomogeneous_linear _ _, isHomogeneous_linear _ _, ?_⟩
    rw [hq']
    have hC : (C (a * r ^ 2 + b * r + c) : MvPolynomial (Fin 2) k) = 0 := by
      rw [hr', map_zero]
    simp only [map_add, map_mul, map_pow, map_neg, map_one] at hC ⊢
    linear_combination (X 1 : MvPolynomial (Fin 2) k) ^ 2 * hC

/-- Two vectors annihilated by the same nonzero binary linear form have
vanishing minor. -/
theorem minor_eq_zero_of_linear {a b : k} (hab : a ≠ 0 ∨ b ≠ 0) {y y' : Fin 2 → k}
    (hy : a * y 0 + b * y 1 = 0) (hy' : a * y' 0 + b * y' 1 = 0) :
    y 0 * y' 1 = y 1 * y' 0 := by
  have h1 : a * (y 0 * y' 1 - y 1 * y' 0) = 0 := by
    linear_combination y' 1 * hy - y 1 * hy'
  have h2 : b * (y 0 * y' 1 - y 1 * y' 0) = 0 := by
    linear_combination y 0 * hy' - y' 0 * hy
  rcases hab with ha | hb
  · exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left ha)
  · exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hb)

/-- Two nonzero binary linear forms with a common nonzero zero are associated. -/
theorem associated_of_common_zero {a₁ b₁ a₂ b₂ : k} (h₁ : a₁ ≠ 0 ∨ b₁ ≠ 0)
    (h₂ : a₂ ≠ 0 ∨ b₂ ≠ 0) {y : Fin 2 → k} (hy : y ≠ 0)
    (hy₁ : a₁ * y 0 + b₁ * y 1 = 0) (hy₂ : a₂ * y 0 + b₂ * y 1 = 0) :
    Associated (C a₁ * X 0 + C b₁ * X 1 : MvPolynomial (Fin 2) k)
      (C a₂ * X 0 + C b₂ * X 1) := by
  have hdet : a₁ * b₂ = a₂ * b₁ := by
    have e1 : y 0 * (a₁ * b₂ - a₂ * b₁) = 0 := by
      linear_combination b₂ * hy₁ - b₁ * hy₂
    have e2 : y 1 * (a₁ * b₂ - a₂ * b₁) = 0 := by
      linear_combination a₁ * hy₂ - a₂ * hy₁
    by_cases hy0 : y 0 = 0
    · have hy1 : y 1 ≠ 0 := by
        intro hy1
        exact hy (funext fun i => by fin_cases i <;> simp [hy0, hy1])
      exact sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left hy1)
    · exact sub_eq_zero.1 ((mul_eq_zero.1 e1).resolve_left hy0)
  have hscale : ∃ c : k, c ≠ 0 ∧ a₂ = c * a₁ ∧ b₂ = c * b₁ := by
    rcases h₁ with ha | hb
    · refine ⟨a₂ / a₁, ?_, by field_simp, ?_⟩
      · intro hc
        rcases div_eq_zero_iff.1 hc with ha2 | ha1
        · rcases h₂ with h | h
          · exact h ha2
          · apply h
            have : a₁ * b₂ = 0 := by rw [hdet, ha2, zero_mul]
            exact (mul_eq_zero.1 this).resolve_left ha
        · exact ha ha1
      · field_simp
        linear_combination hdet
    · refine ⟨b₂ / b₁, ?_, ?_, by field_simp⟩
      · intro hc
        rcases div_eq_zero_iff.1 hc with hb2 | hb1
        · rcases h₂ with h | h
          · apply h
            have : a₂ * b₁ = 0 := by rw [← hdet, hb2, mul_zero]
            exact (mul_eq_zero.1 this).resolve_right hb
          · exact h hb2
        · exact hb hb1
      · field_simp
        linear_combination -hdet
  obtain ⟨c, hc, rfl, rfl⟩ := hscale
  refine ⟨((isUnit_iff_ne_zero.2 hc).map (C : k →+* MvPolynomial (Fin 2) k)).unit, ?_⟩
  simp only [IsUnit.unit_spec, map_mul]
  ring

omit [Field k] in
theorem fin_two_vec_ext {x y : Fin 2 → k} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- Two nonzero vectors with vanishing minor are proportional. -/
theorem exists_smul_of_minor_eq {x y : Fin 2 → k} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x 0 * y 1 = x 1 * y 0) : ∃ c : k, c ≠ 0 ∧ x = c • y := by
  by_cases hy0 : y 0 = 0
  · have hy1 : y 1 ≠ 0 := fun hy1 => hy (fin_two_vec_ext (by simp [hy0]) (by simp [hy1]))
    have hx0 : x 0 = 0 := by
      rw [hy0, mul_zero] at h
      exact (mul_eq_zero.1 h).resolve_right hy1
    refine ⟨x 1 / y 1, ?_, fin_two_vec_ext ?_ ?_⟩
    · intro hc
      rcases div_eq_zero_iff.1 hc with hx1 | hy1'
      · exact hx (fin_two_vec_ext (by simp [hx0]) (by simp [hx1]))
      · exact hy1 hy1'
    · simp [hx0, hy0]
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨x 0 / y 0, ?_, fin_two_vec_ext ?_ ?_⟩
    · intro hc
      rcases div_eq_zero_iff.1 hc with hx0 | hy0'
      · have hx1 : x 1 = 0 := by
          rw [hx0, zero_mul] at h
          exact (mul_eq_zero.1 h.symm).resolve_right hy0
        exact hx (fin_two_vec_ext (by simp [hx0]) (by simp [hx1]))
      · exact hy0 hy0'
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h.symm

/-! ## The derivative of the chart equation along the exceptional curve -/

theorem eval_pderiv_chartEq_of_eq_zero (j : Fin 2) (g : MvPolynomial (Fin 2) k)
    (v : Fin 2 → k) (hv : v 0 = 0) :
    eval v (pderiv 1 (chartEq j g)) =
      eval v (pderiv 1 (aeval (chartPoly j) (homogeneousComponent 2 g))) := by
  have hX : ∀ n : ℕ, pderiv (1 : Fin 2) (X 0 ^ n : MvPolynomial (Fin 2) k) = 0 := by
    intro n
    rw [Derivation.leibniz_pow, pderiv_X_of_ne (by decide)]
    simp
  simp only [chartEq, map_sum, Derivation.leibniz, hX, smul_eq_mul, mul_zero,
    add_zero, map_mul, map_pow, eval_X, hv]
  by_cases hN : 2 ≤ g.totalDegree
  · rw [Finset.sum_eq_single 2]
    · simp
    · intro d hd hne
      have : 2 < d := lt_of_le_of_ne (Finset.mem_Ico.1 hd).1 (Ne.symm hne)
      rw [zero_pow (by omega), zero_mul]
    · intro h
      exact absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) h
  · rw [homogeneousComponent_eq_zero 2 g (by omega), map_zero, map_zero, map_zero]
    apply Finset.sum_eq_zero
    intro d hd
    have := Finset.mem_Ico.1 hd
    omega

theorem eval_pderiv_aeval_mul (j : Fin 2) (l₁ l₂ : MvPolynomial (Fin 2) k) (u : k)
    (h₁ : eval (chartVec j u) l₁ = 0) :
    eval ![0, u] (pderiv 1 (aeval (chartPoly j) (l₁ * l₂))) =
      eval (chartVec j u) l₂ * eval ![0, u] (pderiv 1 (aeval (chartPoly j) l₁)) := by
  have hev : ∀ p : MvPolynomial (Fin 2) k,
      eval ![0, u] (aeval (chartPoly j) p) = eval (chartVec j u) p := by
    intro p
    rw [eval_aeval_eq]
    congr 2
    funext i
    rw [eval_chartPoly]
    rfl
  rw [map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
    hev l₁, h₁, zero_mul, zero_add, hev l₂]

/-- The derivative in `u` of a linear form restricted to the `j`-th chart is the
coefficient of the other coordinate. -/
theorem eval_pderiv_aeval_linear (j : Fin 2) (a b u : k) :
    eval ![0, u] (pderiv 1 (aeval (chartPoly j) (C a * X 0 + C b * X 1 :
      MvPolynomial (Fin 2) k))) = if j = 0 then b else a := by
  fin_cases j <;>
    simp [chartPoly, Derivation.leibniz]

end OrdinaryNode

end Hartshorne
