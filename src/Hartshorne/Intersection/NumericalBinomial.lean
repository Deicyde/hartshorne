/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NumericalPolynomial
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Binomial

/-!
# Binomial expansions of numerical polynomials

Hartshorne, *Algebraic Geometry*, I.7, Proposition 7.3(a) (pp. 49–50).
-/

namespace Hartshorne

open Filter Finset Polynomial
open scoped Polynomial

/-- The polynomial `z (z - 1) ⋯ (z - r + 1) / r!`. -/
noncomputable def numericalBinomial (r : ℕ) : ℚ[X] :=
  (r.factorial : ℚ)⁻¹ • descPochhammer ℚ r

@[simp]
theorem numericalBinomial_natDegree (r : ℕ) :
    (numericalBinomial r).natDegree = r := by
  rw [numericalBinomial, Polynomial.natDegree_smul _ (by positivity)]
  exact descPochhammer_natDegree ℚ r

@[simp]
theorem numericalBinomial_leadingCoeff (r : ℕ) :
    (numericalBinomial r).leadingCoeff = (r.factorial : ℚ)⁻¹ := by
  rw [← Polynomial.coeff_natDegree, numericalBinomial_natDegree, numericalBinomial,
    Polynomial.coeff_smul]
  have h := (monic_descPochhammer ℚ r).coeff_natDegree
  rw [descPochhammer_natDegree] at h
  rw [h]
  simp

@[simp]
theorem numericalBinomial_eval_intCast (r : ℕ) (n : ℤ) :
    (numericalBinomial r).eval (n : ℚ) = ((Ring.choose n r : ℤ) : ℚ) := by
  rw [numericalBinomial, Polynomial.eval_smul]
  rw [show ((Ring.choose n r : ℤ) : ℚ) = Ring.choose (n : ℚ) r by
    exact Ring.map_choose (Int.castRingHom ℚ) n r]
  rw [Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  congr 1
  rw [← descPochhammer_map (Int.castRingHom ℚ) r,
    Polynomial.eval_map]
  simpa using Polynomial.eval₂_smulOneHom_eq_smeval ℤ (descPochhammer ℤ r) (n : ℚ)

/-- Every binomial polynomial takes integer values at integers. -/
theorem numericalBinomial_integerValued (r : ℕ) (n : ℤ) :
    ∃ m : ℤ, (numericalBinomial r).eval (n : ℚ) = (m : ℚ) :=
  ⟨Ring.choose n r, numericalBinomial_eval_intCast r n⟩

@[simp]
theorem numericalBinomial_eval_natCast (r n : ℕ) :
    (numericalBinomial r).eval (n : ℚ) = (n.choose r : ℚ) := by
  calc
    (numericalBinomial r).eval (n : ℚ) =
        ((Ring.choose (n : ℤ) r : ℤ) : ℚ) := by
      simpa using numericalBinomial_eval_intCast r (n : ℤ)
    _ = (n.choose r : ℚ) := by
      norm_cast
      exact Ring.choose_natCast (R := ℤ) n r

private noncomputable def forwardDifference (P : ℚ[X]) : ℚ[X] :=
  P.taylor 1 - P

@[simp]
private theorem forwardDifference_eval_intCast (P : ℚ[X]) (n : ℤ) :
    (forwardDifference P).eval (n : ℚ) =
      P.eval ((n + 1 : ℤ) : ℚ) - P.eval (n : ℚ) := by
  simp [forwardDifference, Polynomial.taylor_eval]

private theorem forwardDifference_isNumericalPolynomial {P : ℚ[X]}
    (hP : IsNumericalPolynomial P) : IsNumericalPolynomial (forwardDifference P) := by
  rw [IsNumericalPolynomial, Filter.eventually_atTop] at hP ⊢
  obtain ⟨N, hN⟩ := hP
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨a, ha⟩ := hN n hn
  obtain ⟨b, hb⟩ := hN (n + 1) (by omega)
  refine ⟨b - a, ?_⟩
  rw [forwardDifference_eval_intCast, hb, ha]
  norm_num

private theorem forwardDifference_natDegree_lt {P : ℚ[X]} (hP : 0 < P.natDegree) :
    (forwardDifference P).natDegree < P.natDegree := by
  have hP0 : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hP
  have hdeg : (P.taylor 1).degree = P.degree := Polynomial.degree_taylor P 1
  have hlc : (P.taylor 1).leadingCoeff = P.leadingCoeff :=
    Polynomial.leadingCoeff_taylor 1 P
  have hlt : (P.taylor 1 - P).degree < (P.taylor 1).degree :=
    Polynomial.degree_sub_lt_left hdeg
      ((Polynomial.taylor_eq_zero 1 P).not.mpr hP0) hlc
  by_cases hD : forwardDifference P = 0
  · simp [hD, hP]
  · rw [forwardDifference]
    apply (Polynomial.natDegree_lt_iff_degree_lt (by simpa [forwardDifference] using hD)).2
    rw [Polynomial.degree_taylor, Polynomial.degree_eq_natDegree hP0] at hlt
    exact hlt

private theorem isNumericalPolynomial_integerValued_aux (P : ℚ[X])
    (hP : IsNumericalPolynomial P) :
    ∀ n : ℤ, ∃ m : ℤ, P.eval (n : ℚ) = (m : ℚ) := by
  induction hdeg : P.natDegree using Nat.strong_induction_on generalizing P with
  | h d ih =>
      by_cases hd : d = 0
      · have hPdeg : P.natDegree = 0 := hdeg.trans hd
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hP
        obtain ⟨m, hm⟩ := hN N le_rfl
        intro n
        refine ⟨m, ?_⟩
        rw [Polynomial.eq_C_of_natDegree_eq_zero hPdeg] at hm ⊢
        simpa using hm
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        let D := forwardDifference P
        have hDlt : D.natDegree < d := by
          rw [← hdeg]
          exact forwardDifference_natDegree_lt (hdeg.symm ▸ hdpos)
        have hDnum : IsNumericalPolynomial D :=
          forwardDifference_isNumericalPolynomial hP
        have hDint : ∀ n : ℤ, ∃ m : ℤ, D.eval (n : ℚ) = (m : ℚ) :=
          ih D.natDegree hDlt D hDnum rfl
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hP
        obtain ⟨mN, hmN⟩ := hN N le_rfl
        intro n
        induction n using Int.inductionOn' (b := N) with
        | zero => exact ⟨mN, hmN⟩
        | succ k hk ihk =>
            obtain ⟨m, hm⟩ := ihk
            obtain ⟨a, ha⟩ := hDint k
            refine ⟨m + a, ?_⟩
            have hdiff := forwardDifference_eval_intCast P k
            change D.eval (k : ℚ) = _ at hdiff
            rw [ha, hm] at hdiff
            push_cast at hdiff ⊢
            change P.eval ((k : ℚ) + 1) = (m : ℚ) + (a : ℚ)
            change (a : ℚ) = P.eval ((k : ℚ) + 1) - (m : ℚ) at hdiff
            linarith
        | pred k hk ihk =>
            obtain ⟨m, hm⟩ := ihk
            obtain ⟨a, ha⟩ := hDint (k - 1)
            refine ⟨m - a, ?_⟩
            have hdiff := forwardDifference_eval_intCast P (k - 1)
            change D.eval ((k - 1 : ℤ) : ℚ) = _ at hdiff
            simp only [sub_add_cancel] at hdiff
            rw [ha, hm] at hdiff
            push_cast at hdiff ⊢
            change P.eval ((k : ℚ) - 1) = (m : ℚ) - (a : ℚ)
            change (a : ℚ) = (m : ℚ) - P.eval ((k : ℚ) - 1) at hdiff
            linarith

/-- Hartshorne's consequence that a numerical polynomial takes an integer
value at every integer, including negative integers. -/
theorem IsNumericalPolynomial.integerValued {P : ℚ[X]}
    (hP : IsNumericalPolynomial P) (n : ℤ) :
    ∃ m : ℤ, P.eval (n : ℚ) = (m : ℚ) :=
  isNumericalPolynomial_integerValued_aux P hP n

private theorem fwdDiffIter_zero_integerValued {P : ℚ[X]}
    (hP : ∀ n : ℤ, ∃ m : ℤ, P.eval (n : ℚ) = (m : ℚ)) (r : ℕ) :
    ∃ m : ℤ, (fwdDiff (1 : ℚ))^[r] P.eval 0 = (m : ℚ) := by
  choose value hvalue using fun n : ℕ ↦ hP n
  refine ⟨∑ k ∈ Finset.range (r + 1),
      ((-1 : ℤ) ^ (r - k) * r.choose k) * value k, ?_⟩
  rw [fwdDiff_iter_eq_sum_shift]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  simp only [zero_add, nsmul_eq_mul, mul_one]
  have hv : P.eval (k : ℚ) = (value k : ℚ) := by simpa using hvalue k
  rw [hv]
  simp

private noncomputable def newtonCoeff (P : ℚ[X]) (r : ℕ) : ℚ :=
  (fwdDiff (1 : ℚ))^[r] P.eval 0

private theorem newtonExpansion (P : ℚ[X]) :
    P = ∑ r ∈ Finset.range (P.natDegree + 1),
      newtonCoeff P r • numericalBinomial r := by
  let Q := ∑ r ∈ Finset.range (P.natDegree + 1),
    newtonCoeff P r • numericalBinomial r
  have hQdeg : Q.natDegree ≤ P.natDegree := by
    dsimp only [Q]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r hr
    exact (Polynomial.natDegree_smul_le _ _).trans <| by
      rw [numericalBinomial_natDegree]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q
      (f := fun i : Fin (P.natDegree + 1) ↦ (i : ℕ))
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_inj.mp hij
  · intro i
    have hin : (i : ℕ) ≤ P.natDegree := Nat.le_of_lt_succ i.isLt
    have hnewton := shift_eq_sum_fwdDiff_iter (h := (1 : ℚ)) P.eval (i : ℕ) 0
    simp only [zero_add, nsmul_eq_mul, mul_one] at hnewton
    have hsubset : Finset.range ((i : ℕ) + 1) ⊆
        Finset.range (P.natDegree + 1) := Finset.range_mono (Nat.add_le_add_right hin 1)
    have hsum :
        ∑ r ∈ Finset.range ((i : ℕ) + 1),
            ((i : ℕ).choose r : ℚ) * newtonCoeff P r =
          ∑ r ∈ Finset.range (P.natDegree + 1),
            ((i : ℕ).choose r : ℚ) * newtonCoeff P r := by
      apply Finset.sum_subset hsubset
      intro r hr hri
      have hir : (i : ℕ) < r := by simpa using hri
      rw [Nat.choose_eq_zero_of_lt hir]
      simp
    rw [hnewton]
    change (∑ r ∈ Finset.range ((i : ℕ) + 1),
      ((i : ℕ).choose r : ℚ) * newtonCoeff P r) = _
    rw [hsum]
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_smul,
      numericalBinomial_eval_natCast, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r hr
    exact mul_comm _ _
  · simp [hQdeg]

/-- A rational polynomial is numerical exactly when it is an integral linear
combination of the binomial polynomials, with support bounded by its degree.
The final equality records the top coefficient of the expansion. -/
theorem isNumericalPolynomial_iff_exists_binomialExpansion (P : ℚ[X]) :
    IsNumericalPolynomial P ↔
      ∃ c : ℕ → ℤ,
        (∀ r, P.natDegree < r → c r = 0) ∧
        P = ∑ r ∈ Finset.range (P.natDegree + 1),
          (c r : ℚ) • numericalBinomial r ∧
        (P.natDegree.factorial : ℚ) * P.leadingCoeff =
          (c P.natDegree : ℚ) := by
  constructor
  · intro hP
    have hPint := hP.integerValued
    choose c hc using fun r ↦ fwdDiffIter_zero_integerValued hPint r
    refine ⟨c, ?_, ?_, ?_⟩
    · intro r hr
      have hz := congrFun
        (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := P) hr) 0
      change newtonCoeff P r = 0 at hz
      have hcr : (c r : ℚ) = 0 := (hc r).symm.trans hz
      exact_mod_cast hcr
    · calc
        P = ∑ r ∈ Finset.range (P.natDegree + 1),
            newtonCoeff P r • numericalBinomial r := newtonExpansion P
        _ = ∑ r ∈ Finset.range (P.natDegree + 1),
            (c r : ℚ) • numericalBinomial r := by
          apply Finset.sum_congr rfl
          intro r hr
          have hcr : newtonCoeff P r = (c r : ℚ) := by
            simpa only [newtonCoeff] using hc r
          rw [hcr]
    · have htop : newtonCoeff P P.natDegree =
          P.leadingCoeff * (P.natDegree.factorial : ℚ) := by
        have h := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial P) 0
        change newtonCoeff P P.natDegree =
          P.leadingCoeff * (P.natDegree.factorial : ℚ) at h
        exact h
      calc
        (P.natDegree.factorial : ℚ) * P.leadingCoeff =
            P.leadingCoeff * (P.natDegree.factorial : ℚ) := mul_comm _ _
        _ = newtonCoeff P P.natDegree := htop.symm
        _ = (c P.natDegree : ℚ) := hc P.natDegree
  · rintro ⟨c, _, hP, _⟩
    rw [IsNumericalPolynomial]
    apply Filter.Eventually.of_forall
    intro n
    refine ⟨∑ r ∈ Finset.range (P.natDegree + 1),
      c r * Ring.choose n r, ?_⟩
    have hEval := congrArg (fun Q : ℚ[X] ↦ Q.eval (n : ℚ)) hP
    calc
      P.eval (n : ℚ) =
          (∑ r ∈ Finset.range (P.natDegree + 1),
            (c r : ℚ) • numericalBinomial r).eval (n : ℚ) := hEval
      _ = (∑ r ∈ Finset.range (P.natDegree + 1),
          c r * Ring.choose n r : ℤ) := by
        rw [Polynomial.eval_finsetSum]
        simp only [Polynomial.eval_smul, numericalBinomial_eval_intCast, smul_eq_mul]
        push_cast
        rfl

end Hartshorne
