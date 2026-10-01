/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NumericalBinomial

/-!
# Discrete antidifferentiation of numerical polynomials

Hartshorne, *Algebraic Geometry*, I.7, Proposition 7.3(b) (p. 50).
-/

namespace Hartshorne

open Filter Finset Polynomial
open scoped Polynomial

/-- The forward difference `P(z + 1) - P(z)` of a rational polynomial. -/
noncomputable def polynomialForwardDifference (P : ℚ[X]) : ℚ[X] :=
  P.taylor 1 - P

@[simp]
theorem polynomialForwardDifference_eval (P : ℚ[X]) (x : ℚ) :
    (polynomialForwardDifference P).eval x = P.eval (x + 1) - P.eval x := by
  simp [polynomialForwardDifference, Polynomial.taylor_eval]

private theorem numericalBinomial_eval (r : ℕ) (x : ℚ) :
    (numericalBinomial r).eval x = Ring.choose x r := by
  rw [numericalBinomial, Polynomial.eval_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  congr 1
  rw [← descPochhammer_map (Int.castRingHom ℚ) r, Polynomial.eval_map]
  simpa using Polynomial.eval₂_smulOneHom_eq_smeval ℤ (descPochhammer ℤ r) x

/-- Forward difference lowers the index of a binomial polynomial by one. -/
theorem polynomialForwardDifference_numericalBinomial_succ (r : ℕ) :
    polynomialForwardDifference (numericalBinomial (r + 1)) = numericalBinomial r := by
  apply Polynomial.funext
  intro x
  rw [polynomialForwardDifference_eval, numericalBinomial_eval,
    numericalBinomial_eval, numericalBinomial_eval]
  rw [Ring.choose_succ_succ]
  abel

private noncomputable def binomialAntidifference (Q : ℚ[X]) (c : ℕ → ℤ) : ℚ[X] :=
  ∑ r ∈ Finset.range (Q.natDegree + 1),
    (c r : ℚ) • numericalBinomial (r + 1)

private theorem polynomialForwardDifference_binomialAntidifference
    {Q : ℚ[X]} {c : ℕ → ℤ}
    (hQ : Q = ∑ r ∈ Finset.range (Q.natDegree + 1),
      (c r : ℚ) • numericalBinomial r) :
    polynomialForwardDifference (binomialAntidifference Q c) = Q := by
  calc
    polynomialForwardDifference (binomialAntidifference Q c) =
        ∑ r ∈ Finset.range (Q.natDegree + 1),
          (c r : ℚ) • numericalBinomial r := by
      simp only [polynomialForwardDifference, binomialAntidifference, map_sum, map_smul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← smul_sub]
      change (c r : ℚ) •
        polynomialForwardDifference (numericalBinomial (r + 1)) = _
      rw [polynomialForwardDifference_numericalBinomial_succ]
    _ = Q := hQ.symm

private theorem binomialAntidifference_isNumericalPolynomial
    (Q : ℚ[X]) (c : ℕ → ℤ) :
    IsNumericalPolynomial (binomialAntidifference Q c) := by
  rw [IsNumericalPolynomial]
  apply Filter.Eventually.of_forall
  intro n
  refine ⟨∑ r ∈ Finset.range (Q.natDegree + 1), c r * Ring.choose n (r + 1), ?_⟩
  simp only [binomialAntidifference, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    numericalBinomial_eval_intCast, smul_eq_mul]
  push_cast
  rfl

private theorem binomialAntidifference_natDegree
    (Q : ℚ[X]) (c : ℕ → ℤ) (hc : c Q.natDegree ≠ 0) :
    (binomialAntidifference Q c).natDegree = Q.natDegree + 1 := by
  have hlow :
      (∑ r ∈ Finset.range Q.natDegree,
        (c r : ℚ) • numericalBinomial (r + 1)).natDegree ≤ Q.natDegree := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r hr
    exact (Polynomial.natDegree_smul_le _ _).trans <| by
      rw [numericalBinomial_natDegree]
      exact Finset.mem_range.mp hr
  have hcast : (c Q.natDegree : ℚ) ≠ 0 := by exact_mod_cast hc
  have htop :
      ((c Q.natDegree : ℚ) •
        numericalBinomial (Q.natDegree + 1)).natDegree = Q.natDegree + 1 := by
    rw [Polynomial.natDegree_smul _ hcast, numericalBinomial_natDegree]
  rw [binomialAntidifference, Finset.sum_range_succ]
  rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt
    (hlow.trans_lt (htop.symm ▸ Nat.lt_succ_self Q.natDegree)), htop]

private theorem binomialAntidifference_leadingCoeff
    (Q : ℚ[X]) (c : ℕ → ℤ) (hc : c Q.natDegree ≠ 0) :
    (binomialAntidifference Q c).leadingCoeff =
      (c Q.natDegree : ℚ) * ((Q.natDegree + 1).factorial : ℚ)⁻¹ := by
  have hlow :
      (∑ r ∈ Finset.range Q.natDegree,
        (c r : ℚ) • numericalBinomial (r + 1)).natDegree ≤ Q.natDegree := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r hr
    exact (Polynomial.natDegree_smul_le _ _).trans <| by
      rw [numericalBinomial_natDegree]
      exact Finset.mem_range.mp hr
  have hcast : (c Q.natDegree : ℚ) ≠ 0 := by exact_mod_cast hc
  have htop :
      ((c Q.natDegree : ℚ) •
        numericalBinomial (Q.natDegree + 1)).natDegree = Q.natDegree + 1 := by
    rw [Polynomial.natDegree_smul _ hcast, numericalBinomial_natDegree]
  have hdegrees :
      (∑ r ∈ Finset.range Q.natDegree,
        (c r : ℚ) • numericalBinomial (r + 1)).degree <
      ((c Q.natDegree : ℚ) •
        numericalBinomial (Q.natDegree + 1)).degree :=
    Polynomial.degree_lt_degree (hlow.trans_lt (htop.symm ▸ Nat.lt_succ_self Q.natDegree))
  rw [binomialAntidifference, Finset.sum_range_succ,
    Polynomial.leadingCoeff_add_of_degree_lt hdegrees]
  rw [Polynomial.leadingCoeff, htop, Polynomial.coeff_smul]
  rw [show (numericalBinomial (Q.natDegree + 1)).coeff (Q.natDegree + 1) =
      ((Q.natDegree + 1).factorial : ℚ)⁻¹ by
    have hcoeff := Polynomial.coeff_natDegree
      (p := numericalBinomial (Q.natDegree + 1))
    rw [numericalBinomial_natDegree, numericalBinomial_leadingCoeff] at hcoeff
    exact hcoeff]
  simp [smul_eq_mul]

/-- A numerical polynomial has a numerical polynomial antidifference.  The
identity is an equality of polynomials, and for a nonzero input the degree and
leading coefficient have the expected values. -/
theorem exists_isNumericalPolynomial_forwardDifference_eq (Q : ℚ[X])
    (hQ : IsNumericalPolynomial Q) :
    ∃ P : ℚ[X],
      IsNumericalPolynomial P ∧
      polynomialForwardDifference P = Q ∧
      (Q ≠ 0 →
        P.natDegree = Q.natDegree + 1 ∧
        P.leadingCoeff = Q.leadingCoeff / (Q.natDegree + 1 : ℚ)) := by
  obtain ⟨c, _, hcQ, hctop⟩ :=
    (isNumericalPolynomial_iff_exists_binomialExpansion Q).mp hQ
  let P := binomialAntidifference Q c
  refine ⟨P, binomialAntidifference_isNumericalPolynomial Q c,
    polynomialForwardDifference_binomialAntidifference hcQ, ?_⟩
  intro hQ0
  have hQlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ0
  have hc : c Q.natDegree ≠ 0 := by
    intro hc0
    rw [hc0, Int.cast_zero] at hctop
    exact hQlc (mul_eq_zero.mp hctop |>.resolve_left (by positivity))
  refine ⟨binomialAntidifference_natDegree Q c hc, ?_⟩
  rw [binomialAntidifference_leadingCoeff Q c hc, ← hctop, Nat.factorial_succ]
  push_cast
  field_simp

private theorem isNumericalPolynomial_add_intConstant {P : ℚ[X]}
    (hP : IsNumericalPolynomial P) (a : ℤ) :
    IsNumericalPolynomial (P + Polynomial.C (a : ℚ)) := by
  rw [IsNumericalPolynomial]
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨m, hm⟩ := hP.integerValued n
  refine ⟨m + a, ?_⟩
  simp [hm]

private theorem polynomialForwardDifference_add_constant (P : ℚ[X]) (a : ℚ) :
    polynomialForwardDifference (P + Polynomial.C a) = polynomialForwardDifference P := by
  simp [polynomialForwardDifference]

/-- If the eventual first difference of an integer-valued function is given
by a numerical polynomial, then the function is eventually represented by a
numerical polynomial. -/
theorem exists_isNumericalPolynomial_eventuallyEq_of_diff
    (f : ℤ → ℤ) (Q : ℚ[X]) (hQ : IsNumericalPolynomial Q)
    (hdiff : ∀ᶠ n : ℤ in Filter.atTop,
      ((f (n + 1) - f n : ℤ) : ℚ) = Q.eval (n : ℚ)) :
    ∃ P : ℚ[X],
      IsNumericalPolynomial P ∧
      (∀ᶠ n : ℤ in Filter.atTop, P.eval (n : ℚ) = (f n : ℚ)) ∧
      polynomialForwardDifference P = Q ∧
      (Q ≠ 0 →
        P.natDegree = Q.natDegree + 1 ∧
        P.leadingCoeff = Q.leadingCoeff / (Q.natDegree + 1 : ℚ)) := by
  obtain ⟨A, hA, hAdiff, hA_degree⟩ :=
    exists_isNumericalPolynomial_forwardDifference_eq Q hQ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hdiff
  obtain ⟨aN, haN⟩ := hA.integerValued N
  let a : ℤ := f N - aN
  let P : ℚ[X] := A + Polynomial.C (a : ℚ)
  have hP : IsNumericalPolynomial P :=
    isNumericalPolynomial_add_intConstant hA a
  have hPdiff : polynomialForwardDifference P = Q := by
    change polynomialForwardDifference (A + Polynomial.C (a : ℚ)) = Q
    rw [polynomialForwardDifference_add_constant, hAdiff]
  have hPeventually :
      ∀ᶠ n : ℤ in Filter.atTop, P.eval (n : ℚ) = (f n : ℚ) := by
    refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
    intro n hn
    refine Int.leInduction (motive := fun n _ ↦
      P.eval (n : ℚ) = (f n : ℚ)) ?_ ?_ n hn
    · simp [P, a, haN]
    · intro k hk ih
      have hf := hN k hk
      have hp := congrArg (fun R : ℚ[X] ↦ R.eval (k : ℚ)) hPdiff
      rw [polynomialForwardDifference_eval] at hp
      push_cast at hf ⊢
      change P.eval ((k : ℚ) + 1) = (f (k + 1) : ℚ)
      linarith
  refine ⟨P, hP, hPeventually, hPdiff, ?_⟩
  intro hQ0
  obtain ⟨hAdeg, hAlc⟩ := hA_degree hQ0
  have hPdeg : P.natDegree = Q.natDegree + 1 := by
    change (A + Polynomial.C (a : ℚ)).natDegree = Q.natDegree + 1
    rw [Polynomial.natDegree_add_C]
    exact hAdeg
  refine ⟨hPdeg, ?_⟩
  have hA0 : A ≠ 0 := Polynomial.ne_zero_of_natDegree_gt <| by
    rw [hAdeg]
    exact Nat.succ_pos Q.natDegree
  have hApos : 0 < A.degree := by
    rw [Polynomial.degree_eq_natDegree hA0, hAdeg]
    exact_mod_cast Nat.succ_pos Q.natDegree
  have hPlc : P.leadingCoeff = A.leadingCoeff := by
    change (A + Polynomial.C (a : ℚ)).leadingCoeff = A.leadingCoeff
    exact Polynomial.leadingCoeff_add_of_degree_lt'
      (Polynomial.degree_C_le.trans_lt hApos)
  exact hPlc.trans hAlc

end Hartshorne
