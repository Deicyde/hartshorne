/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.TensorProduct.Free

/-!
# The trace exponential and the reciprocal characteristic determinant

Hartshorne, *Algebraic Geometry*, Appendix C, Lemma 4.1 (p. 455): for an
endomorphism `φ` of a finite-dimensional vector space over a field of
characteristic zero,
`exp (∑_{r ≥ 1} Tr (φ ^ r) t ^ r / r) = det (1 - t φ)⁻¹` in `K⟦t⟧`.

The proof compares logarithmic derivatives.  Writing `D = det (1 - t M)` for a
matrix `M`, Jacobi's formula (obtained from Mathlib's first-order expansion of
`det (1 + s N)` after a Taylor shift `t ↦ t + s`) together with the geometric
series `(1 - t M)⁻¹ = ∑ t ^ k M ^ k` gives `D' = -(∑ Tr (M ^ (k + 1)) t ^ k) D`.
The exponential side has the same logarithmic derivative by the chain rule, so
the product of the exponential with `D` has derivative zero and constant term
one.
-/

namespace Hartshorne

noncomputable section

open PowerSeries Matrix
open scoped TensorProduct

variable {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix geometric series `∑ t ^ k M ^ k`, entrywise a power series. -/
private def geomMatrix (M : Matrix n n K) : Matrix n n K⟦X⟧ :=
  Matrix.of fun i j => PowerSeries.mk fun k => (M ^ k) i j

private lemma one_sub_X_smul_mul_geomMatrix (M : Matrix n n K) :
    (1 - (X : K⟦X⟧) • M.map (C (R := K))) * geomMatrix M = 1 := by
  ext i j k
  rw [sub_mul, one_mul, smul_mul_assoc]
  rcases k with _ | k
  · simp [geomMatrix, one_apply]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, coeff_succ_X_mul]
    simp [geomMatrix, mul_apply, coeff_C_mul, pow_succ', one_apply, map_sum]
    split_ifs <;> simp [coeff_one]

private lemma trace_geomMatrix_mul (M : Matrix n n K) :
    trace (geomMatrix M * M.map (C (R := K))) = PowerSeries.mk fun k => trace (M ^ (k + 1)) := by
  ext k
  simp [trace, geomMatrix, mul_apply, map_sum, coeff_mul_C, pow_succ]

open Polynomial in
private lemma derivative_det_one_sub_X_smul (M : Matrix n n K) :
    d⁄dX K (det (1 - (PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C (R := K)))) =
      -(PowerSeries.mk fun k => trace (M ^ (k + 1))) *
        det (1 - (PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C (R := K))) := by
  set A : Matrix n n K⟦X⟧ := 1 - (PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C (R := K))
  set P : K[X] := det (1 - (Polynomial.X : K[X]) • M.map Polynomial.C) with hP
  have hPA : (P : K⟦X⟧) = det A := by
    rw [hP, ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    by_cases h : i = j <;> simp [A, one_apply, h] <;> ring
  set N : Matrix n n K⟦X⟧ := M.map PowerSeries.C with hN
  set B := geomMatrix M with hB
  have hAB : A * B = 1 := one_sub_X_smul_mul_geomMatrix M
  have key : (Polynomial.derivative P : K⟦X⟧) = det A * (-trace (B * N)) := by
    rw [← eval₂_C_X_eq_coe, ← Polynomial.eval_map, ← Polynomial.derivative_map,
      ← Polynomial.taylor_coeff_one]
    have h1 : Polynomial.taylor (PowerSeries.X : K⟦X⟧) (P.map PowerSeries.C) =
        det (1 - (Polynomial.X + Polynomial.C PowerSeries.X : K⟦X⟧[X]) • N.map Polynomial.C) := by
      rw [Polynomial.taylor_apply, hP, ← Polynomial.coe_mapRingHom, RingHom.map_det,
        ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
      congr 1
      refine Matrix.ext fun i j => ?_
      by_cases h : i = j <;> simp [N, one_apply, h] <;> ring
    have hAm : A.map (Polynomial.C (R := K⟦X⟧)) =
        1 - (Polynomial.C (PowerSeries.X : K⟦X⟧) : K⟦X⟧[X]) • N.map Polynomial.C := by
      refine Matrix.ext fun i j => ?_
      by_cases h : i = j <;> simp [A, N, one_apply, h]
    have h2 : (1 - (Polynomial.X + Polynomial.C PowerSeries.X : K⟦X⟧[X]) • N.map Polynomial.C) =
        A.map Polynomial.C * (1 + (Polynomial.X : K⟦X⟧[X]) • (-(B * N)).map Polynomial.C) := by
      rw [mul_add, mul_one, Matrix.mul_smul, ← Matrix.map_mul, mul_neg, ← mul_assoc, hAB, one_mul,
        Matrix.map_neg (hf := fun a => map_neg Polynomial.C a), hAm, add_smul, smul_neg]
      abel
    rw [h1, h2, det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Polynomial.coeff_C_mul,
      coeff_det_one_add_X_smul_one, trace_neg]
  rw [← hPA, derivative_coe, key, hPA, hB, hN, trace_geomMatrix_mul]
  ring

private lemma constantCoeff_det_one_sub_X_smul (M : Matrix n n K) :
    constantCoeff (det (1 - (PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C (R := K)))) = 1 := by
  rw [RingHom.map_det, ← det_one (R := K) (n := n)]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;> simp [one_apply, h]

/-- **Hartshorne, Appendix C, Lemma 4.1.** For an endomorphism `φ` of a
finite-dimensional vector space `V` over a field `K` of characteristic zero,
`exp (∑_{r ≥ 1} Tr (φ ^ r) t ^ r / r) = det (1 - t φ)⁻¹` as formal power series
in `t`.  The determinant is that of `1 - t φ` acting on `K⟦t⟧ ⊗[K] V`, and the
exponential is the formal exponential series substituted at the series with
zero constant term. -/
theorem traceExponential_eq_inv_det {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (φ : Module.End K V) :
    (PowerSeries.exp K).subst
        (PowerSeries.mk fun r : ℕ => if r = 0 then (0 : K) else LinearMap.trace K V (φ ^ r) / r) =
      (LinearMap.det ((1 : Module.End K⟦X⟧ (K⟦X⟧ ⊗[K] V)) -
        (PowerSeries.X : K⟦X⟧) • φ.baseChange K⟦X⟧))⁻¹ := by
  classical
  set b := Module.finBasis K V
  set M := LinearMap.toMatrix b b φ
  set f : K⟦X⟧ :=
    PowerSeries.mk fun r : ℕ => if r = 0 then (0 : K) else LinearMap.trace K V (φ ^ r) / r with hf
  have htr : ∀ r : ℕ, LinearMap.trace K V (φ ^ r) = trace (M ^ r) := by
    intro r
    rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.toMatrix_pow]
  have hdet : LinearMap.det ((1 : Module.End K⟦X⟧ (K⟦X⟧ ⊗[K] V)) -
        (PowerSeries.X : K⟦X⟧) • φ.baseChange K⟦X⟧) =
      det (1 - (PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C (R := K))) := by
    rw [← LinearMap.det_toMatrix (Algebra.TensorProduct.basis K⟦X⟧ b)]
    set bX := Algebra.TensorProduct.basis K⟦X⟧ b
    rw [map_sub (LinearMap.toMatrix bX bX), map_smul (LinearMap.toMatrix bX bX),
      LinearMap.toMatrix_one, LinearMap.toMatrix_baseChange]
    rfl
  rw [hdet]
  set D := det (1 - (PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C (R := K)))
  have hD0 : constantCoeff D = 1 := constantCoeff_det_one_sub_X_smul M
  have hDd : d⁄dX K D = -(PowerSeries.mk fun k => trace (M ^ (k + 1))) * D :=
    derivative_det_one_sub_X_smul M
  have hf0 : constantCoeff f = 0 := by simp [hf]
  have hsub : HasSubst f := HasSubst.of_constantCoeff_zero' hf0
  have hfd : d⁄dX K f = PowerSeries.mk fun k => trace (M ^ (k + 1)) := by
    ext k
    rw [coeff_derivative, hf, coeff_mk, coeff_mk, if_neg (Nat.succ_ne_zero k), htr]
    push_cast
    field_simp
  set E := (PowerSeries.exp K).subst f with hEdef
  have hE0 : constantCoeff E = 1 := by
    change MvPowerSeries.constantCoeff ((PowerSeries.exp K).subst f) = 1
    rw [PowerSeries.constantCoeff_subst hsub]
    have hf0' : MvPowerSeries.constantCoeff f = 0 := hf0
    simp only [map_pow, hf0']
    rw [finsum_eq_single _ 0 (fun d hd => by simp [hd])]
    simp
  have hEd : d⁄dX K E = E * d⁄dX K f := by
    rw [hEdef, derivative_subst hsub, derivative_exp]
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [hD0]; exact one_ne_zero)]
  apply derivative.ext
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hEd, hDd, hfd, derivative_one]
    ring
  · rw [map_mul, hE0, hD0, map_one, mul_one]

end

end Hartshorne
