/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Weil.ProjectiveLinePointCount
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The zeta function of the projective line

Hartshorne, *Algebraic Geometry*, Appendix C.1, projective-line calculation (p. 450): for
the projective line over `𝔽_q`,
`Z(ℙ¹, t) = 1 / ((1 - t) (1 - q t))`,
both as an identity of formal power series in `ℚ⟦t⟧` and as the statement that the zeta
series is the expansion at the origin of that rational function in `ℚ(t)`.

## Proof

Following the book: since `N_r(ℙ¹) = q^r + 1`, the logarithm series of `Z(ℙ¹, t)` is the
sum of the two series `∑_{r ≥ 1} a^r t^r / r = -log (1 - a t)` for `a = 1` and `a = q`.
Exponentiating, the exponential of a sum is the product of the exponentials, and the
exponential of `-log (1 - a t)` is `(1 - a t)⁻¹`.  Both exponential identities are proved
by comparing derivatives: the formal chain rule gives `(exp f)' = f' exp f`, so the
relevant products have derivative zero and constant coefficient one.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

noncomputable section

open PowerSeries

/-- The series `∑_{r ≥ 1} a^r t^r / r`, i.e. `-log (1 - a t)`. -/
private def negLogOneSub (a : ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun r => if r = 0 then 0 else a ^ r / r

private lemma constantCoeff_negLogOneSub (a : ℚ) : constantCoeff (negLogOneSub a) = 0 := by
  simp [negLogOneSub]

private lemma derivative_negLogOneSub (a : ℚ) :
    d⁄dX ℚ (negLogOneSub a) = PowerSeries.mk fun r => a ^ (r + 1) := by
  ext r
  rw [coeff_derivative, negLogOneSub, coeff_mk, coeff_mk, if_neg (Nat.succ_ne_zero r)]
  push_cast
  field_simp

/-- The geometric series identity `(∑_{r ≥ 0} a^{r+1} t^r) (1 - a t) = a`. -/
private lemma geom_mul_one_sub (a : ℚ) :
    (PowerSeries.mk fun r => a ^ (r + 1)) * (1 - C a * X) = C a := by
  ext n
  rw [mul_sub, mul_one, mul_comm (C a) X, ← mul_assoc, map_sub]
  rcases n with _ | n
  · simp
  · rw [coeff_mul_C, coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_C, if_neg (Nat.succ_ne_zero n)]
    ring

private lemma constantCoeff_exp_subst {f : ℚ⟦X⟧} (hf : constantCoeff f = 0) :
    constantCoeff ((exp ℚ).subst f) = 1 := by
  change MvPowerSeries.constantCoeff ((exp ℚ).subst f) = 1
  rw [PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero' hf)]
  have hf' : MvPowerSeries.constantCoeff f = 0 := hf
  simp only [map_pow, hf']
  rw [finsum_eq_single _ 0 (fun d hd => by simp [hd])]
  simp

private lemma derivative_exp_subst {f : ℚ⟦X⟧} (hf : constantCoeff f = 0) :
    d⁄dX ℚ ((exp ℚ).subst f) = (exp ℚ).subst f * d⁄dX ℚ f := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hf), derivative_exp]

/-- `exp (-log (1 - a t)) = (1 - a t)⁻¹`, in the form `exp (-log (1 - a t)) (1 - a t) = 1`. -/
private lemma exp_subst_negLogOneSub_mul (a : ℚ) :
    (exp ℚ).subst (negLogOneSub a) * (1 - C a * X) = 1 := by
  apply derivative.ext
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      derivative_exp_subst (constantCoeff_negLogOneSub a), derivative_negLogOneSub,
      derivative_one, map_sub, derivative_one, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      derivative_X, derivative_C]
    linear_combination ((exp ℚ).subst (negLogOneSub a)) * geom_mul_one_sub a
  · simp [constantCoeff_exp_subst (constantCoeff_negLogOneSub a)]

/-- `exp f exp (-f) = 1` for a series `f` with zero constant coefficient. -/
private lemma exp_subst_mul_exp_subst_neg {f : ℚ⟦X⟧} (hf : constantCoeff f = 0) :
    (exp ℚ).subst f * (exp ℚ).subst (-f) = 1 := by
  have hf' : constantCoeff (-f) = 0 := by simp [hf]
  apply derivative.ext
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_exp_subst hf,
      derivative_exp_subst hf', map_neg, derivative_one]
    ring
  · simp [constantCoeff_exp_subst hf, constantCoeff_exp_subst hf']

/-- The exponential of a sum is the product of the exponentials. -/
private lemma exp_subst_add {f g : ℚ⟦X⟧} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) :
    (exp ℚ).subst (f + g) = (exp ℚ).subst f * (exp ℚ).subst g := by
  have hfg : constantCoeff (f + g) = 0 := by simp [hf, hg]
  have hf' : constantCoeff (-f) = 0 := by simp [hf]
  have hg' : constantCoeff (-g) = 0 := by simp [hg]
  have key : (exp ℚ).subst (f + g) * (exp ℚ).subst (-f) * (exp ℚ).subst (-g) = 1 := by
    apply derivative.ext
    · rw [Derivation.leibniz, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, derivative_exp_subst hfg, derivative_exp_subst hf',
        derivative_exp_subst hg', map_add, map_neg, map_neg, derivative_one]
      ring
    · simp [constantCoeff_exp_subst hfg, constantCoeff_exp_subst hf',
        constantCoeff_exp_subst hg']
  linear_combination ((exp ℚ).subst f * (exp ℚ).subst g) * key -
    ((exp ℚ).subst (f + g) * (exp ℚ).subst g * (exp ℚ).subst (-g)) *
      exp_subst_mul_exp_subst_neg hf -
    (exp ℚ).subst (f + g) * exp_subst_mul_exp_subst_neg hg

/-- **Hartshorne, Appendix C.1, projective-line calculation (p. 450).** For the projective
line `ℙ¹` over a finite field `k` with `q = #k` elements,
`Z(ℙ¹, t) = 1 / ((1 - t) (1 - q t))`.

The first conjunct is the identity in the formal power series ring `ℚ⟦t⟧`, where
`Z(ℙ¹, t)` is `Hartshorne.hasseWeilZetaSeries`, the formal exponential of
`∑_{r ≥ 1} N_r t^r / r`.  The second says that this formal series is the expansion at the
origin of the displayed rational function: its image in the Laurent series field `ℚ⸨t⸩`
equals the image of `1 / ((1 - t) (1 - q t)) ∈ ℚ(t)`. -/
theorem hasseWeilZetaSeries_projectiveLine (k : Type u) [Field k] [Finite k] :
    hasseWeilZetaSeries k (projectiveSpaceOverScheme 1 (Spec (.of k)))
        (projectiveSpaceOverSchemeProjection 1 (Spec (.of k)))
        (projectiveSpaceOverSchemeProjection_finiteType 1 (Spec (.of k))) =
      ((1 - X) * (1 - C (Nat.card k : ℚ) * X))⁻¹ ∧
    ((hasseWeilZetaSeries k (projectiveSpaceOverScheme 1 (Spec (.of k)))
        (projectiveSpaceOverSchemeProjection 1 (Spec (.of k)))
        (projectiveSpaceOverSchemeProjection_finiteType 1 (Spec (.of k))) : ℚ⟦X⟧) :
          LaurentSeries ℚ) =
      ((1 / ((1 - RatFunc.X) * (1 - RatFunc.C (Nat.card k : ℚ) * RatFunc.X)) :
        RatFunc ℚ) : LaurentSeries ℚ) := by
  set q : ℚ := (Nat.card k : ℚ) with hq
  set Z := hasseWeilZetaSeries k (projectiveSpaceOverScheme 1 (Spec (.of k)))
    (projectiveSpaceOverSchemeProjection 1 (Spec (.of k)))
    (projectiveSpaceOverSchemeProjection_finiteType 1 (Spec (.of k))) with hZ
  -- The logarithm series is `-log (1 - t) - log (1 - q t)`.
  have hlog : hasseWeilZetaLogSeries k (projectiveSpaceOverScheme 1 (Spec (.of k)))
      (projectiveSpaceOverSchemeProjection 1 (Spec (.of k)))
      (projectiveSpaceOverSchemeProjection_finiteType 1 (Spec (.of k))) =
        negLogOneSub 1 + negLogOneSub q := by
    ext n
    rw [hasseWeilZetaLogSeries, map_add, negLogOneSub, negLogOneSub, coeff_mk, coeff_mk,
      coeff_mk]
    split_ifs with hn
    · simp
    · rw [pointCountSequence_projectiveLine k ⟨n, Nat.pos_of_ne_zero hn⟩]
      rw [hq]
      push_cast
      rw [PNat.mk_coe]
      ring
  have hmul : Z * ((1 - X) * (1 - C q * X)) = 1 := by
    rw [hZ, hasseWeilZetaSeries, hlog,
      exp_subst_add (constantCoeff_negLogOneSub 1) (constantCoeff_negLogOneSub q)]
    have h1 := exp_subst_negLogOneSub_mul 1
    have h2 := exp_subst_negLogOneSub_mul q
    rw [map_one, one_mul] at h1
    linear_combination ((exp ℚ).subst (negLogOneSub q) * (1 - C q * X)) * h1 + h2
  have hP0 : constantCoeff ((1 - X : ℚ⟦X⟧) * (1 - C q * X)) ≠ 0 := by simp
  refine ⟨(PowerSeries.eq_inv_iff_mul_eq_one hP0).mpr hmul, ?_⟩
  -- Pass to Laurent series.
  have hpoly : ((((1 - Polynomial.X) * (1 - Polynomial.C q * Polynomial.X) : Polynomial ℚ) :
      ℚ⟦X⟧) : LaurentSeries ℚ) =
        (((1 - Polynomial.X) * (1 - Polynomial.C q * Polynomial.X) : Polynomial ℚ) :
          RatFunc ℚ) :=
    RatFunc.coe_coe _
  have hPS : (((1 - Polynomial.X) * (1 - Polynomial.C q * Polynomial.X) : Polynomial ℚ) :
      ℚ⟦X⟧) = (1 - X) * (1 - C q * X) := by
    simp
  have hRF : (((1 - Polynomial.X) * (1 - Polynomial.C q * Polynomial.X) : Polynomial ℚ) :
      RatFunc ℚ) = (1 - RatFunc.X) * (1 - RatFunc.C q * RatFunc.X) := by
    simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [hPS, hRF] at hpoly
  have hmulL : ((Z : ℚ⟦X⟧) : LaurentSeries ℚ) *
      (((1 - X) * (1 - C q * X) : ℚ⟦X⟧) : LaurentSeries ℚ) = 1 := by
    rw [← PowerSeries.coe_mul, hmul, PowerSeries.coe_one]
  rw [hpoly] at hmulL
  rw [one_div, map_inv₀]
  exact eq_inv_of_mul_eq_one_left hmulL

end

end Hartshorne
