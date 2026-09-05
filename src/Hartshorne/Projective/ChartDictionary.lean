/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Homogenize
import Hartshorne.Projective.Dehomogenize
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The dehomogenisation dictionary

Hartshorne, *Algebraic Geometry*, I.2, the pair `α`, `β` of Proposition 2.2
(pp. 10-11).

Proposition 2.2 uses `α` and `β` to move *closed sets* between `Uᵢ` and `𝔸ⁿ`.
This file records what they do to *polynomials*, which is what Theorem 3.4 needs:
`α` is a bijection from the homogeneous polynomials, up to powers of `xᵢ`, onto
all polynomials in the affine coordinates.

Both halves are here.

`α(β(g)) = g` on the nose: `β` pads each monomial with a power of `xᵢ` and `α`
sets `xᵢ = 1`, which puts the padding back to nothing.

`α` is injective on homogeneous polynomials, which is the half with content. It
is proved by evaluation rather than by comparing supports. If `α(g) = 0` then
`g` vanishes at every vector with `i`-th coordinate `1`, hence by homogeneity at
every vector with `i`-th coordinate nonzero; so `xᵢ · g` vanishes identically
and, over an infinite field, is the zero polynomial. The polynomial ring is a
domain, so `g = 0`.

## Main results

* `Hartshorne.dehomogenize_homogenize`
* `Hartshorne.eq_zero_of_dehomogenize_eq_zero`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- **`α ∘ β = id`.** Homogenising pads each monomial with a power of `xᵢ`, and
dehomogenising sets `xᵢ` to `1`, undoing exactly that. -/
@[simp]
theorem dehomogenize_homogenize (i : σ) (g : MvPolynomial {j : σ // j ≠ i} k) :
    dehomogenize i (homogenize i g) = g := by
  rw [homogenize, map_sum]
  conv_rhs => rw [g.as_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_mul, map_mul, map_pow, dehomogenize_X_self, one_pow, mul_one, map_prod,
    monomial_eq]
  congr 1
  · simp [dehomogenize]
  · exact Finset.prod_congr rfl fun j _ => by
      rw [map_pow, dehomogenize_X_of_ne j.2]

/-- The vector with `1` in slot `i` built from the ratios `v_j/v_i` is `v`
rescaled. -/
theorem chartInvVec_div (i : σ) {v : σ → k} (hv : v i ≠ 0) :
    chartInvVec i (fun j : {j : σ // j ≠ i} => v j / v i) = (v i)⁻¹ • v := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · rw [chartInvVec_self]
    simp [inv_mul_cancel₀ hv]
  · rw [chartInvVec_of_ne _ hj]
    simp [div_eq_inv_mul]

/-- **`α` is injective on homogeneous polynomials.**

A homogeneous `g` killed by `α` vanishes wherever `xᵢ` does not, so `xᵢ · g`
vanishes everywhere and is zero; the polynomial ring is a domain. Homogeneity is
what turns "vanishes on the slice `vᵢ = 1`" into "vanishes wherever `vᵢ ≠ 0`",
and it is essential: `xᵢ - 1` is killed by `α` and is not zero. -/
theorem eq_zero_of_dehomogenize_eq_zero [Infinite k] {i : σ} {n : ℕ}
    {g : MvPolynomial σ k} (hg : g.IsHomogeneous n) (h : dehomogenize i g = 0) :
    g = 0 := by
  have hXg : (X i * g : MvPolynomial σ k) = 0 := by
    refine MvPolynomial.funext fun v => ?_
    rcases eq_or_ne (v i) 0 with hv | hv
    · simp [hv]
    · have h0 : eval (chartInvVec i fun j : {j : σ // j ≠ i} => v j / v i) g = 0 := by
        rw [← eval_dehomogenize, h, map_zero]
      rw [chartInvVec_div i hv, hg.eval_smul] at h0
      have hgv : eval v g = 0 := by
        rcases mul_eq_zero.1 h0 with hc | hc
        · exact absurd hc (pow_ne_zero n (inv_ne_zero hv))
        · exact hc
      simp [hgv]
  rcases mul_eq_zero.1 hXg with hc | hc
  · exact absurd hc (X_ne_zero i)
  · exact hc

end Hartshorne
