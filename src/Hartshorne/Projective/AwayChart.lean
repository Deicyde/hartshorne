/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ChartDictionary
import Hartshorne.Projective.HomogeneousIdeal
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The graded localisation at `xᵢ` is a polynomial ring

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(b) and (c).

`S_(xᵢ) ≅ k[y₁,…,yₙ]`, where the left side is the degree-zero part of `S`
localised at `xᵢ` and the right side is the coordinate ring of the standard
chart.

This is the ring-theoretic shadow of Proposition 2.2 and the ambient case of the
isomorphism `A(Yᵢ) ≅ S(Y)_(xᵢ)` that Theorem 3.4 runs on. It is stated for the
whole polynomial ring; cutting down by a variety comes later.

The map is dehomogenisation. Since `α` sends `xᵢ` to `1`, a unit, it factors
through the localisation at `xᵢ` before any grading is mentioned, and the
degree-zero part is then carried along. Surjectivity and injectivity are the two
halves of the polynomial dictionary: `α(β(p)) = p`, and `α` kills no nonzero
homogeneous polynomial.

## Main definitions

* `Hartshorne.awayDehomogenize`, `Hartshorne.awayChartEquiv`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- Dehomogenising inverts `xᵢ`, so it factors through the localisation. -/
noncomputable def awayDehomogenize (i : σ) :
    Localization.Away (X i : MvPolynomial σ k) →+* MvPolynomial {j : σ // j ≠ i} k :=
  IsLocalization.lift (M := Submonoid.powers (X i : MvPolynomial σ k))
    (g := (dehomogenize i).toRingHom) (by
      rintro ⟨y, n, rfl⟩
      simp)

@[simp]
theorem awayDehomogenize_mk (i : σ) (a : MvPolynomial σ k) (n : ℕ)
    (h : (X i : MvPolynomial σ k) ^ n ∈ Submonoid.powers (X i : MvPolynomial σ k)) :
    awayDehomogenize i (Localization.mk a ⟨_, h⟩) = dehomogenize i a := by
  rw [Localization.mk_eq_mk', awayDehomogenize, IsLocalization.lift_mk'_spec]
  simp

omit [DecidableEq σ] in
/-- `xᵢ` is homogeneous of degree one, which is what makes it a legitimate
denominator for the graded localisation. -/
theorem X_mem_homogeneousSubmodule (i : σ) :
    (X i : MvPolynomial σ k) ∈ homogeneousSubmodule σ k 1 :=
  (mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X k i)

/-- The map `S_(xᵢ) → k[y]`: dehomogenise a representative. -/
noncomputable def awayToPoly (i : σ) :
    HomogeneousLocalization.Away (homogeneousSubmodule σ k) (X i) →+*
      MvPolynomial {j : σ // j ≠ i} k where
  toFun z := awayDehomogenize i z.val
  map_one' := by simp [HomogeneousLocalization.val_one]
  map_mul' a b := by simp [HomogeneousLocalization.val_mul]
  map_zero' := by simp [HomogeneousLocalization.val_zero]
  map_add' a b := by simp [HomogeneousLocalization.val_add]

@[simp]
theorem awayToPoly_mk (i : σ) (n : ℕ) (a : MvPolynomial σ k)
    (ha : a ∈ homogeneousSubmodule σ k (n • 1)) :
    awayToPoly i (HomogeneousLocalization.Away.mk (homogeneousSubmodule σ k)
      (X_mem_homogeneousSubmodule i) n a ha) = dehomogenize i a := by
  show awayDehomogenize i _ = _
  rw [HomogeneousLocalization.Away.val_mk, awayDehomogenize_mk]

/-- **`S_(xᵢ) ≅ k[y]`.**

Surjective because `α(β(p)) = p`, injective because `α` kills no nonzero
homogeneous polynomial. -/
noncomputable def awayChartEquiv [Infinite k] (i : σ) :
    HomogeneousLocalization.Away (homogeneousSubmodule σ k) (X i) ≃+*
      MvPolynomial {j : σ // j ≠ i} k :=
  RingEquiv.ofBijective (awayToPoly i) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨n, a, ha, rfl⟩ :=
        HomogeneousLocalization.Away.mk_surjective _ (X_mem_homogeneousSubmodule i) z
      rw [awayToPoly_mk] at hz
      have hzero : a = 0 :=
        eq_zero_of_dehomogenize_eq_zero
          ((mem_homogeneousSubmodule _ _).1 (by simpa using ha)) hz
      subst hzero
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
        Localization.mk_zero]
    · intro p
      refine ⟨HomogeneousLocalization.Away.mk (homogeneousSubmodule σ k)
        (X_mem_homogeneousSubmodule i) p.totalDegree (homogenize i p) ?_, ?_⟩
      · simpa using (mem_homogeneousSubmodule _ _).2 (homogenize_isHomogeneous i p)
      · rw [awayToPoly_mk, dehomogenize_homogenize])

end Hartshorne
