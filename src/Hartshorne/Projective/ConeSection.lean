/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.DehomogenizeKernel
import Hartshorne.Projective.CoordAwayChart

/-!
# `S(Y)/(xᵢ − 1) ≅ A(Yᵢ)`

Toward Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.6 (pp. 11-12).

The chart `Yᵢ` is a hyperplane section of the affine cone over `Y`: cutting
`S(Y)` by the single element `xᵢ − 1` gives exactly `A(Yᵢ)`.

Hartshorne's hint runs through `S(Y)_{xᵢ} ≅ A(Yᵢ)[xᵢ, xᵢ⁻¹]`, which is the same
statement read on the localisation. The quotient form is what the dimension
formula wants, and it is shorter: dehomogenisation is surjective, and its kernel
is `(xᵢ − 1)` on the nose.

Two inputs, one from each side. Upstairs, the kernel of `α` on the polynomial
ring is `(xᵢ − 1)`. Downstairs, the ideal dictionary says `α(g) ∈ I(Yᵢ)` exactly
when `xᵢ · g ∈ J(Y)`, and that is what turns a polynomial killed modulo `I(Yᵢ)`
into one killed modulo `J(Y)` after subtracting a multiple of `xᵢ − 1`.

## Main results

* `Hartshorne.surjective_coordChartHom`
* `Hartshorne.ker_coordChartHom`
* `Hartshorne.coordChartQuotEquiv`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- `α` is onto `A(Yᵢ)`: every polynomial in the chart variables is the
dehomogenisation of its own homogenisation. -/
theorem surjective_coordChartHom (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    Function.Surjective (coordChartHom i Y) := by
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨Ideal.Quotient.mk _ (homogenize i p), by
    rw [coordChartHom_mk, dehomogenize_homogenize]⟩

/-- **The kernel of `S(Y) → A(Yᵢ)` is `(xᵢ − 1)`.**

Given `g` with `α(g) ∈ I(Yᵢ)`, put `f = α(g)` and rehomogenise it. The
dictionary makes `xᵢ · β(f)` a member of `J(Y)`, and `g` differs from it by
something `α` kills, hence by a multiple of `xᵢ − 1`. -/
theorem ker_coordChartHom (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    RingHom.ker (coordChartHom i Y)
      = Ideal.span {Ideal.Quotient.mk (homogeneousVanishingIdeal Y)
          (X i - 1 : MvPolynomial σ k)} := by
  refine le_antisymm (fun a ha => ?_) ?_
  · obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [RingHom.mem_ker, coordChartHom_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    set f : MvPolynomial {j : σ // j ≠ i} k := dehomogenize i g with hf
    have hH : X i * homogenize i f ∈ homogeneousVanishingIdeal Y :=
      (dehomogenize_mem_vanishingIdeal_iff (homogenize_isHomogeneous i f) Y).1
        (by rw [dehomogenize_homogenize]; exact ha)
    have hker : g - X i * homogenize i f
        ∈ RingHom.ker (dehomogenize (k := k) i).toRingHom := by
      rw [RingHom.mem_ker]
      show dehomogenize i (g - X i * homogenize i f) = 0
      rw [map_sub, map_mul, dehomogenize_X_self, dehomogenize_homogenize, one_mul, ← hf,
        sub_self]
    rw [ker_dehomogenize, Ideal.mem_span_singleton] at hker
    obtain ⟨q, hq⟩ := hker
    have hg : g = X i * homogenize i f + (X i - 1) * q := by rw [← hq]; ring
    rw [hg, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hH, zero_add, map_mul]
    exact Ideal.mem_span_singleton.2 ⟨_, rfl⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      coordChartHom_mk, map_sub, dehomogenize_X_self, map_one, sub_self, map_zero]

/-- **`S(Y)/(xᵢ − 1) ≅ A(Yᵢ)`.** -/
noncomputable def coordChartQuotEquiv (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    (homogeneousCoordinateRing Y ⧸ Ideal.span
        {Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i - 1 : MvPolynomial σ k)})
      ≃+* coordinateRing (chartMap i '' (Y ∩ standardChart i)) :=
  (Ideal.quotEquivOfEq (ker_coordChartHom i Y).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_coordChartHom i Y))

end Hartshorne
