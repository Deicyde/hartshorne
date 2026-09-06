/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ConeSection
import Hartshorne.Projective.PointIdeal
import Hartshorne.Affine.DimensionCoordinateRing
import Hartshorne.Dimension.DimFormula
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# `dim S(Y) = dim Yᵢ + 1`

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.6 (pp. 11-12), the algebraic
half.

`xᵢ − 1` cuts `S(Y)` down to `A(Yᵢ)`, and it cuts the dimension down by exactly
one.

The height is one for the two standard reasons: at least one because `xᵢ − 1` is
a nonzero element of a domain, at most one by Krull's principal ideal theorem.
Theorem 1.8A(b) then converts the height into the dimension drop.

That `xᵢ − 1` is nonzero in `S(Y)` is where the grading is used, and it is the
only place: `xᵢ` is homogeneous of degree one and `1` of degree zero, so they can
agree only in the zero ring.

The remaining half of Exercise 2.6, that `dim Y = dim Yᵢ`, is topological and
lives with the projective dimension statement.

## Main results

* `Hartshorne.mk_X_sub_one_ne_zero`
* `Hartshorne.height_chartSectionIdeal`
* `Hartshorne.ringKrullDim_homogeneousCoordinateRing`
-/

namespace Hartshorne

open MvPolynomial

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {σ : Type} [Finite σ] [DecidableEq σ]
  {Y : Set (ProjectiveSpace k σ)}

/-- `S(Y)` is a finitely generated `k`-algebra, being a quotient of a polynomial
ring in finitely many variables. -/
instance finiteType_homogeneousCoordinateRing (Y : Set (ProjectiveSpace k σ)) :
    Algebra.FiniteType k (homogeneousCoordinateRing Y) :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ k (homogeneousVanishingIdeal Y)) Ideal.Quotient.mk_surjective

/-- The ideal `(xᵢ − 1)` of `S(Y)`, whose quotient is `A(Yᵢ)`. -/
noncomputable def chartSectionIdeal (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    Ideal (homogeneousCoordinateRing Y) :=
  Ideal.span {Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i - 1 : MvPolynomial σ k)}

/-- **`xᵢ − 1` is nonzero in `S(Y)`.**

`xᵢ` is homogeneous of degree one and `1` of degree zero, so if they agreed then
the degree-zero component of `1` would be both `1` and `0`. -/
theorem mk_X_sub_one_ne_zero (i : σ) (hY : IsProjVariety Y) :
    Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i - 1 : MvPolynomial σ k) ≠ 0 := by
  have := isDomain_homogeneousCoordinateRing hY
  intro h
  rw [map_sub, map_one, sub_eq_zero] at h
  have hzero : (DirectSum.decompose (projCoordGrading Y)
      (1 : homogeneousCoordinateRing Y) 0 : homogeneousCoordinateRing Y) = 0 := by
    rw [← h]
    exact DirectSum.decompose_of_mem_ne _ (mk_X_mem_projCoordGrading i Y) one_ne_zero
  rw [DirectSum.decompose_of_mem_same _ SetLike.GradedOne.one_mem] at hzero
  exact one_ne_zero hzero

/-- `(xᵢ − 1)` is prime, its quotient `A(Yᵢ)` being a domain. -/
theorem isPrime_chartSectionIdeal (i : σ) (hY : IsProjVariety Y)
    (hne : (Y ∩ standardChart i).Nonempty) : (chartSectionIdeal i Y).IsPrime := by
  have : IsDomain (coordinateRing (chartMap i '' (Y ∩ standardChart i))) :=
    isDomain_coordinateRing (isAffineVariety_chartMap_image i hY hne)
  have : IsDomain (homogeneousCoordinateRing Y ⧸ chartSectionIdeal i Y) :=
    (coordChartQuotEquiv i Y).isDomain _
  exact Ideal.Quotient.isDomain_iff_prime _ |>.1 ‹_›

/-- **`(xᵢ − 1)` has height one.**

At least one because `S(Y)` is a domain and `xᵢ − 1` is not zero; at most one by
Krull's principal ideal theorem, `S(Y)` being Noetherian. -/
theorem height_chartSectionIdeal (i : σ) (hY : IsProjVariety Y)
    (hne : (Y ∩ standardChart i).Nonempty) : (chartSectionIdeal i Y).height = 1 := by
  have := isDomain_homogeneousCoordinateRing hY
  have hp := isPrime_chartSectionIdeal i hY hne
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (mk_X_sub_one_ne_zero i hY))
    fun hunit => hp.ne_top (Ideal.span_singleton_eq_top.2 hunit)

/-- **Exercise 2.6, algebraic half**: `dim S(Y) = dim Yᵢ + 1`. -/
theorem ringKrullDim_homogeneousCoordinateRing (i : σ) (hY : IsProjVariety Y)
    (hne : (Y ∩ standardChart i).Nonempty) :
    ringKrullDim (homogeneousCoordinateRing Y)
      = dim (chartMap i '' (Y ∩ standardChart i)) + 1 := by
  have := isDomain_homogeneousCoordinateRing hY
  have := isPrime_chartSectionIdeal i hY hne
  have hA : IsAffineVariety (chartMap i '' (Y ∩ standardChart i)) :=
    isAffineVariety_chartMap_image i hY hne
  have hform := height_add_ringKrullDim_quotient_eq k (homogeneousCoordinateRing Y)
    (chartSectionIdeal i Y) 1 (height_chartSectionIdeal i hY hne)
  rw [ringKrullDim_eq_of_ringEquiv (coordChartQuotEquiv i Y),
    ← dim_eq_ringKrullDim_coordinateRing hA.isAlgebraicSet] at hform
  rw [← hform, Nat.cast_one, add_comm]

end Hartshorne
