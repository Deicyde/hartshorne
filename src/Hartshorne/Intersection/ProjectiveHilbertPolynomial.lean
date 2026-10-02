/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.HilbertSerre
import Hartshorne.Projective.CoordAwayChart
import Hartshorne.Projective.Correspondence

/-!
# Hilbert polynomials and degrees of projective algebraic sets

Hartshorne, *Algebraic Geometry*, definitions after Theorem I.7.5 (p. 52).

For a projective algebraic set `Y`, its Hilbert polynomial is the Hilbert
polynomial of the homogeneous coordinate ring `S(Y) = S / J(Y)`.  If this
polynomial has degree `r`, the degree of `Y` is `r!` times its leading
coefficient.
-/

namespace Hartshorne

open MvPolynomial Polynomial Set
open scoped Polynomial

noncomputable section

universe u

/-- The homogeneous vanishing ideal, bundled for the integer polynomial
grading. -/
noncomputable abbrev integerProjVanishingIdeal
    {k : Type u} [Field k] {σ : Type*}
    (Y : Set (ProjectiveSpace k σ)) :
    HomogeneousIdeal (integerHomogeneousSubmodule k σ) :=
  ⟨homogeneousVanishingIdeal Y,
    (ideal_isHomogeneous_integer_iff k σ
      (homogeneousVanishingIdeal Y)).2
      (isHomogeneousIdeal_homogeneousVanishingIdeal Y)⟩

/-- The integer grading on the homogeneous coordinate ring of a projective
set.  It extends the existing natural-number grading by zero in negative
degrees. -/
noncomputable abbrev integerProjCoordGrading
    {k : Type u} [Field k] {σ : Type*}
    (Y : Set (ProjectiveSpace k σ)) :
    ℤ → Submodule k (homogeneousCoordinateRing Y) :=
  quotGrading (integerHomogeneousSubmodule k σ)
    (integerProjVanishingIdeal Y)

noncomputable instance integerProjCoordGradingDecomposition
    {k : Type u} [Field k] {σ : Type*}
    (Y : Set (ProjectiveSpace k σ)) :
    DirectSum.Decomposition (integerProjCoordGrading Y) :=
  instDecompositionQuotientIdealToIdealSubmoduleQuotGrading
    (integerHomogeneousSubmodule k σ) (integerProjVanishingIdeal Y)

/-- The ambient polynomial-ring action respects the integer grading on its
homogeneous coordinate-ring quotient. -/
instance integerProjCoordGradingGradedSMul
    {k : Type u} [Field k] {σ : Type*}
    (Y : Set (ProjectiveSpace k σ)) :
    SetLike.GradedSMul (integerHomogeneousSubmodule k σ)
      (integerProjCoordGrading Y) where
  smul_mem {i j a q} ha hq := by
    obtain ⟨b, hb, rfl⟩ := hq
    refine ⟨a * b, SetLike.mul_mem_graded ha hb, ?_⟩
    change Ideal.Quotient.mk (integerProjVanishingIdeal Y).toIdeal (a * b) =
      a • Ideal.Quotient.mk (integerProjVanishingIdeal Y).toIdeal b
    exact Submodule.Quotient.mk_smul
      (integerProjVanishingIdeal Y).toIdeal a b

/-- In nonnegative degree the integer grading on `S(Y)` is the existing
natural-number grading. -/
@[simp]
theorem integerProjCoordGrading_ofNat
    {k : Type u} [Field k] {σ : Type*}
    (Y : Set (ProjectiveSpace k σ)) (d : ℕ) :
    integerProjCoordGrading Y (d : ℤ) = projCoordGrading Y d := by
  rfl

/-- The annihilator of the homogeneous coordinate ring, as a module over the
ambient polynomial ring, is its defining homogeneous vanishing ideal. -/
theorem annihilator_homogeneousCoordinateRing
    {k : Type u} [Field k] {σ : Type*}
    (Y : Set (ProjectiveSpace k σ)) :
    Module.annihilator (MvPolynomial σ k) (homogeneousCoordinateRing Y) =
      homogeneousVanishingIdeal Y := by
  exact Ideal.annihilator_quotient

/-- The projective support of the homogeneous coordinate ring of an
algebraic set is the set itself. -/
theorem projZeroSet_annihilator_homogeneousCoordinateRing
    {k : Type u} [Field k] {σ : Type*}
    {Y : Set (ProjectiveSpace k σ)} (hY : IsProjAlgebraicSet Y) :
    projZeroSet
        (Module.annihilator (MvPolynomial σ k)
          (homogeneousCoordinateRing Y) : Set (MvPolynomial σ k)) = Y := by
  rw [annihilator_homogeneousCoordinateRing]
  exact hY.projZeroSet_homogeneousVanishingIdeal_eq

/-- The Hilbert polynomial of a projective set `Y`: the canonical Hilbert
polynomial of its homogeneous coordinate ring `S(Y)`. -/
noncomputable def projectiveHilbertPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) : ℚ[X] :=
  gradedHilbertPolynomial
    (k := k) (n := n) (M := homogeneousCoordinateRing Y)
    (integerProjCoordGrading Y)

/-- The canonical projective Hilbert polynomial eventually computes the
Hilbert function of the homogeneous coordinate ring. -/
theorem projectiveHilbertPolynomial_isHilbertPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) :
    IsHilbertPolynomial (σ := Fin (n + 1))
      (integerProjCoordGrading Y) (projectiveHilbertPolynomial Y) :=
  gradedHilbertPolynomial_isHilbertPolynomial
    (k := k) (n := n) (M := homogeneousCoordinateRing Y)
    (integerProjCoordGrading Y)

/-- For an algebraic set, the degree of its projective Hilbert polynomial is
its projective dimension (with the empty set represented by `⊥`). -/
theorem projectiveHilbertPolynomial_degree
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {Y : Set (ProjectiveSpace k (Fin (n + 1)))}
    (hY : IsProjAlgebraicSet Y) :
    hilbertPolynomialDegree (projectiveHilbertPolynomial Y) = projDim Y := by
  rw [projectiveHilbertPolynomial, gradedHilbertPolynomial_degree,
    projZeroSet_annihilator_homogeneousCoordinateRing hY]

/-- The degree of a projective set is `r!` times the leading coefficient of
its Hilbert polynomial, where `r` is the polynomial's natural degree. -/
noncomputable def projectiveDegree
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) : ℚ :=
  (projectiveHilbertPolynomial Y).natDegree.factorial *
    (projectiveHilbertPolynomial Y).leadingCoeff

end

end Hartshorne
