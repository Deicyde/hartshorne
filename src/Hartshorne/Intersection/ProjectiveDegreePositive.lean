/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NumericalBinomial
import Hartshorne.Intersection.ProjectiveHilbertPolynomial

/-!
# Positivity and integrality of projective degree

Hartshorne, *Algebraic Geometry*, Proposition I.7.6(a) (p. 52).

The binomial-basis expansion of the numerical Hilbert polynomial identifies
its factorial-scaled leading coefficient with an integer.  Hilbert--Serre's
positivity theorem then shows that integer is positive for a nonempty
projective algebraic set.
-/

namespace Hartshorne

open Polynomial Set
open scoped Polynomial

noncomputable section

universe u

/-- The projective Hilbert polynomial is a numerical polynomial. -/
theorem projectiveHilbertPolynomial_isNumericalPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) :
    IsNumericalPolynomial (projectiveHilbertPolynomial Y) :=
  (projectiveHilbertPolynomial_isHilbertPolynomial Y).1

/-- The projective Hilbert polynomial of a nonempty projective algebraic set
has positive leading coefficient. -/
theorem projectiveHilbertPolynomial_leadingCoeff_pos
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {Y : Set (ProjectiveSpace k (Fin (n + 1)))}
    (hY : IsProjAlgebraicSet Y) (hne : Y.Nonempty) :
    0 < (projectiveHilbertPolynomial Y).leadingCoeff := by
  unfold projectiveHilbertPolynomial
  apply gradedHilbertPolynomial_leadingCoeff_pos
  rw [projZeroSet_annihilator_homogeneousCoordinateRing hY]
  exact hne

/-- Projective degree is always an integer: it is the top integral coefficient
in the binomial-basis expansion of the projective Hilbert polynomial. -/
theorem projectiveDegree_eq_intCast
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) :
    ∃ d : ℤ, projectiveDegree Y = (d : ℚ) := by
  obtain ⟨c, _, _, htop⟩ :=
    (isNumericalPolynomial_iff_exists_binomialExpansion
      (projectiveHilbertPolynomial Y)).mp
      (projectiveHilbertPolynomial_isNumericalPolynomial Y)
  exact ⟨c (projectiveHilbertPolynomial Y).natDegree, htop⟩

/-- A nonempty projective algebraic set has strictly positive projective
degree. -/
theorem projectiveDegree_pos
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {Y : Set (ProjectiveSpace k (Fin (n + 1)))}
    (hY : IsProjAlgebraicSet Y) (hne : Y.Nonempty) :
    0 < projectiveDegree Y := by
  rw [projectiveDegree]
  exact mul_pos (by positivity)
    (projectiveHilbertPolynomial_leadingCoeff_pos hY hne)

/-- **Hartshorne I.7.6(a).** The degree of a nonempty projective algebraic
set is the cast of a strictly positive natural number. -/
theorem projectiveDegree_eq_natCast_of_nonempty
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {Y : Set (ProjectiveSpace k (Fin (n + 1)))}
    (hY : IsProjAlgebraicSet Y) (hne : Y.Nonempty) :
    ∃ d : ℕ, 0 < d ∧ projectiveDegree Y = (d : ℚ) := by
  let P := projectiveHilbertPolynomial Y
  obtain ⟨c, _, _, htop⟩ :=
    (isNumericalPolynomial_iff_exists_binomialExpansion P).mp
      (projectiveHilbertPolynomial_isNumericalPolynomial Y)
  have hdeg : 0 < projectiveDegree Y := projectiveDegree_pos hY hne
  have hcq : (0 : ℚ) < (c P.natDegree : ℚ) := by
    rw [← htop]
    exact hdeg
  have hc : 0 < c P.natDegree := by exact_mod_cast hcq
  refine ⟨(c P.natDegree).toNat, Int.pos_iff_toNat_pos.mp hc, ?_⟩
  change (P.natDegree.factorial : ℚ) * P.leadingCoeff =
    ((c P.natDegree).toNat : ℚ)
  rw [htop]
  exact_mod_cast (Int.toNat_of_nonneg hc.le).symm

end

end Hartshorne
