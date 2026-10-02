/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NumericalBinomial
import Hartshorne.Intersection.ProjectiveHilbertPolynomial
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# The Hilbert polynomial and degree of projective space

Hartshorne, *Algebraic Geometry*, Proposition I.7.6(c) (p. 52).

The degree-`l` monomials in `k[x₀, ..., xₙ]` are indexed by the weak
compositions of `l` into `n + 1` parts, so their number is `choose (l + n) n`.
Consequently the Hilbert polynomial of projective `n`-space is the translated
binomial polynomial `z ↦ choose (z + n) n`, whose leading coefficient is
`1 / n!`; hence projective space has degree one.
-/

namespace Hartshorne

open Filter MvPolynomial Polynomial Set
open scoped Polynomial

noncomputable section

universe u

private theorem finrank_homogeneousSubmodule
    {k : Type u} [Field k] (n l : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k l) =
      (l + n).choose n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank k
      (MvPolynomial.restrictSupport k
        {d : Fin (n + 1) →₀ ℕ | d.degree = l}) = _
  rw [Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport k
      {d : Fin (n + 1) →₀ ℕ | d.degree = l})]
  change Nat.card {d : Fin (n + 1) →₀ ℕ // d.degree = l} = _
  calc
    Nat.card {d : Fin (n + 1) →₀ ℕ // d.degree = l} =
        Nat.card (Sym (Fin (n + 1)) l) :=
      Nat.card_congr (Sym.equivNatSum (Fin (n + 1)) l).symm
    _ = Fintype.card (Sym (Fin (n + 1)) l) := Nat.card_eq_fintype_card
    _ = ((n + 1) + l - 1).choose l := by
      simpa using Sym.card_sym_eq_choose (α := Fin (n + 1)) l
    _ = (l + n).choose n := by
      have h : (n + 1) + l - 1 = l + n := by omega
      rw [h]
      exact Nat.choose_symm_add

private theorem hilbertFunction_projectiveSpace
    {k : Type u} [Field k] [IsAlgClosed k] (n l : ℕ) :
    hilbertFunction (k := k) (σ := Fin (n + 1))
        (integerProjCoordGrading
          (Set.univ : Set (ProjectiveSpace k (Fin (n + 1))))) (l : ℤ) =
      (l + n).choose n := by
  rw [hilbertFunction, integerProjCoordGrading_ofNat]
  let e : homogeneousCoordinateRing
        (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) ≃ₐ[k]
      MvPolynomial (Fin (n + 1)) k :=
    (Ideal.quotientEquivAlgOfEq k homogeneousVanishingIdeal_univ).trans
      (AlgEquiv.quotientBot k (MvPolynomial (Fin (n + 1)) k))
  have hmap :
      (projCoordGrading
        (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) l).map
          e.toLinearEquiv.toLinearMap =
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k l := by
    ext f
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      simpa [e] using hp
    · intro hf
      refine ⟨Ideal.Quotient.mk _ f, ⟨f, hf, rfl⟩, ?_⟩
      simp [e]
  calc
    Module.finrank k
        (projCoordGrading
          (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) l) =
        Module.finrank k
          ((projCoordGrading
            (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) l).map
              e.toLinearEquiv.toLinearMap) :=
      (e.toLinearEquiv.finrank_map_eq _).symm
    _ = Module.finrank k
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k l) := by rw [hmap]
    _ = (l + n).choose n := finrank_homogeneousSubmodule n l

private theorem translatedNumericalBinomial_isHilbertPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) :
    IsHilbertPolynomial (σ := Fin (n + 1))
      (integerProjCoordGrading
        (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))))
      ((numericalBinomial n).taylor (n : ℚ)) := by
  constructor
  · rw [IsNumericalPolynomial, Filter.eventually_atTop]
    refine ⟨0, fun d hd => ?_⟩
    refine ⟨Ring.choose (d + n) n, ?_⟩
    rw [Polynomial.taylor_eval]
    simpa only [Int.cast_add, Int.cast_natCast] using
      numericalBinomial_eval_intCast n (d + n)
  · rw [Filter.eventually_atTop]
    refine ⟨0, fun d hd => ?_⟩
    obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [Polynomial.taylor_eval, hilbertFunction_projectiveSpace]
    have h := numericalBinomial_eval_natCast n (l + n)
    norm_num at h ⊢
    exact h

/-- **Hartshorne I.7.6(c).** The Hilbert function of projective `n`-space in
nonnegative degree `l` is `choose (l + n) n`; its Hilbert polynomial is the
corresponding translated numerical binomial polynomial; and its projective
degree is one. -/
theorem projectiveSpace_hilbertPolynomial_and_degree
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) :
    (∀ l : ℕ,
      hilbertFunction (k := k) (σ := Fin (n + 1))
          (integerProjCoordGrading
            (Set.univ : Set (ProjectiveSpace k (Fin (n + 1))))) (l : ℤ) =
        (l + n).choose n) ∧
      projectiveHilbertPolynomial
          (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) =
        (numericalBinomial n).taylor (n : ℚ) ∧
      projectiveDegree
          (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) = 1 := by
  have hfunction := hilbertFunction_projectiveSpace (k := k) n
  have hpolynomial :
      projectiveHilbertPolynomial
          (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) =
        (numericalBinomial n).taylor (n : ℚ) :=
    isHilbertPolynomial_unique
      (integerProjCoordGrading
        (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))))
      (projectiveHilbertPolynomial_isHilbertPolynomial
        (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))))
      (translatedNumericalBinomial_isHilbertPolynomial (k := k) n)
  refine ⟨hfunction, hpolynomial, ?_⟩
  rw [projectiveDegree, hpolynomial, Polynomial.natDegree_taylor,
    numericalBinomial_natDegree, Polynomial.leadingCoeff_taylor,
    numericalBinomial_leadingCoeff]
  exact mul_inv_cancel₀ (by positivity)

end

end Hartshorne
