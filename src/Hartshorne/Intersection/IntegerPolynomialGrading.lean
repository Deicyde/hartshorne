/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.HomogeneousIdeal

/-!
# The integer grading on a polynomial ring

Hartshorne, *Algebraic Geometry*, I.7, graded-ring conventions before
Proposition 7.4 (p. 50).
-/

namespace Hartshorne

open DirectSum MvPolynomial

variable (k : Type*) [CommRing k] (σ : Type*)

/-- The total-degree grading on a polynomial ring, extended from `ℕ` to `ℤ`
by making every negative-degree piece zero. -/
noncomputable def integerHomogeneousSubmodule : ℤ → Submodule k (MvPolynomial σ k)
  | .ofNat n => MvPolynomial.homogeneousSubmodule σ k n
  | .negSucc _ => ⊥

@[simp]
theorem integerHomogeneousSubmodule_ofNat (n : ℕ) :
    integerHomogeneousSubmodule k σ (n : ℤ) =
      MvPolynomial.homogeneousSubmodule σ k n := rfl

@[simp]
theorem integerHomogeneousSubmodule_negSucc (n : ℕ) :
    integerHomogeneousSubmodule k σ (.negSucc n) = ⊥ := rfl

theorem integerHomogeneousSubmodule_eq_bot_of_neg {d : ℤ} (hd : d < 0) :
    integerHomogeneousSubmodule k σ d = ⊥ := by
  cases d with
  | ofNat n => exact ((not_lt_of_ge (Int.natCast_nonneg n)) hd).elim
  | negSucc n => rfl

attribute [local instance] MvPolynomial.gradedAlgebra

private noncomputable def naturalPieceEquivIntegerPiece (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ k n ≃ₗ[k]
      integerHomogeneousSubmodule k σ (n : ℤ) where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' r x := by ext; rfl

private noncomputable def naturalToIntegerDirectSum :
    (⨁ n : ℕ, MvPolynomial.homogeneousSubmodule σ k n) →ₗ[k]
      ⨁ d : ℤ, integerHomogeneousSubmodule k σ d :=
  DirectSum.toModule k ℕ _ fun n ↦
    (DirectSum.lof k ℤ (fun d ↦ ↑(integerHomogeneousSubmodule k σ d))
      (n : ℤ)).comp (naturalPieceEquivIntegerPiece k σ n).toLinearMap

private noncomputable def integerDecomposeLinearMap :
    MvPolynomial σ k →ₗ[k] ⨁ d : ℤ, integerHomogeneousSubmodule k σ d :=
  (naturalToIntegerDirectSum k σ).comp
    (DirectSum.decomposeLinearEquiv
      (MvPolynomial.homogeneousSubmodule σ k)).toLinearMap

private theorem integerDecomposeLinearMap_of_mem
    {p : MvPolynomial σ k} {n : ℕ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule σ k n) :
    integerDecomposeLinearMap k σ p =
      DirectSum.lof k ℤ (fun d ↦ ↑(integerHomogeneousSubmodule k σ d))
        (n : ℤ) (naturalPieceEquivIntegerPiece k σ n ⟨p, hp⟩) := by
  change (naturalToIntegerDirectSum k σ)
    (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ k) p) = _
  rw [DirectSum.decompose_of_mem (MvPolynomial.homogeneousSubmodule σ k) hp]
  change (naturalToIntegerDirectSum k σ)
    (DirectSum.lof k ℕ (fun n ↦ ↑(MvPolynomial.homogeneousSubmodule σ k n))
      n ⟨p, hp⟩) = _
  rw [naturalToIntegerDirectSum, DirectSum.toModule_lof, LinearMap.comp_apply]
  rfl

private theorem integerRecompose_decompose (p : MvPolynomial σ k) :
    DirectSum.coeLinearMap (integerHomogeneousSubmodule k σ)
      (integerDecomposeLinearMap k σ p) = p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial d r =>
      have hhom : MvPolynomial.monomial d r ∈
          MvPolynomial.homogeneousSubmodule σ k d.degree :=
        MvPolynomial.isHomogeneous_monomial r rfl
      rw [integerDecomposeLinearMap_of_mem k σ hhom,
        DirectSum.coeLinearMap_lof]
      rfl

private theorem integerDecompose_recompose :
    (integerDecomposeLinearMap k σ).comp
        (DirectSum.coeLinearMap (integerHomogeneousSubmodule k σ)) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  cases d with
  | ofNat n =>
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof,
        LinearMap.id_apply]
      have hx : (x : MvPolynomial σ k) ∈
          MvPolynomial.homogeneousSubmodule σ k n := by
        simpa using x.property
      rw [integerDecomposeLinearMap_of_mem k σ hx]
      congr 1
  | negSucc n =>
      have hx : x = 0 := by
        apply Subtype.ext
        simpa [integerHomogeneousSubmodule] using x.property
      subst x
      simp only [map_zero]

/-- The integer-indexed homogeneous pieces form a direct-sum decomposition of
the polynomial ring. -/
noncomputable instance integerHomogeneousDecomposition :
    DirectSum.Decomposition (integerHomogeneousSubmodule k σ) :=
  DirectSum.Decomposition.ofLinearMap (integerHomogeneousSubmodule k σ)
    (integerDecomposeLinearMap k σ)
    (by
      apply LinearMap.ext
      intro p
      exact integerRecompose_decompose k σ p)
    (integerDecompose_recompose k σ)

/-- Multiplication respects the integer grading.  If either index is negative,
the corresponding factor belongs to the zero submodule. -/
noncomputable instance integerHomogeneousGradedMonoid :
    SetLike.GradedMonoid (integerHomogeneousSubmodule k σ) where
  one_mem := by
    change MvPolynomial.IsHomogeneous (1 : MvPolynomial σ k) 0
    exact MvPolynomial.isHomogeneous_one σ k
  mul_mem i j x y hx hy := by
    cases i with
    | ofNat m =>
        cases j with
        | ofNat n =>
            have hij : Int.ofNat m + Int.ofNat n = Int.ofNat (m + n) := by
              simp
            rw [hij]
            exact MvPolynomial.IsHomogeneous.mul hx hy
        | negSucc n =>
            have hy0 : y = 0 := by
              simpa [integerHomogeneousSubmodule] using hy
            subst y
            simpa only [mul_zero] using
              (integerHomogeneousSubmodule k σ _).zero_mem
    | negSucc m =>
        have hx0 : x = 0 := by
          simpa [integerHomogeneousSubmodule] using hx
        subst x
        simpa only [zero_mul] using
          (integerHomogeneousSubmodule k σ _).zero_mem

/-- The usual total-degree grading of a polynomial ring, extended from
natural to integer degrees by zero in negative degrees. -/
noncomputable instance integerHomogeneousGradedAlgebra :
    GradedAlgebra (integerHomogeneousSubmodule k σ) where

/-- A polynomial is homogeneous for the integer grading exactly when it is
homogeneous for the usual natural-number grading.  The zero polynomial in a
negative piece causes no discrepancy, since it lies in every natural piece. -/
theorem isHomogeneousElem_integer_iff {p : MvPolynomial σ k} :
    SetLike.IsHomogeneousElem (integerHomogeneousSubmodule k σ) p ↔
      SetLike.IsHomogeneousElem (MvPolynomial.homogeneousSubmodule σ k) p := by
  constructor
  · rintro ⟨d, hd⟩
    cases d with
    | ofNat n => exact ⟨n, by simpa using hd⟩
    | negSucc n =>
        have hp : p = 0 := by
          simpa [integerHomogeneousSubmodule] using hd
        subst p
        exact ⟨0, (MvPolynomial.homogeneousSubmodule σ k 0).zero_mem⟩
  · rintro ⟨n, hn⟩
    exact ⟨(n : ℤ), by simpa using hn⟩

/-- An ideal is homogeneous for the integer grading exactly when it is
homogeneous for the existing natural total-degree grading. -/
theorem ideal_isHomogeneous_integer_iff (I : Ideal (MvPolynomial σ k)) :
    I.IsHomogeneous (integerHomogeneousSubmodule k σ) ↔
      IsHomogeneousIdeal I := by
  change I.IsHomogeneous (integerHomogeneousSubmodule k σ) ↔
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)
  have hsubmonoid :
      SetLike.homogeneousSubmonoid (integerHomogeneousSubmodule k σ) =
        SetLike.homogeneousSubmonoid
          (MvPolynomial.homogeneousSubmodule σ k) := by
    ext p
    exact isHomogeneousElem_integer_iff k σ
  rw [Ideal.IsHomogeneous.iff_exists, Ideal.IsHomogeneous.iff_exists,
    hsubmonoid]

end Hartshorne
