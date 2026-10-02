/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.HilbertSerre

/-!
# Hilbert polynomials of shifted homogeneous prime quotients

Hartshorne, *Algebraic Geometry*, Theorem I.7.5 (pp. 51--52).

This is the shifted-prime specialization of Hilbert--Serre.  It records the
eventual Hilbert polynomial of `(k[x₀,…,xₙ] / p)(l)`, including the empty
support case and the exact projective-dimension, degree, and positivity
statements.
-/

namespace Hartshorne

open DirectSum MvPolynomial Polynomial Set TopologicalSpace
open scoped Polynomial

noncomputable section

universe u

/-- A shift of a quotient by a homogeneous prime ideal has a unique numerical
Hilbert polynomial.  Its degree is the projective dimension of the zero set of
the prime; empty support gives the zero polynomial, while finite dimension
`r` gives a nonzero polynomial of natural degree `r` and positive leading
coefficient. -/
theorem existsUnique_hilbertPolynomial_primeQuotient
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
    (hp : p.1.IsHomogeneous
      (integerHomogeneousSubmodule k (Fin (n + 1))))
    (l : ℤ) :
    let 𝒜 := integerHomogeneousSubmodule k (Fin (n + 1))
    let ℱ := gradedQuotientPiece 𝒜 𝒜
      (homogeneousIdealSubmodule 𝒜 p.1 hp)
    let Z := projZeroSet
      (p.1 : Set (MvPolynomial (Fin (n + 1)) k))
    ∃! P : ℚ[X],
      IsHilbertPolynomial (σ := Fin (n + 1))
          (gradedModuleTwist ℱ l) P ∧
        hilbertPolynomialDegree P = projDim Z ∧
        (Z.Nonempty → 0 < P.leadingCoeff) ∧
        (Z = ∅ → P = 0) ∧
        ∀ r : ℕ, projDim Z = (r : WithBot ℕ∞) →
          P ≠ 0 ∧ P.natDegree = r ∧ 0 < P.leadingCoeff := by
  dsimp only
  let 𝒜 := integerHomogeneousSubmodule k (Fin (n + 1))
  let ℱ := gradedQuotientPiece 𝒜 𝒜
    (homogeneousIdealSubmodule 𝒜 p.1 hp)
  let ℱl := gradedModuleTwist ℱ l
  have hann : Module.annihilator (MvPolynomial (Fin (n + 1)) k)
      (MvPolynomial (Fin (n + 1)) k ⧸
        (homogeneousIdealSubmodule 𝒜 p.1 hp).toSubmodule) = p.1 := by
    change Module.annihilator (MvPolynomial (Fin (n + 1)) k)
      (MvPolynomial (Fin (n + 1)) k ⧸ p.1) = p.1
    exact Ideal.annihilator_quotient
  let P : ℚ[X] :=
    gradedHilbertPolynomial (k := k) (n := n) ℱl
  have hP : IsHilbertPolynomial (σ := Fin (n + 1)) ℱl P :=
    gradedHilbertPolynomial_isHilbertPolynomial
      (k := k) (n := n) ℱl
  have hdegree : hilbertPolynomialDegree P =
      projDim (projZeroSet
        (p.1 : Set (MvPolynomial (Fin (n + 1)) k))) := by
    simpa only [P, ℱl, hann] using
      (gradedHilbertPolynomial_degree
        (k := k) (n := n) ℱl)
  have hleading :
      (projZeroSet
        (p.1 : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
        0 < P.leadingCoeff := by
    intro hZ
    exact gradedHilbertPolynomial_leadingCoeff_pos
      (k := k) (n := n) ℱl (by
        simpa only [hann] using hZ)
  have hempty : projZeroSet
      (p.1 : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ → P = 0 := by
    intro hZ
    exact gradedHilbertPolynomial_eq_zero_of_support_eq_empty
      (k := k) (n := n) ℱl (by
        simpa only [hann] using hZ)
  have hfinite : ∀ r : ℕ,
      projDim (projZeroSet
        (p.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
          (r : WithBot ℕ∞) →
        P ≠ 0 ∧ P.natDegree = r ∧ 0 < P.leadingCoeff := by
    intro r hr
    have hPne : P ≠ 0 := by
      intro hPzero
      have hbot : (⊥ : WithBot ℕ∞) = (r : WithBot ℕ∞) := by
        simpa [hilbertPolynomialDegree, hPzero] using hdegree.trans hr
      simp at hbot
    have hnatDegree : P.natDegree = r := by
      have hcast : (P.natDegree : WithBot ℕ∞) =
          (r : WithBot ℕ∞) := by
        simpa [hilbertPolynomialDegree, hPne] using hdegree.trans hr
      exact_mod_cast hcast
    have hZ : (projZeroSet
        (p.1 : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hZempty
      exact hPne (hempty hZempty)
    exact ⟨hPne, hnatDegree, hleading hZ⟩
  refine ⟨P, ⟨hP, hdegree, hleading, hempty, hfinite⟩, ?_⟩
  intro Q hQ
  have toHilbertSerreSpec : ∀ {R : ℚ[X]},
      IsHilbertPolynomial (σ := Fin (n + 1)) ℱl R ∧
        hilbertPolynomialDegree R =
          projDim (projZeroSet
            (p.1 : Set (MvPolynomial (Fin (n + 1)) k))) ∧
        ((projZeroSet
          (p.1 : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
            0 < R.leadingCoeff) →
      IsHilbertPolynomial (σ := Fin (n + 1)) ℱl R ∧
        hilbertPolynomialDegree R =
          projDim (projZeroSet
            (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
              (MvPolynomial (Fin (n + 1)) k ⧸
                (homogeneousIdealSubmodule 𝒜 p.1 hp).toSubmodule) :
                  Set (MvPolynomial (Fin (n + 1)) k))) ∧
        ((projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
            (MvPolynomial (Fin (n + 1)) k ⧸
              (homogeneousIdealSubmodule 𝒜 p.1 hp).toSubmodule) :
                Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
          0 < R.leadingCoeff) := by
    intro R hR
    simpa only [hann] using hR
  exact (hilbertSerre (k := k) (n := n) ℱl).unique
    (toHilbertSerreSpec ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩)
    (toHilbertSerreSpec ⟨hP, hdegree, hleading⟩)

end

end Hartshorne
