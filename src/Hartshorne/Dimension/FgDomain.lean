/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.FgAlgebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Theorem 1.8A(a): dimension equals transcendence degree

Hartshorne, *Algebraic Geometry*, I.1, Theorem 1.8A(a) (p. 6).

Let `k` be a field and `B` a domain that is a finitely generated `k`-algebra.
Then `dim B` is the transcendence degree of `K(B)` over `k`.

Hartshorne quotes this without proof, citing Matsumura and Atiyah–Macdonald.
Both sides are computed from the same Noether normalisation
`k[y₁,…,y_s] ↪ B`, and the content is that `s` answers both questions.

* On the dimension side, `B` is integral over `k[y₁,…,y_s]`, integral
  extensions preserve the Krull dimension, and `dim k[y₁,…,y_s] = s`.
* On the transcendence side, `B` is algebraic over `k[y₁,…,y_s]`, so it
  contributes nothing, and the `y` are algebraically independent, so
  `trdeg_k B = s`. Passing to `K(B)` changes nothing either, because a fraction
  field is algebraic over its domain.

Both sides therefore reduce to additivity of transcendence degree in a tower
with an algebraic top, which is Stacks 030H and is in Mathlib.

The statement is phrased as a single natural number `s` answering both, rather
than as an equation between a `WithBot ℕ∞` and a `Cardinal`. That is not a
dodge: it is the only way to say `dim B = trdeg_k K(B)` without inventing a
coercion between the two, and it is stronger, since it also records that both
are finite.

## Main results

* `Hartshorne.isAlgebraic_of_isFractionRing`
* `Hartshorne.exists_ringKrullDim_eq_trdeg`
-/

namespace Hartshorne

open Algebra Polynomial

universe u

/-- A fraction field is algebraic over its domain: `a/b` is a root of
`bX - a`.

Mathlib has the fraction field of an algebraic extension and the algebraicity
of one fraction field over another, but not this. -/
theorem isAlgebraic_of_isFractionRing (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Algebra.IsAlgebraic R K := by
  constructor
  intro x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb0 : algebraMap R K b ≠ 0 :=
    fun h => hb' (IsFractionRing.injective R K (by simpa using h))
  refine ⟨C b * X - C a, fun h => hb' ?_, ?_⟩
  · simpa using congrArg (fun p => Polynomial.coeff p 1) h
  · rw [map_sub, aeval_mul, aeval_C, aeval_C, aeval_X, mul_div_cancel₀ _ hb0, sub_self]

variable (k R K : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  [Algebra.FiniteType k R] [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
  [IsFractionRing R K]

/-- **Theorem 1.8A(a)**: the dimension of a finitely generated domain over a
field is the transcendence degree of its fraction field.

One Noether normalisation `k[y₁,…,y_s] ↪ R` answers both: `R` is integral over
the polynomial ring, so it has the same dimension, and it is algebraic over it,
so it has the same transcendence degree. The fraction field is in turn algebraic
over `R`, so it does not move the transcendence degree either. -/
theorem exists_ringKrullDim_eq_trdeg :
    ∃ s : ℕ, ringKrullDim R = s ∧ Algebra.trdeg k K = s := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k R
  -- View `R` as an algebra over the polynomial ring via the normalisation map.
  let : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) R :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) R := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine ⟨s, ?_, ?_⟩
  · -- Dimension: the integral extension preserves it, and `dim k[y₁,…,y_s] = s`.
    rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) R,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  · -- Transcendence degree: `R` over `k[y₁,…,y_s]` and `K` over `R` are both algebraic,
    -- so both steps of the tower contribute `0`.
    have : Algebra.IsAlgebraic R K := isAlgebraic_of_isFractionRing R K
    have : FaithfulSMul R K :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective R K)
    have hPR : Algebra.trdeg (MvPolynomial (Fin s) k) R = 0 := trdeg_eq_zero
    have hRK : Algebra.trdeg R K = 0 := trdeg_eq_zero
    have h₁ : Algebra.trdeg k (MvPolynomial (Fin s) k) + Algebra.trdeg (MvPolynomial (Fin s) k) R
        = Algebra.trdeg k R := trdeg_add_eq k (MvPolynomial (Fin s) k)
    have h₂ : Algebra.trdeg k R + Algebra.trdeg R K = Algebra.trdeg k K :=
      trdeg_add_eq k R
    rw [hPR, add_zero] at h₁
    rw [hRK, add_zero, ← h₁] at h₂
    rw [← h₂]
    simp

end Hartshorne
