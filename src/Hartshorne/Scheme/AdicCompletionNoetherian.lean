/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Noetherianity of adic completion

Hartshorne, *Algebraic Geometry*, Theorem II.9.3A(d) (pp. 193–194).

If `A` is Noetherian and `I = (a₁, …, aₙ)`, evaluation `Xᵢ ↦ aᵢ` maps the ideal of variables
of `A[X₁, …, Xₙ]` onto `I`, so it induces a ring homomorphism between the adic completions.
That map is surjective: compatible representatives in `A` are lifted step by step, adding at
stage `k` a preimage in the `k`-th power of the ideal of variables. Mathlib identifies the
completion of the polynomial ring at the ideal of variables with the power-series ring
`A⟦X₁, …, Xₙ⟧`, which is Noetherian, so `Â` is a quotient of a Noetherian ring.
-/

namespace Hartshorne

open AdicCompletion

variable {A : Type*} [CommRing A]

private lemma map_aeval_idealOfVars_pow {n : ℕ} (a : Fin n → A) (k : ℕ) :
    ((MvPolynomial.idealOfVars (Fin n) A) ^ k).map
      (MvPolynomial.aeval a : MvPolynomial (Fin n) A →ₐ[A] A) = Ideal.span (Set.range a) ^ k := by
  rw [Ideal.map_pow, MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  congr 3
  ext i
  simp

/-- Evaluation at a generating family of `I`, at finite level `k`. -/
private noncomputable def completionAevalLevel {n : ℕ} (a : Fin n → A) (k : ℕ) :
    AdicCompletion (MvPolynomial.idealOfVars (Fin n) A) (MvPolynomial (Fin n) A) →+*
      A ⧸ Ideal.span (Set.range a) ^ k :=
  (Ideal.quotientMap _ (MvPolynomial.aeval a : MvPolynomial (Fin n) A →ₐ[A] A).toRingHom
    (Ideal.map_le_iff_le_comap.mp (map_aeval_idealOfVars_pow a k).le)).comp
      (evalₐ _ k).toRingHom

private lemma completionAevalLevel_mk {n : ℕ} (a : Fin n → A) (k : ℕ)
    (b : AdicCauchySequence (MvPolynomial.idealOfVars (Fin n) A) (MvPolynomial (Fin n) A)) :
    completionAevalLevel a k (AdicCompletion.mk _ _ b) =
      Ideal.Quotient.mk _ (MvPolynomial.aeval a (b k)) := by
  simp only [completionAevalLevel, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    evalₐ_mk, Ideal.quotientMap_mk]

private lemma completionAevalLevel_compat {n : ℕ} (a : Fin n → A) {m k : ℕ} (hle : m ≤ k) :
    (Ideal.Quotient.factorPow (Ideal.span (Set.range a)) hle).comp (completionAevalLevel a k) =
      completionAevalLevel a m := by
  ext x
  induction x using AdicCompletion.induction_on with
  | h b =>
    rw [RingHom.comp_apply, completionAevalLevel_mk, completionAevalLevel_mk,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
    refine (Ideal.map_le_iff_le_comap.mp (map_aeval_idealOfVars_pow a m).le) ?_
    have := b.property hle
    rw [SModEq.sub_mem] at this
    rw [← neg_sub]
    exact neg_mem (by simpa using this)

/-- Evaluation at a generating family of `I`, on completions. -/
private noncomputable def completionAeval {n : ℕ} (a : Fin n → A) :
    AdicCompletion (MvPolynomial.idealOfVars (Fin n) A) (MvPolynomial (Fin n) A) →+*
      AdicCompletion (Ideal.span (Set.range a)) A :=
  AdicCompletion.liftRingHom (Ideal.span (Set.range a)) (completionAevalLevel a)
    (completionAevalLevel_compat a)

private lemma completionAeval_surjective {n : ℕ} (a : Fin n → A) :
    Function.Surjective (completionAeval a) := by
  set φ : MvPolynomial (Fin n) A →ₐ[A] A := MvPolynomial.aeval a
  set J := MvPolynomial.idealOfVars (Fin n) A
  have hφ : Function.Surjective φ := fun x => ⟨MvPolynomial.C x, by simp [φ]⟩
  intro y
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  have hd : ∀ k, ∃ p ∈ J ^ k, φ p = c (k + 1) - c k := by
    intro k
    have h := c.property (Nat.le_succ k)
    rw [SModEq.sub_mem] at h
    have h' : c (k + 1) - c k ∈ (J ^ k).map φ := by
      rw [map_aeval_idealOfVars_pow]
      rw [← neg_sub]
      exact neg_mem (by simpa using h)
    exact (Ideal.mem_map_iff_of_surjective φ hφ).mp h'
  choose p hpJ hp using hd
  let Q : ℕ → MvPolynomial (Fin n) A := fun k =>
    Nat.rec (MvPolynomial.C (c 0)) (fun k q => q + p k) k
  have hQ : ∀ k, φ (Q k) = c k := by
    intro k
    induction k with
    | zero => simp [Q, φ]
    | succ k ih =>
      change φ (Q k + p k) = _
      rw [map_add, ih, hp]
      abel
  let Qc : AdicCauchySequence J (MvPolynomial (Fin n) A) :=
    AdicCauchySequence.mk J _ Q (fun k => by
      rw [SModEq.sub_mem]
      change Q k - (Q k + p k) ∈ _
      rw [sub_add_cancel_left]
      exact neg_mem (by simpa using hpJ k))
  refine ⟨AdicCompletion.mk J _ Qc, AdicCompletion.ext_evalₐ fun k => ?_⟩
  rw [completionAeval, evalₐ_liftRingHom, completionAevalLevel_mk, evalₐ_mk]
  exact congrArg _ (hQ k)

/-- **Hartshorne II, Theorem 9.3A(d).** The adic completion of a Noetherian ring with respect
to any ideal is a Noetherian ring. -/
theorem isNoetherianRing_adicCompletion [IsNoetherianRing A] (I : Ideal A) :
    IsNoetherianRing (AdicCompletion I A) := by
  obtain ⟨n, a, ha⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  have hI : Ideal.span (Set.range a) = I := ha
  subst hI
  have : IsNoetherianRing
      (AdicCompletion (MvPolynomial.idealOfVars (Fin n) A) (MvPolynomial (Fin n) A)) :=
    isNoetherianRing_of_ringEquiv _ (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) A).toRingEquiv
  exact isNoetherianRing_of_surjective _ _ (completionAeval a) (completionAeval_surjective a)

end Hartshorne
