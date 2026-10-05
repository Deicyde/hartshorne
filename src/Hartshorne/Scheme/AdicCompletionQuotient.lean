/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Quotients of an adic completion

Hartshorne, *Algebraic Geometry*, Theorem II.9.3A(a) (pp. 193–194).

For a Noetherian ring, reduction from the adic completion induces an
isomorphism modulo each positive power of the defining ideal.
-/

open Submodule

namespace Hartshorne

/-- **Hartshorne II.9.3A(a).** Reduction modulo `I ^ (n + 1)` induces a ring
isomorphism from the corresponding quotient of the `I`-adic completion to
`A ⧸ I ^ (n + 1)`. -/
theorem exists_adicCompletionQuotientRingEquiv
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ∃ e : (AdicCompletion I A ⧸
        (I ^ (n + 1)).map (algebraMap A (AdicCompletion I A))) ≃+* (A ⧸ I ^ (n + 1)),
      e.toRingHom.comp
          (Ideal.Quotient.mk ((I ^ (n + 1)).map (algebraMap A (AdicCompletion I A)))) =
        (AdicCompletion.evalₐ I (n + 1)).toRingHom := by
  classical
  let f : AdicCompletion I A →+* A ⧸ I ^ (n + 1) :=
    (AdicCompletion.evalₐ I (n + 1)).toRingHom
  have hf : Function.Surjective f := AdicCompletion.surjective_evalₐ I (n + 1)
  have hker : RingHom.ker f =
      (I ^ (n + 1)).map (algebraMap A (AdicCompletion I A)) := by
    ext x
    change AdicCompletion.evalₐ I (n + 1) x = 0 ↔
      x ∈ Submodule.restrictScalars A
        ((I ^ (n + 1)).map (algebraMap A (AdicCompletion I A)))
    rw [← Ideal.smul_top_eq_map]
    rw [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing]
    rw [LinearMap.mem_ker]
    have eq : I ^ (n + 1) * (⊤ : Ideal A) = I ^ (n + 1) := by simp
    have hinj : Function.Injective (Ideal.Quotient.factor (le_of_eq eq)) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker] using
        Ideal.map_mk_eq_bot_of_le (le_of_eq eq.symm)
    simpa [← AdicCompletion.factor_eval_eq_evalₐ] using map_eq_zero_iff _ hinj
  let e := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hf)
  refine ⟨e, ?_⟩
  ext x
  change (RingHom.quotientKerEquivOfSurjective hf)
    ((Ideal.quotEquivOfEq hker.symm)
      ((Ideal.Quotient.mk
        ((I ^ (n + 1)).map (algebraMap A (AdicCompletion I A)))) x)) = _
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

end Hartshorne
