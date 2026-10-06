/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama

/-!
# Faithfulness of maximal-adic completion on finite modules

Over a Noetherian local ring, surjectivity of a map between finite modules can
be detected after completion at the maximal ideal.
-/

universe u

namespace Hartshorne

open IsLocalRing

/-- Let `u : M →ₗ[A] N` be a map of finite modules over a Noetherian local
ring. If the induced map on maximal-adic completions is surjective, then `u`
is surjective. -/
theorem surjective_of_maximalAdicCompletionMap_surjective
    {A M N : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (u : M →ₗ[A] N)
    (hu : Function.Surjective (AdicCompletion.map (maximalIdeal A) u)) :
    Function.Surjective u := by
  let m := maximalIdeal A
  apply LinearMap.surjective_of_surjective_comp_mkQ u (m ^ 1)
    (by simpa only [pow_one] using IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
  intro ybar
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (m ^ 1 • (⊤ : Submodule A N)) ybar
  obtain ⟨xhat, hxhat⟩ := hu (AdicCompletion.of m N y)
  obtain ⟨x, hx⟩ :=
    Submodule.mkQ_surjective (m ^ 1 • (⊤ : Submodule A M)) (xhat.val 1)
  refine ⟨x, ?_⟩
  have hxhat₁ := congrArg (fun z : AdicCompletion m N ↦ z.val 1) hxhat
  simp only [AdicCompletion.map_val_apply, AdicCompletion.of_apply] at hxhat₁
  rw [← hx] at hxhat₁
  dsimp [m] at hxhat₁ ⊢
  simpa only [LinearMap.reduceModIdeal_apply, LinearMap.coe_comp,
    Function.comp_apply] using hxhat₁

end Hartshorne
