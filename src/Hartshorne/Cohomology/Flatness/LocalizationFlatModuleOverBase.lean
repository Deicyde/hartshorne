/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.Localization

/-!
# Localization of a flat module over its base

Hartshorne, *Algebraic Geometry*, III.9, Example 9.1.1 (p. 254).

If a `B`-module is flat over a base semiring `A`, then localizing the module
along a submonoid of `B` preserves its flatness over `A`.
-/

open TensorProduct

namespace Hartshorne

universe u v w

/-- **Hartshorne III.9, Example 9.1.1.** If `M` is a `B`-module flat over `A`,
then its localization at a submonoid of `B`, restricted back to `A`, is flat
over `A`. -/
theorem localizedModule_flat_over_base
    {A : Type u} [CommSemiring A]
    {B : Type v} [CommSemiring B] [Algebra A B]
    {M : Type w} [AddCommMonoid M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Flat A M]
    (S : Submonoid B) : Module.Flat A (LocalizedModule S M) := by
  let _ : IsScalarTower A B (LocalizedModule S M) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      induction x using LocalizedModule.induction_on with
      | h m s =>
        rw [LocalizedModule.smul'_mk, LocalizedModule.smul'_mk,
          IsScalarTower.algebraMap_smul]
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  let g : M →ₗ[B] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  have hmap : Function.Injective
      (IsLocalizedModule.map S
        (AlgebraTensorModule.rTensor A N g)
        (AlgebraTensorModule.rTensor A P g)
        (AlgebraTensorModule.lTensor B M N.subtype)) := by
    apply IsLocalizedModule.map_injective
    exact Module.Flat.lTensor_preserves_injective_linearMap N.subtype Subtype.val_injective
  simpa only [IsLocalizedModule.map_lTensor,
    AlgebraTensorModule.coe_lTensor] using hmap

end Hartshorne
