/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensoring a flat module with a flat algebra

Let `B' → S → C` be ring maps with `C` flat over `S`, and let `N` be an `S`-module which is
flat over `B'`. Then `C ⊗_S N` is flat over `B'` (`Hartshorne.flat_tensorProduct_of_flat_algebra`):
for a `B'`-module `P`, `(C ⊗_S N) ⊗_{B'} P ≅ C ⊗_S (N ⊗_{B'} P)`, and both tensor functors
preserve injections.
-/

open TensorProduct

namespace Hartshorne

universe u

/-- If `C` is a flat `S`-algebra and `N` is an `S`-module which is flat over `B'` (for ring maps
`B' → S → C`), then `C ⊗_S N` is flat over `B'`, acting through `C`. -/
theorem flat_tensorProduct_of_flat_algebra {B' S C N : Type u} [CommRing B'] [CommRing S]
    [CommRing C] [Algebra B' S] [Algebra S C] [Algebra B' C] [IsScalarTower B' S C]
    [AddCommGroup N] [Module S N] [Module B' N] [IsScalarTower B' S N]
    [Module.Flat B' N] [Module.Flat S C] : Module.Flat B' (C ⊗[S] N) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  let e := AlgebraTensorModule.assoc B' S S C N I
  let e' := AlgebraTensorModule.assoc B' S S C N B'
  let g : N ⊗[B'] I →ₗ[S] N ⊗[B'] B' := AlgebraTensorModule.lTensor S N I.subtype
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := N) I.subtype Subtype.val_injective
  have hCg : Function.Injective (g.lTensor C) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := C) g hg
  have key : ∀ z, e' ((LinearMap.lTensor (C ⊗[S] N) I.subtype) z) = g.lTensor C (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a i =>
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
      | tmul c n => rfl
  intro z w hzw
  apply e.injective
  apply hCg
  rw [← key, ← key, hzw]

end Hartshorne
