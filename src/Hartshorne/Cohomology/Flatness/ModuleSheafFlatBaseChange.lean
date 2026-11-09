/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.Flatness.ModuleSheafFlatOverBase
import Hartshorne.Cohomology.Flatness.FlatTensorFlatAlgebra
import Hartshorne.Scheme.FiberProductLocalRing
import Hartshorne.Scheme.ModulePullbackStalk

/-!
# Base change of a module sheaf flat over a base

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.2(b) (p. 254).

Let `f : X → Y`, let `F` be an `𝒪_X`-module flat over `Y`, and let `g : Y' → Y`. Then the module
pullback of `F` along the projection `X' = X ×_Y Y' → X` is flat over `Y'`.

Write `A = 𝒪_{X,x}`, `B = 𝒪_{Y,y}`, `B' = 𝒪_{Y',y'}` and `C = 𝒪_{X',x'}`. The stalk of the
pullback is `C ⊗_A F_x` (`Hartshorne.pullbackStalkLinearEquiv`), `C` is flat over
`R = A ⊗_B B'` (`Hartshorne.FiberProductStalk.flat_tensorToStalk`), and
`C ⊗_A F_x ≅ C ⊗_R (R ⊗_A F_x)` with `R ⊗_A F_x ≅ B' ⊗_B F_x` flat over `B'`; so
`Hartshorne.flat_tensorProduct_of_flat_algebra` applies.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Hartshorne

universe u

/-- Let `B → A` and `B → B'` be ring maps and `R = A ⊗_B B'`, and let `C` be a flat `R`-algebra.
If `F` is an `A`-module flat over `B`, then `C ⊗_A F` is flat over `B'`. -/
theorem flat_tensorProduct_of_flat_of_flat_tensor {B A B' C F : Type u} [CommRing B] [CommRing A]
    [CommRing B'] [CommRing C] [Algebra B A] [Algebra B B'] [Algebra (A ⊗[B] B') C]
    [Algebra A C] [Algebra B' C] [IsScalarTower A (A ⊗[B] B') C] [SMulCommClass A B' C]
    (hB' : ∀ b : B', algebraMap (A ⊗[B] B') C ((1 : A) ⊗ₜ b) = algebraMap B' C b)
    [AddCommGroup F] [Module A F] [Module B F] [IsScalarTower B A F] [Module.Flat B F]
    [Module.Flat (A ⊗[B] B') C] :
    Module.Flat B' (C ⊗[A] F) := by
  let : Algebra B' (A ⊗[B] B') := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B' (A ⊗[B] B') C := IsScalarTower.of_algebraMap_eq fun b => (hB' b).symm
  have : IsScalarTower B B' (A ⊗[B] B') := IsScalarTower.of_algebraMap_eq fun b => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  have : Algebra.IsPushout B B' A (A ⊗[B] B') := TensorProduct.isPushout'
  have hN : Module.Flat B' ((A ⊗[B] B') ⊗[A] F) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange B B' A (A ⊗[B] B') F)
  have := flat_tensorProduct_of_flat_algebra (B' := B') (S := A ⊗[B] B') (C := C)
    (N := (A ⊗[B] B') ⊗[A] F)
  exact Module.Flat.of_linearEquiv
    ((AlgebraTensorModule.cancelBaseChange A (A ⊗[B] B') C C F).symm.restrictScalars B')

open AlgebraicGeometry FiberProductStalk

/-- **Hartshorne III.9, Proposition 9.2(b).** Let `f : X → Y`, let `F` be an `𝒪_X`-module flat over
`Y`, and let `g : Y' → Y`. Then the module pullback of `F` along the projection
`X ×_Y Y' → X` is flat over `Y'`. -/
theorem Scheme.Modules.FlatOver.baseChange {X Y Y' : Scheme.{u}} {f : X ⟶ Y} {F : X.Modules}
    (hF : F.FlatOver f) (g : Y' ⟶ Y) :
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F).FlatOver (pullback.snd f g) := by
  intro x'
  let A := X.presheaf.stalk (pullback.fst f g x')
  let B := Y.presheaf.stalk (f (pullback.fst f g x'))
  let B' := Y'.presheaf.stalk (pullback.snd f g x')
  let C := (pullback f g).presheaf.stalk x'
  let FX : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  let Fx := ↑(TopCat.Presheaf.stalk (C := Ab) FX.presheaf (pullback.fst f g x'))
  let : Algebra B A := algebraLeft f g x'
  let : Algebra B B' := algebraRight f g x'
  let : Algebra (A ⊗[B] B') C := (tensorToStalk f g x').toAlgebra
  let : Algebra A C := ((pullback.fst f g).stalkMap x').hom.toAlgebra
  let : Algebra B' C := ((pullback.snd f g).stalkMap x').hom.toAlgebra
  let : Module B Fx := Module.compHom _ (f.stalkMap (pullback.fst f g x')).hom
  have : Module.Flat B Fx := hF (pullback.fst f g x')
  have : IsScalarTower B A Fx := ⟨fun b a m => by
    change ((f.stalkMap _).hom b * a) • m = (f.stalkMap _).hom b • (a • m)
    rw [mul_smul]⟩
  have : IsScalarTower A (A ⊗[B] B') C := IsScalarTower.of_algebraMap_eq fun a => by
    change _ = tensorToStalk f g x' (a ⊗ₜ 1)
    rw [tensorToStalk_tmul, map_one, mul_one]
    rfl
  have : SMulCommClass A B' C := ⟨fun a b c => by
    simp only [Algebra.smul_def]
    ring⟩
  have hB' : ∀ b : B', algebraMap (A ⊗[B] B') C ((1 : A) ⊗ₜ b) = algebraMap B' C b := fun b => by
    change tensorToStalk f g x' (1 ⊗ₜ b) = _
    rw [tensorToStalk_tmul, map_one, one_mul]
    rfl
  have : Module.Flat (A ⊗[B] B') C := flat_tensorToStalk f g x'
  have key : Module.Flat B' (C ⊗[A] Fx) :=
    flat_tensorProduct_of_flat_of_flat_tensor (B := B) (A := A) (B' := B') (C := C) (F := Fx) hB'
  let : Module (ringSheafStalk (Limits.pullback f g).sheaf x')
      ((ModuleCat.extendScalars ((pullback.fst f g).stalkMap x').hom).obj
        ((Ringed.moduleStalkFunctor (R := X.sheaf) (pullback.fst f g x')).obj F)) :=
    ModuleCat.isModule _
  let e₀ : ↑((Ringed.moduleStalkFunctor (R := (Limits.pullback f g).sheaf) x').obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ≃ₗ[
          ringSheafStalk (Limits.pullback f g).sheaf x']
      ↑((ModuleCat.extendScalars ((pullback.fst f g).stalkMap x').hom).obj
        ((Ringed.moduleStalkFunctor (R := X.sheaf) (pullback.fst f g x')).obj F)) :=
    pullbackStalkLinearEquiv (pullback.fst f g) x' F
  let GX : PresheafOfModules.{u} ((Limits.pullback f g).presheaf ⋙ forget₂ CommRingCat RingCat) :=
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F).val
  let Gx := ↑(TopCat.Presheaf.stalk (C := Ab) GX.presheaf x')
  let : Module B' Gx := Module.compHom _ ((pullback.snd f g).stalkMap x').hom
  change Module.Flat B' Gx
  let e : Gx ≃ₗ[B'] C ⊗[A] Fx :=
    { toFun := fun m => e₀ m
      invFun := fun t => e₀.symm t
      map_add' := fun m m' => e₀.map_add m m'
      map_smul' := fun b m => e₀.map_smul ((pullback.snd f g).stalkMap x' b) m
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv }
  exact Module.Flat.of_linearEquiv e

end Hartshorne
