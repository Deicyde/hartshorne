/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.TensorPowerSectionRing

/-!
# Functoriality of the section ring of tensor powers

A morphism `α : F ⟶ G` of sheaves of modules induces morphisms `T^n F ⟶ T^n G`,
`f₁ ⊗ ⋯ ⊗ fₙ ↦ α f₁ ⊗ ⋯ ⊗ α fₙ` (`TensorPowerSectionRing.powMap`), and these are multiplicative
on sections (`TensorPowerSectionRing.powMap_mul`). An isomorphism `F ≅ G` therefore induces
isomorphisms `T^n F ≅ T^n G` (`TensorPowerSectionRing.powIso`) compatible with the graded
multiplication of the section rings.
-/

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct DirectSum

namespace Hartshorne

universe u

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (ringCatSheafOf R)}

namespace ModuleSheafMultilinear

/-- Precomposition of a multilinear morphism with a morphism of the source. -/
noncomputable def precompHom {r : ℕ} (β : ModuleSheafMultilinear r G H) (α : F ⟶ G) :
    ModuleSheafMultilinear r F H where
  app U := (β.app U).compLinearMap (fun _ => (α.val.app U).hom)
  naturality i m := (β.naturality i _).trans
    (congrArg (β.app _) (funext fun k => (PresheafOfModules.naturality_apply α.val i (m k)).symm))

end ModuleSheafMultilinear

namespace TensorPowerSectionRing

open SheafAlgebraOperations

/-- The morphism `T^n F ⟶ T^n G`, `f₁ ⊗ ⋯ ⊗ fₙ ↦ α f₁ ⊗ ⋯ ⊗ α fₙ`, induced by `α : F ⟶ G`. -/
noncomputable def powMap (α : F ⟶ G) (n : ℕ) :
    moduleSheafTensorPower n F ⟶ moduleSheafTensorPower n G :=
  (moduleSheafTensorPowerHomEquiv n F _).symm
    ((moduleSheafTensorPowerMultilinear n G).precompHom α)

theorem powMap_tprod (α : F ⟶ G) (n : ℕ) (U : (Opens X)ᵒᵖ) (m : Fin n → F.val.obj U) :
    (powMap α n).val.app U ((moduleSheafTensorPowerMultilinear n F).app U m) =
      (moduleSheafTensorPowerMultilinear n G).app U (fun k => α.val.app U (m k)) :=
  Ringed.moduleSheafTensorPowerHomEquiv_symm_tprod _ U.unop m

theorem powMap_comp (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    powMap (α ≫ β) n = powMap α n ≫ powMap β n := by
  refine Ringed.moduleSheafTensorPower_hom_ext fun U m => ?_
  exact (powMap_tprod (α ≫ β) n (op U) m).trans ((powMap_tprod β n (op U) _).symm.trans
    (congrArg ((powMap β n).val.app (op U)) (powMap_tprod α n (op U) m).symm))

theorem powMap_id (n : ℕ) : powMap (𝟙 F) n = 𝟙 _ := by
  refine Ringed.moduleSheafTensorPower_hom_ext fun U m => ?_
  exact powMap_tprod (𝟙 F) n (op U) m

/-- The isomorphism `T^n F ≅ T^n G` induced by an isomorphism `F ≅ G`. -/
noncomputable def powIso (α : F ≅ G) (n : ℕ) :
    moduleSheafTensorPower n F ≅ moduleSheafTensorPower n G where
  hom := powMap α.hom n
  inv := powMap α.inv n
  hom_inv_id := by rw [← powMap_comp, α.hom_inv_id, powMap_id]
  inv_hom_id := by rw [← powMap_comp, α.inv_hom_id, powMap_id]

variable (F) in
/-- The product of two pure tensors is their concatenation. -/
theorem mul_tprod (U : (Opens X)ᵒᵖ) {m n : ℕ} (x : Fin m → F.val.obj U) (y : Fin n → F.val.obj U) :
    mul F U ((moduleSheafTensorPowerMultilinear m F).app U x)
        ((moduleSheafTensorPowerMultilinear n F).app U y) =
      (moduleSheafTensorPowerMultilinear (m + n) F).app U (Fin.append x y) := by
  have e : ∀ (k : ℕ) (z : Fin k → F.val.obj U),
      (moduleSheafTensorAlgebraι k F).val.app U ((moduleSheafTensorPowerMultilinear k F).app U z) =
        (sheafifyUnit (moduleSheafTensorAlgebraPresheaf F)).app U
          (TensorPower.toTensorAlgebra (PiTensorProduct.tprod _ z)) := fun k z =>
    sheafifyMap_unit (moduleSheafTensorAlgebraPresheafι k F) U (PiTensorProduct.tprod _ z)
  apply ι_injective F (m + n) U
  rw [ι_mul, e, e, e, moduleSheafTensorAlgebra_mul_unit, ← TensorPower.tprod_mul_tprod,
    TensorPower.toTensorAlgebra_gMul]

/-- **The morphisms `T^n F ⟶ T^n G` induced by `α : F ⟶ G` are multiplicative on sections.** -/
theorem powMap_mul (α : F ⟶ G) (U : (Opens X)ᵒᵖ) {m n : ℕ} (a : Component F U m)
    (b : Component F U n) :
    (powMap α (m + n)).val.app U (mul F U a b) =
      mul G U ((powMap α m).val.app U a) ((powMap α n).val.app U b) := by
  have base : ∀ (V : (Opens X)ᵒᵖ) (x : Fin m → F.val.obj V) (y : Fin n → F.val.obj V),
      (powMap α (m + n)).val.app V (mul F V ((moduleSheafTensorPowerMultilinear m F).app V x)
          ((moduleSheafTensorPowerMultilinear n F).app V y)) =
        mul G V ((powMap α m).val.app V ((moduleSheafTensorPowerMultilinear m F).app V x))
          ((powMap α n).val.app V ((moduleSheafTensorPowerMultilinear n F).app V y)) := by
    intro V x y
    rw [mul_tprod, powMap_tprod, powMap_tprod, powMap_tprod, mul_tprod]
    congr 1
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  have key : (moduleSheafTensorPowerMul m F n).postcomp (powMap α (m + n)).val =
      (moduleSheafTensorPowerMul m G n).precomp (powMap α m).val (powMap α n).val := by
    apply bilinear_ext_of_unit
    intro V p q
    have hL : (((moduleSheafTensorPowerMul m F n).app V).compl₁₂
        ((sheafifyUnit (moduleSheafTensorPowerPresheaf m F)).app V).hom
        ((sheafifyUnit (moduleSheafTensorPowerPresheaf n F)).app V).hom).compr₂
          ((powMap α (m + n)).val.app V).hom =
        ((moduleSheafTensorPowerMul m G n).app V).compl₁₂
          (((powMap α m).val.app V).hom ∘ₗ
            ((sheafifyUnit (moduleSheafTensorPowerPresheaf m F)).app V).hom)
          (((powMap α n).val.app V).hom ∘ₗ
            ((sheafifyUnit (moduleSheafTensorPowerPresheaf n F)).app V).hom) := by
      refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
      refine PiTensorProduct.ext (MultilinearMap.ext fun y => ?_)
      exact base V x y
    exact congrArg (fun L => L p q) hL
  exact congrArg (fun γ => γ.app U a b) key

theorem powMap_oneSec (α : F ⟶ G) (U : (Opens X)ᵒᵖ) :
    (powMap α 0).val.app U (oneSec F U) = oneSec G U := by
  have e : ∀ (H : SheafOfModules.{u} (ringCatSheafOf R)),
      oneSec H U = (moduleSheafTensorPowerMultilinear 0 H).app U Fin.elim0 := fun H =>
    congrArg ((sheafifyUnit (moduleSheafTensorPowerPresheaf 0 H)).app U) TensorPower.gOne_def
  rw [e F, e G, powMap_tprod]
  exact congrArg _ (funext fun k => k.elim0)

/-- The additive map `Γ(U, F^{⊗ n}) → Γ(U, G^{⊗ n})` induced by `α : F ⟶ G`. -/
noncomputable def componentMap (α : F ⟶ G) (U : (Opens X)ᵒᵖ) (n : ℕ) :
    Component F U n →+ Component G U n :=
  ((powMap α n).val.app U).hom.toAddMonoidHom

/-- The graded ring homomorphism `⨁ₙ Γ(U, F^{⊗ n}) →+* ⨁ₙ Γ(U, G^{⊗ n})` induced by
`α : F ⟶ G`. -/
noncomputable def ringHom (α : F ⟶ G) (U : (Opens X)ᵒᵖ) :
    (⨁ n, Component F U n) →+* ⨁ n, Component G U n :=
  DirectSum.toSemiring (fun n => (DirectSum.of (Component G U) n).comp (componentMap α U n))
    (congrArg (DirectSum.of (Component G U) 0) (powMap_oneSec α U))
    (fun a b => by
      simp only [AddMonoidHom.comp_apply, DirectSum.of_mul_of]
      exact congrArg (DirectSum.of (Component G U) _) (powMap_mul α U a b))

theorem ringHom_of (α : F ⟶ G) (U : (Opens X)ᵒᵖ) (n : ℕ) (a : Component F U n) :
    ringHom α U (DirectSum.of (Component F U) n a) =
      DirectSum.of (Component G U) n ((powMap α n).val.app U a) :=
  DirectSum.toSemiring_of _ _ _ n a

/-- **Graded ring isomorphism of section rings.** An isomorphism `α : F ≅ G` induces a ring
isomorphism `⨁ₙ Γ(U, F^{⊗ n}) ≃+* ⨁ₙ Γ(U, G^{⊗ n})` sending the degree-`n` part to the degree-`n`
part through `Γ(U, α^{⊗ n})` (`ringEquiv_of`). -/
noncomputable def ringEquiv (α : F ≅ G) (U : (Opens X)ᵒᵖ) :
    (⨁ n, Component F U n) ≃+* ⨁ n, Component G U n :=
  RingEquiv.ofRingHom (ringHom α.hom U) (ringHom α.inv U)
    (DirectSum.ringHom_ext fun n a => by
      simp only [RingHom.comp_apply, ringHom_of, RingHom.id_apply]
      congr 1
      change (powMap α.inv n ≫ powMap α.hom n).val.app U a = a
      rw [← powMap_comp, α.inv_hom_id, powMap_id]
      rfl)
    (DirectSum.ringHom_ext fun n a => by
      simp only [RingHom.comp_apply, ringHom_of, RingHom.id_apply]
      congr 1
      change (powMap α.hom n ≫ powMap α.inv n).val.app U a = a
      rw [← powMap_comp, α.hom_inv_id, powMap_id]
      rfl)

theorem ringEquiv_of (α : F ≅ G) (U : (Opens X)ᵒᵖ) (n : ℕ) (a : Component F U n) :
    ringEquiv α U (DirectSum.of (Component F U) n a) =
      DirectSum.of (Component G U) n ((powIso α n).hom.val.app U a) :=
  ringHom_of α.hom U n a

end TensorPowerSectionRing

end Hartshorne
