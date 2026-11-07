/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AffineTildeTensor
import Hartshorne.RingedSpace.ModuleSheafMonoidal

/-!
# Tilde is a strong monoidal functor

Hartshorne, *Algebraic Geometry*, Proposition II.5.2(b).

For a commutative ring `R`, the functor `M ↦ M̃` from `R`-modules to `𝒪_{Spec R}`-modules is
strong monoidal for the tensor product of modules and the monoidal structure on module sheaves
of `Hartshorne.Ringed.monoidalCategory`:

* the tensor comparison `tildeμIso M N : M̃ ⊗ Ñ ≅ (M ⊗_R N)~` is the inverse of the isomorphism
  `affineTildeTensorIso M N : (M ⊗_R N)~ ≅ M̃ ⊗ Ñ` (transported along the identification
  `moduleSheafTensorIsoTensor` of the two descriptions of `M̃ ⊗ Ñ`); it sends the section
  `m ⊗ n` to `m ⊗ n` (`tildeμIso_hom_app_tmulSection`);
* the unit comparison is the identification `𝒪_{Spec R} = R̃`;
* `tildeCoreMonoidal` checks naturality, associativity and unitality. Each coherence square is a
  pair of morphisms out of a tensor product of tilde sheaves; after composing with the tensor
  comparison, it becomes a pair of morphisms out of a tilde sheaf, which are determined by the
  global sections coming from the module (`tilde_tensor_hom_ext`, `tilde_tensor₃_hom_ext`).
-/

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

namespace Hartshorne

open Ringed

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

section Comparison

variable (M N : ModuleCat.{u} R)

/-- The tensor comparison `M̃ ⊗ Ñ ≅ (M ⊗_R N)~` of the tilde functor. -/
noncomputable def tildeμIso : tilde M ⊗ tilde N ≅ tilde (M ⊗ N) :=
  (moduleSheafTensorIsoTensor (tilde M) (tilde N)).symm ≪≫ (affineTildeTensorIso M N).symm

/-- The inverse of the tensor comparison sends the section `m ⊗ n` of `(M ⊗_R N)~` to the
section `m ⊗ n` of `M̃ ⊗ Ñ`. -/
theorem tildeμIso_inv_app_tmul (U : (Spec R).Opens) (m : M) (n : N) :
    (tildeμIso M N).inv.val.app (op U) ((tilde.toOpen (M ⊗ N) U).hom (m ⊗ₜ n)) =
      tmulSection (tilde M) (tilde N) ((tilde.toOpen M U).hom m) ((tilde.toOpen N U).hom n) := by
  change (moduleSheafTensorIsoTensor (tilde M) (tilde N)).hom.val.app (op U)
    ((affineTildeTensorIso M N).hom.val.app (op U) ((tilde.toOpen (M ⊗ N) U).hom (m ⊗ₜ n))) = _
  rw [affineTildeTensorIso_hom_app_tmul, moduleSheafTensorIsoTensor_hom_bilinear]

/-- The tensor comparison sends the section `m ⊗ n` of `M̃ ⊗ Ñ` to the section `m ⊗ n` of
`(M ⊗_R N)~`. -/
theorem tildeμIso_hom_app_tmulSection (U : (Spec R).Opens) (m : M) (n : N) :
    (tildeμIso M N).hom.val.app (op U)
        (tmulSection (tilde M) (tilde N) ((tilde.toOpen M U).hom m) ((tilde.toOpen N U).hom n)) =
      (tilde.toOpen (M ⊗ N) U).hom (m ⊗ₜ n) := by
  rw [← tildeμIso_inv_app_tmul]
  change ((tildeμIso M N).inv ≫ (tildeμIso M N).hom).val.app (op U) _ = _
  rw [Iso.inv_hom_id]
  rfl

end Comparison

section Ext

variable {M N P : ModuleCat.{u} R} {F : (Spec R).Modules}

/-- Morphisms out of `M̃ ⊗ Ñ` are determined by their values on the global sections `m ⊗ n`. -/
theorem tilde_tensor_hom_ext {φ ψ : tilde M ⊗ tilde N ⟶ F}
    (h : ∀ (m : M) (n : N),
      φ.val.app (op ⊤) (tmulSection (tilde M) (tilde N) ((tilde.toOpen M ⊤).hom m)
        ((tilde.toOpen N ⊤).hom n)) =
      ψ.val.app (op ⊤) (tmulSection (tilde M) (tilde N) ((tilde.toOpen M ⊤).hom m)
        ((tilde.toOpen N ⊤).hom n))) : φ = ψ := by
  rw [← cancel_epi (tildeμIso M N).inv]
  apply tildeHom_ext
  intro x
  refine TensorProduct.induction_on (R := R) (M := M) (N := N) x ?_ ?_ ?_
  · erw [map_zero, map_zero, map_zero]
  · intro m n
    change φ.val.app (op ⊤) ((tildeμIso M N).inv.val.app (op ⊤) _) =
      ψ.val.app (op ⊤) ((tildeμIso M N).inv.val.app (op ⊤) _)
    rw [tildeμIso_inv_app_tmul]
    exact h m n
  · intro x y hx hy
    erw [map_add, map_add, map_add, hx, hy]

/-- Morphisms out of `(M̃ ⊗ Ñ) ⊗ P̃` are determined by their values on the global sections
`(m ⊗ n) ⊗ p`. -/
theorem tilde_tensor₃_hom_ext {φ ψ : (tilde M ⊗ tilde N) ⊗ tilde P ⟶ F}
    (h : ∀ (m : M) (n : N) (p : P),
      φ.val.app (op ⊤) (tmulSection _ (tilde P) (tmulSection (tilde M) (tilde N)
        ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)) ((tilde.toOpen P ⊤).hom p)) =
      ψ.val.app (op ⊤) (tmulSection _ (tilde P) (tmulSection (tilde M) (tilde N)
        ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)) ((tilde.toOpen P ⊤).hom p))) :
    φ = ψ := by
  rw [← cancel_epi ((tildeμIso M N).inv ▷ tilde P)]
  apply tilde_tensor_hom_ext
  intro x p
  change φ.val.app (op ⊤) (((tildeμIso M N).inv ▷ tilde P).val.app (op ⊤) _) =
    ψ.val.app (op ⊤) (((tildeμIso M N).inv ▷ tilde P).val.app (op ⊤) _)
  rw [scheme_whiskerRight_tmulSection]
  refine TensorProduct.induction_on (R := R) (M := M) (N := N) x ?_ ?_ ?_
  · erw [map_zero, map_zero, tmulSection_zero_left, map_zero, map_zero]
  · intro m n
    rw [tildeμIso_inv_app_tmul]
    exact h m n p
  · intro x y hx hy
    erw [map_add, map_add, tmulSection_add_left, map_add, map_add, hx, hy]

end Ext

section Monoidal

/-- The unit comparison `𝒪_{Spec R} ≅ R̃` of the tilde functor (an identity). -/
noncomputable def tildeεIso : 𝟙_ (Spec R).Modules ≅ (tilde.functor R).obj (𝟙_ (ModuleCat.{u} R)) :=
  tildeSelf.symm

/-- **Tilde is strong monoidal** (Hartshorne II.5.2(b)): the tensor comparison
`M̃ ⊗ Ñ ≅ (M ⊗_R N)~` and the unit comparison `𝒪_{Spec R} ≅ R̃` satisfy the naturality,
associativity and unitality conditions. -/
noncomputable def tildeCoreMonoidal : (tilde.functor R).CoreMonoidal where
  εIso := tildeεIso
  μIso M N := tildeμIso M N
  μIso_hom_natural_left {M M'} f N := by
    apply tilde_tensor_hom_ext
    intro m n
    change (tildeμIso M' N).hom.val.app (op ⊤) ((tilde.map f ▷ tilde N).val.app (op ⊤) _) =
      (tilde.map (f ▷ N)).val.app (op ⊤) ((tildeμIso M N).hom.val.app (op ⊤) _)
    rw [scheme_whiskerRight_tmulSection, tilde_map_toOpen_apply, tildeμIso_hom_app_tmulSection,
      tildeμIso_hom_app_tmulSection, tilde_map_toOpen_apply]
    rfl
  μIso_hom_natural_right {N N'} M f := by
    apply tilde_tensor_hom_ext
    intro m n
    change (tildeμIso M N').hom.val.app (op ⊤) ((tilde M ◁ tilde.map f).val.app (op ⊤) _) =
      (tilde.map (M ◁ f)).val.app (op ⊤) ((tildeμIso M N).hom.val.app (op ⊤) _)
    rw [scheme_whiskerLeft_tmulSection, tilde_map_toOpen_apply, tildeμIso_hom_app_tmulSection,
      tildeμIso_hom_app_tmulSection, tilde_map_toOpen_apply]
    rfl
  associativity M N P := by
    apply tilde_tensor₃_hom_ext
    intro m n p
    change (tilde.map (α_ M N P).hom).val.app (op ⊤) ((tildeμIso (M ⊗ N) P).hom.val.app (op ⊤)
        (((tildeμIso M N).hom ▷ tilde P).val.app (op ⊤) _)) =
      (tildeμIso M (N ⊗ P)).hom.val.app (op ⊤) ((tilde M ◁ (tildeμIso N P).hom).val.app (op ⊤)
        ((α_ (tilde M) (tilde N) (tilde P)).hom.val.app (op ⊤) _))
    rw [scheme_whiskerRight_tmulSection, tildeμIso_hom_app_tmulSection, tildeμIso_hom_app_tmulSection,
      tilde_map_toOpen_apply, scheme_associator_hom_tmulSection, scheme_whiskerLeft_tmulSection,
      tildeμIso_hom_app_tmulSection, tildeμIso_hom_app_tmulSection]
    rfl
  left_unitality M := by
    apply tilde_tensor_hom_ext (M := 𝟙_ (ModuleCat.{u} R))
    intro r m
    change (λ_ (tilde M)).hom.val.app (op ⊤) _ =
      (tilde.map (λ_ M).hom).val.app (op ⊤) ((tildeμIso (𝟙_ (ModuleCat.{u} R)) M).hom.val.app
        (op ⊤) ((tildeεIso.hom ▷ tilde M).val.app (op ⊤) _))
    refine (leftUnitor_hom_tmulSection (tilde M) (U := op ⊤) _ _).trans ?_
    refine Eq.trans ?_ (congrArg (fun y => (tilde.map (λ_ M).hom).val.app (op ⊤)
      ((tildeμIso (𝟙_ (ModuleCat.{u} R)) M).hom.val.app (op ⊤) y))
      (scheme_whiskerRight_tmulSection tildeεIso.hom _ _)).symm
    change _ = (tilde.map (λ_ M).hom).val.app (op ⊤)
      ((tildeμIso (𝟙_ (ModuleCat.{u} R)) M).hom.val.app (op ⊤)
        (tmulSection _ _ ((tilde.toOpen (𝟙_ (ModuleCat.{u} R)) ⊤).hom r)
          ((tilde.toOpen M ⊤).hom m)))
    rw [tildeμIso_hom_app_tmulSection, tilde_map_toOpen_apply]
    exact ((tilde.toOpen M ⊤).hom.map_smul r m).symm
  right_unitality M := by
    apply tilde_tensor_hom_ext (N := 𝟙_ (ModuleCat.{u} R))
    intro m r
    change (ρ_ (tilde M)).hom.val.app (op ⊤) _ =
      (tilde.map (ρ_ M).hom).val.app (op ⊤) ((tildeμIso M (𝟙_ (ModuleCat.{u} R))).hom.val.app
        (op ⊤) ((tilde M ◁ tildeεIso.hom).val.app (op ⊤) _))
    refine (rightUnitor_hom_tmulSection (tilde M) (U := op ⊤) _ _).trans ?_
    refine Eq.trans ?_ (congrArg (fun y => (tilde.map (ρ_ M).hom).val.app (op ⊤)
      ((tildeμIso M (𝟙_ (ModuleCat.{u} R))).hom.val.app (op ⊤) y))
      (scheme_whiskerLeft_tmulSection tildeεIso.hom _ _)).symm
    change _ = (tilde.map (ρ_ M).hom).val.app (op ⊤)
      ((tildeμIso M (𝟙_ (ModuleCat.{u} R))).hom.val.app (op ⊤)
        (tmulSection _ _ ((tilde.toOpen M ⊤).hom m)
          ((tilde.toOpen (𝟙_ (ModuleCat.{u} R)) ⊤).hom r)))
    rw [tildeμIso_hom_app_tmulSection, tilde_map_toOpen_apply]
    exact ((tilde.toOpen M ⊤).hom.map_smul r m).symm

/-- **Tilde is a strong monoidal functor** from `R`-modules to `𝒪_{Spec R}`-modules. -/
noncomputable instance tildeFunctorMonoidal : (tilde.functor R).Monoidal :=
  tildeCoreMonoidal.toMonoidal

/-- The tensor comparison of the monoidal functor tilde is the inverse of the isomorphism
`(M ⊗_R N)~ ≅ M̃ ⊗ Ñ` of Hartshorne II.5.2(b). -/
theorem tilde_μ_eq (M N : ModuleCat.{u} R) :
    Functor.LaxMonoidal.μ (tilde.functor R) M N = (tildeμIso M N).hom := rfl

/-- The inverse tensor comparison of the monoidal functor tilde is the isomorphism
`(M ⊗_R N)~ ≅ M̃ ⊗ Ñ` of Hartshorne II.5.2(b), followed by the identification of the two
descriptions of `M̃ ⊗ Ñ`. -/
theorem tilde_δ_eq (M N : ModuleCat.{u} R) :
    Functor.OplaxMonoidal.δ (tilde.functor R) M N =
      (affineTildeTensorIso M N).hom ≫ (moduleSheafTensorIsoTensor (tilde M) (tilde N)).hom :=
  rfl

end Monoidal

end Hartshorne
