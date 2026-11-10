/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ClosedImmersionIdealSheaf
import Hartshorne.Scheme.ModuleSheafTensor
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The conormal sheaf of an immersion

Hartshorne, *Algebraic Geometry*, II.8 (pp. 175–176); Stacks Project, Section 29.32.

For a closed immersion `i : Z ⟶ X` with ideal sheaf `I`, the multiplication `I ⊗ I ⟶ I`,
`a ⊗ b ↦ a b`, has cokernel `I/I²`. The unit `I ⟶ i_* i^* I` of the pullback–pushforward
adjunction kills the image of the multiplication, because the `𝒪_X`-action on `i_* i^* I` goes
through `i^♯`, which kills `I`. It therefore factors through a morphism `I/I² ⟶ i_* i^* I`.

For an immersion `f : Z ⟶ X`, factored as the closed immersion `f.liftCoborder` into the open
subscheme `f.coborderRange` followed by its inclusion, the conormal sheaf is `N^*_f = i'^* I`,
where `i' = f.liftCoborder` and `I` is its ideal sheaf.
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace Hartshorne

variable {X Z : Scheme.{u}}

section Multiplication

variable {I : X.Modules} (ι : I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (M : X.Modules)

/-- For a morphism `ι : I ⟶ 𝒪_X`, the bilinear map `I × M → M`, `(a, m) ↦ ι(a) m`. -/
noncomputable def idealMulBilinear : ModuleSheafBilinear (R := X.sheaf) I M M where
  app V := LinearMap.mk₂ _
    (fun a m => (@id ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V) (ι.val.app V a)) • m)
    (fun a a' m => by simp only [id, map_add]; exact add_smul _ _ _)
    (fun c a m => by
      refine Eq.trans (congrArg
        (fun r => (@id ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V) r) • m)
        ((ι.val.app V).hom.map_smul c a)) ?_
      exact mul_smul _ _ _)
    (fun a m m' => smul_add _ _ _)
    (fun c a m => by rw [smul_smul, smul_smul, mul_comm])
  naturality {V W} j a m := by
    refine (PresheafOfModules.map_smul M.val j _ m).trans ?_
    exact congrArg (fun r => (@id (X.ringCatSheaf.obj.obj W) r) •
      (show M.val.obj W from M.val.map j m)) (PresheafOfModules.naturality_apply ι.val j a).symm

/-- The tensor product `I ⊗ M` of `𝒪_X`-modules, as an `𝒪_X`-module. -/
noncomputable abbrev idealTensor : X.Modules := moduleSheafTensor I M

/-- For a morphism `ι : I ⟶ 𝒪_X`, the multiplication `I ⊗ M ⟶ M`, `a ⊗ m ↦ ι(a) m`. -/
noncomputable def idealMul : idealTensor (I := I) M ⟶ M :=
  (moduleSheafTensorHomEquiv I M M).symm (idealMulBilinear ι M)

theorem idealMul_bilinear (V : X.Opens) (a : Γ(I, V)) (m : Γ(M, V)) :
    (idealMul ι M).app V ((moduleSheafTensorBilinear I M).app (op V) a m) =
      (show Γ(X, V) from ι.app V a) • m := by
  have h := moduleSheafTensorHomEquiv_apply (idealMul ι M)
  rw [idealMul, Equiv.apply_symm_apply] at h
  exact (congrArg (fun β => β.app (op V) a m) h).symm

end Multiplication

section ClosedImmersion

variable (i : Z ⟶ X)

/-- The quotient `I/I²` of the ideal sheaf `I` of `i : Z ⟶ X` by its square: the cokernel of the
multiplication `I ⊗ I ⟶ I`. -/
noncomputable def idealSheafSqQuotient : X.Modules :=
  cokernel (idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i))

/-- The multiplication `I ⊗ I ⟶ I` followed by the unit `I ⟶ i_* i^* I` is zero. -/
theorem idealMul_comp_unit :
    idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (closedImmersionIdealSheaf i) =
      0 := by
  have hz : ∀ (V : X.Opensᵒᵖ) (a : (closedImmersionIdealSheaf i).val.obj V),
      (structureSheafToPushforward i).val.app V ((closedImmersionIdealSheafι i).val.app V a) =
        0 := fun V a =>
    congrArg (fun φ => φ.val.app V a) (kernel.condition (structureSheafToPushforward i))
  have hμ := moduleSheafTensorHomEquiv_apply
    (idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i))
  rw [idealMul, Equiv.apply_symm_apply] at hμ
  apply (moduleSheafTensorHomEquiv _ _ _).injective
  refine (moduleSheafTensorHomEquiv_apply _).trans
    ((ModuleSheafBilinear.ext fun V a b => ?_).trans (moduleSheafTensorHomEquiv_apply _).symm)
  have e1 := congrArg (fun β => β.app V a b) hμ
  change _ = (idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i)).val.app V
    ((moduleSheafTensorBilinear _ _).app V a b) at e1
  change ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (closedImmersionIdealSheaf i)).val.app V
    ((idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i)).val.app V
      ((moduleSheafTensorBilinear _ _).app V a b)) = 0
  rw [← e1]
  refine ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (closedImmersionIdealSheaf i)).val.app V).hom.map_smul _ _).trans ?_
  change (@id (Z.ringCatSheaf.obj.obj ((TopologicalSpace.Opens.map i.base).op.obj V))
    ((structureSheafToPushforward i).val.app V ((closedImmersionIdealSheafι i).val.app V a))) •
      (_ : ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)).val.obj
        ((TopologicalSpace.Opens.map i.base).op.obj V)) = 0
  rw [hz]
  exact zero_smul _ _

/-- The comparison morphism `I/I² ⟶ i_* i^* I` induced by the unit of the pullback–pushforward
adjunction. -/
noncomputable def idealSheafSqQuotientToPushforward :
    idealSheafSqQuotient i ⟶
      (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)) :=
  cokernel.desc _ _ (idealMul_comp_unit i)

end ClosedImmersion

section Immersion

variable (f : Z ⟶ X) [IsImmersion f]

/-- The ideal sheaf `I` of the closed immersion `f.liftCoborder : Z ⟶ f.coborderRange` through
which an immersion `f` factors. -/
noncomputable abbrev immersionIdealSheaf : f.coborderRange.toScheme.Modules :=
  closedImmersionIdealSheaf f.liftCoborder

/-- **The conormal sheaf of an immersion** `f : Z ⟶ X`: `N^*_f = i'^* I`, for the closed
immersion `i' = f.liftCoborder : Z ⟶ f.coborderRange` with ideal sheaf `I`. -/
noncomputable def immersionConormalSheaf : Z.Modules :=
  (Scheme.Modules.pullback f.liftCoborder).obj (immersionIdealSheaf f)

end Immersion

end Hartshorne
