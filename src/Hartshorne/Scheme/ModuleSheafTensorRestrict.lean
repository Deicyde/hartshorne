/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SheafTensorOperations

/-!
# Tensor products of module sheaves restrict to open subschemes

For an open immersion `f : Y ⟶ X` and `𝒪_X`-modules `F`, `G`, the restriction of `F ⊗ G` to `Y`
is `F|_Y ⊗ G|_Y` (`Hartshorne.moduleSheafTensorRestrictIso`), compatibly with the universal
bilinear maps (`Hartshorne.moduleSheafTensorRestrictIso_bilinear`). The presheaves
`U ↦ F(U) ⊗ G(U)` restrict on the nose, and sheafification commutes with restriction
(`Hartshorne.SheafTensorOperations.sheafificationRestrictHom`).
-/

universe u

open scoped TensorProduct

namespace Hartshorne.SheafTensorOperations

section TensorMap

variable {A B : Type u} [CommRing A] [CommRing B]
  {M M' N N' : Type u} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
  [Module A M] [Module A M'] [Module B N] [Module B N']

/-- The `σ`-semilinear map `M ⊗[A] M' → N ⊗[B] N'` induced by `σ`-semilinear maps `M → N` and
`M' → N'`. -/
noncomputable def tensorMapₛₗ (σ : A →+* B) (g : M →ₛₗ[σ] N) (g' : M' →ₛₗ[σ] N') :
    M ⊗[A] M' →ₛₗ[σ] N ⊗[B] N' :=
  letI : Module A (N ⊗[B] N') := Module.compHom _ σ
  { toFun := TensorProduct.lift (LinearMap.mk₂ A (fun m m' => g m ⊗ₜ[B] g' m')
      (fun m₁ m₂ m' => by rw [map_add, TensorProduct.add_tmul])
      (fun a m m' => by
        rw [map_smulₛₗ, ← TensorProduct.smul_tmul']
        rfl)
      (fun m m'₁ m'₂ => by rw [map_add, TensorProduct.tmul_add])
      (fun a m m' => by
        rw [map_smulₛₗ, TensorProduct.tmul_smul]
        rfl))
    map_add' := map_add _
    map_smul' := (TensorProduct.lift _).map_smul }

@[simp]
theorem tensorMapₛₗ_tmul (σ : A →+* B) (g : M →ₛₗ[σ] N) (g' : M' →ₛₗ[σ] N') (m : M) (m' : M') :
    tensorMapₛₗ σ g g' (m ⊗ₜ m') = g m ⊗ₜ g' m' :=
  rfl

end TensorMap

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (F G : SheafOfModules.{u} (ringCatSheafOf X.sheaf))

/-- Sections over `W` of the presheaf `W ↦ F|_Y(W) ⊗ G|_Y(W)` agree with sections over `f(W)` of
the presheaf `U ↦ F(U) ⊗ G(U)`. -/
noncomputable def tensorRestrictEquiv (W : (Opens Y)ᵒᵖ) :
    (moduleSheafTensorPresheaf ((restrictModule f).obj F) ((restrictModule f).obj G)).obj W ≃ₗ[
      (ringCatSheafOf Y.sheaf).obj.obj W]
      ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafTensorPresheaf F G)).obj W where
  toFun := tensorMapₛₗ (restrictRing f W) (restrictSections f F W) (restrictSections f G W)
  map_add' := map_add _
  map_smul' :=
    (tensorMapₛₗ (restrictRing f W) (restrictSections f F W) (restrictSections f G W)).map_smulₛₗ
  invFun := tensorMapₛₗ (restrictRingInv f W) (restrictSectionsInv f F W)
    (restrictSectionsInv f G W)
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m m' => rw [tensorMapₛₗ_tmul, tensorMapₛₗ_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m m' => rw [tensorMapₛₗ_tmul, tensorMapₛₗ_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The presheaf `W ↦ F|_Y(W) ⊗ G|_Y(W)` is the restriction to `Y` of the presheaf
`U ↦ F(U) ⊗ G(U)`. -/
noncomputable def tensorPresheafRestrictIso :
    moduleSheafTensorPresheaf ((restrictModule f).obj F) ((restrictModule f).obj G) ≅
      (PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafTensorPresheaf F G) :=
  PresheafOfModules.isoMk (fun W => (tensorRestrictEquiv f F G W).toModuleIso)
    (fun W W' i => by
      ext x
      induction x using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | tmul m m' => rfl
      | add x y hx hy =>
        exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm))

end Hartshorne.SheafTensorOperations

namespace Hartshorne

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry SheafTensorOperations
  ModuleSheafBilinear

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (F G : SheafOfModules.{u} (ringCatSheafOf X.sheaf))

/-- **Tensor products restrict compatibly to open subschemes.** For an open immersion
`f : Y ⟶ X`, the restriction of `F ⊗ G` to `Y` is `F|_Y ⊗ G|_Y`. -/
noncomputable def moduleSheafTensorRestrictIso :
    (restrictModule f).obj (moduleSheafTensor F G) ≅
      moduleSheafTensor ((restrictModule f).obj F) ((restrictModule f).obj G) :=
  (asIso (sheafificationRestrictHom f (moduleSheafTensorPresheaf F G))).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).mapIso
      (tensorPresheafRestrictIso f F G).symm

/-- The isomorphism `moduleSheafTensorRestrictIso` sends `a ⊗ b`, formed from sections over
`f(W)`, to the same expression over `W`. -/
theorem moduleSheafTensorRestrictIso_bilinear (W : (Opens Y)ᵒᵖ)
    (a : F.val.obj (f.opensFunctor.op.obj W)) (b : G.val.obj (f.opensFunctor.op.obj W)) :
    (moduleSheafTensorRestrictIso f F G).hom.val.app W
        ((moduleSheafTensorBilinear F G).app (f.opensFunctor.op.obj W) a b) =
      (moduleSheafTensorBilinear ((restrictModule f).obj F) ((restrictModule f).obj G)).app W
        a b := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf Y.sheaf).obj)).unit
  let e := (tensorPresheafRestrictIso f F G).inv
  let x : (moduleSheafTensorPresheaf F G).obj (f.opensFunctor.op.obj W) := a ⊗ₜ b
  have h1 := inv_sheafificationRestrictHom_unit f (moduleSheafTensorPresheaf F G) W x
  have h2 : (η.app (moduleSheafTensorPresheaf ((restrictModule f).obj F)
        ((restrictModule f).obj G))).app W (e.app W x) =
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).map e).val.app W
        ((η.app ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj
          (moduleSheafTensorPresheaf F G))).app W x) :=
    congrArg (fun k => (k.app W).hom x) (η.naturality e)
  have h3 : e.app W x = (a ⊗ₜ b : (moduleSheafTensorPresheaf ((restrictModule f).obj F)
      ((restrictModule f).obj G)).obj W) := tensorMapₛₗ_tmul _ _ _ a b
  rw [h3] at h2
  exact (congrArg _ h1).trans h2.symm

end Hartshorne
