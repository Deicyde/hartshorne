/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.PlurigenusBirational
import Hartshorne.Surface.CanonicalSectionRing

/-!
# Pullback of pluricanonical sections preserves products

Hartshorne, *Algebraic Geometry*, V.6, birational invariance of the canonical ring (p. 421).

The comparison maps used for the birational invariance of plurigenera are the morphisms
`T^m F ⟶ f_*(T^m G)` induced by a morphism `α : F ⟶ f_* G` (`tensorPowerPushforwardMap`). This
file shows that they preserve the product of the tensor-power section rings
(`tensorPowerPushforwardMap_mul`): the product of local tensors is their concatenation
(`moduleSheafTensorPowerMul_multilinear`), and both sides are bilinear morphisms out of
sheafifications, which are determined by their values on local tensors.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace Hartshorne

open SheafAlgebraOperations

section TensorPowerMul

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (F : SheafOfModules.{u} (ringCatSheafOf R))

/-- **The product of local tensors is their concatenation:**
`(f₁ ⊗ ⋯ ⊗ fᵣ) · (g₁ ⊗ ⋯ ⊗ gₛ) = f₁ ⊗ ⋯ ⊗ fᵣ ⊗ g₁ ⊗ ⋯ ⊗ gₛ` in `T^{r+s} F`. -/
theorem moduleSheafTensorPowerMul_multilinear (r s : ℕ) (U : (Opens X)ᵒᵖ)
    (m : Fin r → F.val.obj U) (m' : Fin s → F.val.obj U) :
    (moduleSheafTensorPowerMul r F s).app U ((moduleSheafTensorPowerMultilinear r F).app U m)
        ((moduleSheafTensorPowerMultilinear s F).app U m') =
      (moduleSheafTensorPowerMultilinear (r + s) F).app U (Fin.append m m') := by
  rw [moduleSheafTensorPowerMultilinear_app, moduleSheafTensorPowerMultilinear_app,
    moduleSheafTensorPowerMultilinear_app]
  refine ((moduleSheafTensorAlgebraPresheaf_isGraded F).sheafMul_unit r s U _ _).trans ?_
  congr 1
  apply (moduleSheafTensorAlgebraPresheaf_isGraded F).injective U (r + s)
  refine ((moduleSheafTensorAlgebraPresheaf_isGraded F).ι_presheafMul r s U _ _).trans ?_
  change TensorPower.toTensorAlgebra (PiTensorProduct.tprod _ m) *
      TensorPower.toTensorAlgebra (PiTensorProduct.tprod _ m') =
    TensorPower.toTensorAlgebra (PiTensorProduct.tprod _ (Fin.append m m'))
  rw [← TensorPower.toTensorAlgebra_gMul, TensorPower.tprod_mul_tprod]

/-- Bilinear morphisms `T^r F × T^s F → H` into a sheaf agreeing on pairs of local tensors are
equal. -/
theorem tensorPower_bilinear_ext {r s : ℕ} {H : SheafOfModules.{u} (ringCatSheafOf R)}
    {γ γ' : PresheafBilinear (moduleSheafTensorPower r F).val (moduleSheafTensorPower s F).val
      H.val}
    (h : ∀ (U : (Opens X)ᵒᵖ) (m : Fin r → F.val.obj U) (m' : Fin s → F.val.obj U),
      γ.app U ((moduleSheafTensorPowerMultilinear r F).app U m)
          ((moduleSheafTensorPowerMultilinear s F).app U m') =
        γ'.app U ((moduleSheafTensorPowerMultilinear r F).app U m)
          ((moduleSheafTensorPowerMultilinear s F).app U m')) : γ = γ' := by
  apply bilinear_ext_of_unit
  intro U p q
  have key : (γ.app U).compl₁₂ ((sheafifyUnit (moduleSheafTensorPowerPresheaf r F)).app U).hom
      ((sheafifyUnit (moduleSheafTensorPowerPresheaf s F)).app U).hom =
      (γ'.app U).compl₁₂ ((sheafifyUnit (moduleSheafTensorPowerPresheaf r F)).app U).hom
        ((sheafifyUnit (moduleSheafTensorPowerPresheaf s F)).app U).hom := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
    refine PiTensorProduct.ext (MultilinearMap.ext fun m' => ?_)
    exact h U m m'
  exact LinearMap.congr_fun₂ key p q

end TensorPowerMul

section Pushforward

variable {Y V : Scheme.{u}} (f : V ⟶ Y)

/-- The pushforward of a bilinear morphism of `𝒪_V`-modules along `f : V ⟶ Y`: on an open
`U ⊆ Y` it is the bilinear map over `f⁻¹ U`, viewed as `𝒪_Y(U)`-bilinear through `f^♯`. -/
noncomputable def SheafAlgebraOperations.PresheafBilinear.pushforward {P Q N : V.Modules}
    (β : PresheafBilinear (R := V.sheaf) P.val Q.val N.val) :
    PresheafBilinear (R := Y.sheaf) ((Scheme.Modules.pushforward f).obj P).val
      ((Scheme.Modules.pushforward f).obj Q).val ((Scheme.Modules.pushforward f).obj N).val where
  app U := LinearMap.mk₂ _ (fun p q => β.app (op (f ⁻¹ᵁ U.unop)) p q)
    (fun p p' q => (β.app (op (f ⁻¹ᵁ U.unop))).map_add₂ p p' q)
    (fun c p q => (β.app (op (f ⁻¹ᵁ U.unop))).map_smul₂ (f.app U.unop c) p q)
    (fun p q q' => (β.app (op (f ⁻¹ᵁ U.unop)) p).map_add q q')
    (fun c p q => (β.app (op (f ⁻¹ᵁ U.unop)) p).map_smul (f.app U.unop c) q)
  naturality _ p q := β.naturality _ p q

theorem SheafAlgebraOperations.PresheafBilinear.pushforward_app {P Q N : V.Modules}
    (β : PresheafBilinear (R := V.sheaf) P.val Q.val N.val) (U : Y.Opensᵒᵖ)
    (p : ((Scheme.Modules.pushforward f).obj P).val.obj U)
    (q : ((Scheme.Modules.pushforward f).obj Q).val.obj U) :
    (β.pushforward f).app U p q = β.app (op (f ⁻¹ᵁ U.unop)) p q :=
  rfl

variable {F : Y.Modules} {G : V.Modules}

/-- **The comparison maps of tensor powers preserve products.** For `α : F ⟶ f_* G`, the induced
morphisms `T^m F ⟶ f_*(T^m G)` send the product of sections of `T^i F` and `T^j F` to the product
of their images. -/
theorem tensorPowerPushforwardMap_mul (α : F ⟶ (Scheme.Modules.pushforward f).obj G) (i j : ℕ)
    (U : Y.Opensᵒᵖ) (a : (moduleSheafTensorPower (R := Y.sheaf) i F).val.obj U)
    (b : (moduleSheafTensorPower (R := Y.sheaf) j F).val.obj U) :
    (tensorPowerPushforwardMap f α (i + j)).val.app U ((moduleSheafTensorPowerMul i F j).app U a b) =
      (moduleSheafTensorPowerMul i G j).app (op (f ⁻¹ᵁ U.unop))
        ((tensorPowerPushforwardMap f α i).val.app U a)
        ((tensorPowerPushforwardMap f α j).val.app U b) := by
  have h : (moduleSheafTensorPowerMul i F j).postcomp (tensorPowerPushforwardMap f α (i + j)).val =
      ((moduleSheafTensorPowerMul i G j).pushforward f).precomp
        (tensorPowerPushforwardMap f α i).val (tensorPowerPushforwardMap f α j).val := by
    refine tensorPower_bilinear_ext F fun U m m' => ?_
    change (tensorPowerPushforwardMap f α (i + j)).val.app U
        ((moduleSheafTensorPowerMul i F j).app U _ _) =
      (moduleSheafTensorPowerMul i G j).app (op (f ⁻¹ᵁ U.unop))
        ((tensorPowerPushforwardMap f α i).val.app U _)
        ((tensorPowerPushforwardMap f α j).val.app U _)
    have e1 := moduleSheafTensorPowerMul_multilinear (R := Y.sheaf) F i j U m m'
    have e2 := tensorPowerPushforwardMap_tprod f α (i + j) U (Fin.append m m')
    have e3 := tensorPowerPushforwardMap_tprod f α i U m
    have e4 := tensorPowerPushforwardMap_tprod f α j U m'
    have e5 := moduleSheafTensorPowerMul_multilinear (R := V.sheaf) G i j (op (f ⁻¹ᵁ U.unop))
      (fun k => α.val.app U (m k)) (fun k => α.val.app U (m' k))
    have e6 : (fun k => α.val.app U (Fin.append m m' k)) =
        Fin.append (fun k => α.val.app U (m k)) (fun k => α.val.app U (m' k)) := by
      funext k
      refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp only [Fin.append_left]
      · simp only [Fin.append_right]
    rw [e1, e2, e3, e4, e6]
    exact e5.symm
  exact congrArg (fun γ : PresheafBilinear _ _ _ => γ.app U a b) h

end Pushforward

section GradedRingHom

open scoped DirectSum

variable {X X' : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {R' : Sheaf (Opens.grothendieckTopology X') CommRingCat.{u}}
  (F : SheafOfModules.{u} (ringCatSheafOf R)) (U : (Opens X)ᵒᵖ)
  (F' : SheafOfModules.{u} (ringCatSheafOf R')) (U' : (Opens X')ᵒᵖ)
  (ψ : ∀ m, TensorPowerSectionRing.Component F U m →+ TensorPowerSectionRing.Component F' U' m)
  (hone : ψ 0 (TensorPowerSectionRing.oneSec F U) = TensorPowerSectionRing.oneSec F' U')
  (hmul : ∀ (i j : ℕ) (a : TensorPowerSectionRing.Component F U i)
    (b : TensorPowerSectionRing.Component F U j),
    ψ (i + j) (TensorPowerSectionRing.mul F U a b) =
      TensorPowerSectionRing.mul F' U' (ψ i a) (ψ j b))

/-- The ring homomorphism `⨁ₘ Γ(U, F^{⊗ m}) → ⨁ₘ Γ(U', F'^{⊗ m})` of section rings given by
additive maps in each degree that preserve the unit and the products. -/
noncomputable def TensorPowerSectionRing.gradedRingHom :
    (⨁ m, TensorPowerSectionRing.Component F U m) →+*
      ⨁ m, TensorPowerSectionRing.Component F' U' m :=
  DirectSum.toSemiring (fun m => (DirectSum.of _ m).comp (ψ m))
    (by
      change DirectSum.of _ 0 (ψ 0 (TensorPowerSectionRing.oneSec F U)) = 1
      rw [hone]
      rfl)
    (fun {i j} a b => by
      change DirectSum.of _ (i + j) (ψ (i + j) (TensorPowerSectionRing.mul F U a b)) = _
      rw [hmul, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, DirectSum.of_mul_of]
      rfl)

theorem TensorPowerSectionRing.gradedRingHom_of (m : ℕ)
    (x : TensorPowerSectionRing.Component F U m) :
    TensorPowerSectionRing.gradedRingHom F U F' U' ψ hone hmul (DirectSum.of _ m x) =
      DirectSum.of _ m (ψ m x) :=
  DirectSum.toSemiring_of _ _ _ m x

theorem TensorPowerSectionRing.coe_gradedRingHom :
    ⇑(TensorPowerSectionRing.gradedRingHom F U F' U' ψ hone hmul) = DirectSum.map ψ := by
  have h : (TensorPowerSectionRing.gradedRingHom F U F' U' ψ hone hmul).toAddMonoidHom =
      DirectSum.map ψ :=
    DirectSum.addHom_ext fun m x => by
      rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, gradedRingHom_of,
        DirectSum.map_of]
  exact congrArg DFunLike.coe h

theorem TensorPowerSectionRing.gradedRingHom_injective (h : ∀ m, Function.Injective (ψ m)) :
    Function.Injective (TensorPowerSectionRing.gradedRingHom F U F' U' ψ hone hmul) := by
  rw [coe_gradedRingHom]
  exact (DirectSum.map_injective ψ).2 h

theorem TensorPowerSectionRing.gradedRingHom_surjective (h : ∀ m, Function.Surjective (ψ m)) :
    Function.Surjective (TensorPowerSectionRing.gradedRingHom F U F' U' ψ hone hmul) := by
  rw [coe_gradedRingHom]
  exact (DirectSum.map_surjective ψ).2 h

end GradedRingHom

end Hartshorne
