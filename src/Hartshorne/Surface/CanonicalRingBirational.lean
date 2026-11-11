/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.PlurigenusBirational
import Hartshorne.Surface.CanonicalSectionRing

/-!
# Birational varieties have isomorphic canonical rings

This supplements Hartshorne, *Algebraic Geometry*, V.6 (p. 421), where the Kodaira dimension
`trdeg_k R(X, K) - 1` is said to be a birational invariant: birationally equivalent nonsingular
varieties, proper over an algebraically closed field, have isomorphic canonical section rings as
graded `k`-algebras (`Hartshorne.canonicalSectionRing_ringEquiv_of_birational`), through the
isomorphism induced by restriction to dense opens and extension across codimension-two
complements (`Hartshorne.pluricanonicalSectionRing_ringEquiv_of_birational`).

## Construction

The comparison maps are those of the birational invariance of plurigenera (Exercise II.8.8).
For `f : A ⟶ B` and structure morphisms with `f ≫ q_B = q_A`, pullback of differentials gives
`T^m ⋀^n Ω_{B/k} ⟶ f_*(T^m ⋀^n Ω_{A/k})` (`Hartshorne.pluricanonicalPullback`). For a
partial isomorphism `e : X ⤏ X'` over `k` with domain of definition `V ⊆ X`, the degree-`m` map
`Γ(X', ω_{X'}^{⊗ m}) → Γ(X, ω_X^{⊗ m})` (`Hartshorne.pluricanonicalTransfer`) is pullback along
`V ⟶ X'` followed by the inverse of restriction to `V`, which is bijective because `X \ V` has
codimension at least two.

* The maps preserve products (`Hartshorne.pluricanonicalTransfer_mul`): the comparison maps
  `T^m F ⟶ f_*(T^m G)` preserve the product of tensor-power section rings
  (`Hartshorne.tensorPowerPushforwardMap_mul`), since the product of local tensors is their
  concatenation and both sides are bilinear morphisms out of sheafifications.
* On the source `U` of `e` the map is pullback along `U ≅ U' ⊆ X'`
  (`Hartshorne.pluricanonicalTransfer_source`), because pullback is compatible with composition
  (`Hartshorne.pluricanonicalPullback_comp`). Hence the map of `e⁻¹` is a left inverse
  (`Hartshorne.pluricanonicalTransfer_symm_apply`): both sides agree after pullback to the
  nonempty open `U'`, and sections of the invertible sheaf `ω_{X'}^{⊗ m}` on the integral scheme
  `X'` are determined there.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open scoped DirectSum

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

section Functoriality

variable {S A B C : Scheme.{u}}

/-- The comparison map `T^0 F ⟶ f_*(T^0 G)` sends the unit section to the unit section. -/
theorem tensorPowerPushforwardMap_oneSec (f : A ⟶ B) {F : B.Modules} {G : A.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G) (U : B.Opensᵒᵖ) :
    (tensorPowerPushforwardMap f α 0).val.app U (TensorPowerSectionRing.oneSec (R := B.sheaf) F U) =
      TensorPowerSectionRing.oneSec (R := A.sheaf) G (op (f ⁻¹ᵁ U.unop)) := by
  have e : ∀ {Z : Scheme.{u}} (H : Z.Modules) (W : Z.Opensᵒᵖ),
      TensorPowerSectionRing.oneSec (R := Z.sheaf) H W =
        (moduleSheafTensorPowerMultilinear 0 H).app W Fin.elim0 := fun H W =>
    congrArg ((sheafifyUnit (moduleSheafTensorPowerPresheaf 0 H)).app W) TensorPower.gOne_def
  rw [e F, e G, tensorPowerPushforwardMap_tprod]
  exact congrArg _ (funext fun k => k.elim0)

/-- The comparison maps of tensor powers are compatible with composition of morphisms. -/
theorem tensorPowerPushforwardMap_comp (f : A ⟶ B) (g : B ⟶ C) {F : C.Modules} {G : B.Modules}
    {H : A.Modules} (α : F ⟶ (Scheme.Modules.pushforward g).obj G)
    (β : G ⟶ (Scheme.Modules.pushforward f).obj H) (m : ℕ) :
    tensorPowerPushforwardMap (f ≫ g)
        (α ≫ (Scheme.Modules.pushforward g).map β ≫
          (Scheme.Modules.pushforwardComp f g).hom.app H) m =
      tensorPowerPushforwardMap g α m ≫
        (Scheme.Modules.pushforward g).map (tensorPowerPushforwardMap f β m) ≫
          (Scheme.Modules.pushforwardComp f g).hom.app _ := by
  apply moduleSheafTensorPower_hom_ext
  intro U x
  change (tensorPowerPushforwardMap (f ≫ g) _ m).val.app U
      ((moduleSheafTensorPowerMultilinear m F).app U x) =
    (tensorPowerPushforwardMap f β m).val.app (op (g ⁻¹ᵁ U.unop))
      ((tensorPowerPushforwardMap g α m).val.app U
        ((moduleSheafTensorPowerMultilinear m F).app U x))
  rw [tensorPowerPushforwardMap_tprod, tensorPowerPushforwardMap_tprod]
  exact (tensorPowerPushforwardMap_tprod f β m (op (g ⁻¹ᵁ U.unop)) _).symm

/-- The comparison maps of exterior powers are compatible with composition of morphisms. -/
theorem exteriorPowerPushforwardMap_comp (f : A ⟶ B) (g : B ⟶ C) {F : C.Modules}
    {G : B.Modules} {H : A.Modules} (α : F ⟶ (Scheme.Modules.pushforward g).obj G)
    (β : G ⟶ (Scheme.Modules.pushforward f).obj H) (n : ℕ) :
    exteriorPowerPushforwardMap (f ≫ g)
        (α ≫ (Scheme.Modules.pushforward g).map β ≫
          (Scheme.Modules.pushforwardComp f g).hom.app H) n =
      exteriorPowerPushforwardMap g α n ≫
        (Scheme.Modules.pushforward g).map (exteriorPowerPushforwardMap f β n) ≫
          (Scheme.Modules.pushforwardComp f g).hom.app _ := by
  apply moduleSheafExteriorPower_hom_ext
  intro U x
  change (exteriorPowerPushforwardMap (f ≫ g) _ n).val.app U
      ((moduleSheafExteriorPowerMultilinear n F).app U x) =
    (exteriorPowerPushforwardMap f β n).val.app (op (g ⁻¹ᵁ U.unop))
      ((exteriorPowerPushforwardMap g α n).val.app U
        ((moduleSheafExteriorPowerMultilinear n F).app U x))
  rw [exteriorPowerPushforwardMap_wedge, exteriorPowerPushforwardMap_wedge]
  exact (exteriorPowerPushforwardMap_wedge f β n (op (g ⁻¹ᵁ U.unop)) _).symm

/-- Pullback of relative differentials `Ω_{B/S} ⟶ f_*Ω_{A/S}`, `d b ↦ d(f^♯ b)`, along
`f : A ⟶ B`, for structure morphisms `q_A`, `q_B` with `f ≫ q_B = q_A`. -/
noncomputable def differentialsPullback (f : A ⟶ B) {qA : A ⟶ S} {qB : B ⟶ S}
    (h : f ≫ qB = qA) :
    Scheme.relativeDifferentials qB ⟶
      (Scheme.Modules.pushforward f).obj (Scheme.relativeDifferentials qA) :=
  h ▸ Scheme.relativeDifferentialsToPushforwardComp f qB

theorem differentialsPullback_d (f : A ⟶ B) {qA : A ⟶ S} {qB : B ⟶ S} (h : f ≫ qB = qA)
    (U : B.Opensᵒᵖ) (b : B.presheaf.obj U) :
    (differentialsPullback f h).val.app U ((Scheme.relativeDifferentialsDerivation qB).d b) =
      (Scheme.relativeDifferentialsDerivation qA).d (f.c.app U b) := by
  subst h
  exact Scheme.relativeDifferentialsToPushforwardComp_d f qB U b

/-- Pullback of differentials is compatible with composition. -/
theorem differentialsPullback_comp (f : A ⟶ B) (g : B ⟶ C) {qA : A ⟶ S} {qB : B ⟶ S}
    {qC : C ⟶ S} (hf : f ≫ qB = qA) (hg : g ≫ qC = qB) (hfg : (f ≫ g) ≫ qC = qA) :
    differentialsPullback (f ≫ g) hfg =
      differentialsPullback g hg ≫ (Scheme.Modules.pushforward g).map (differentialsPullback f hf) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app _ := by
  apply (Scheme.relativeDifferentialsHomEquiv qC _).injective
  rw [Scheme.relativeDifferentialsHomEquiv_apply, Scheme.relativeDifferentialsHomEquiv_apply]
  ext U b
  change (differentialsPullback (f ≫ g) hfg).val.app U
      ((Scheme.relativeDifferentialsDerivation qC).d b) =
    (differentialsPullback f hf).val.app (op (g ⁻¹ᵁ U.unop))
      ((differentialsPullback g hg).val.app U ((Scheme.relativeDifferentialsDerivation qC).d b))
  refine (differentialsPullback_d (f ≫ g) hfg U b).trans ?_
  refine Eq.trans ?_ (congrArg _ (differentialsPullback_d g hg U b)).symm
  exact (differentialsPullback_d f hf (op (g ⁻¹ᵁ U.unop)) (g.c.app U b)).symm

end Functoriality

section PluricanonicalPullback

variable {S A B C : Scheme.{u}}

/-- Pullback of pluricanonical forms `T^m ⋀^n Ω_{B/S} ⟶ f_*(T^m ⋀^n Ω_{A/S})` along
`f : A ⟶ B`, for structure morphisms `q_A`, `q_B` with `f ≫ q_B = q_A`. -/
noncomputable def pluricanonicalPullback (n m : ℕ) (f : A ⟶ B) {qA : A ⟶ S} {qB : B ⟶ S}
    (h : f ≫ qB = qA) :
    moduleSheafTensorPower (R := B.sheaf) m
        (moduleSheafExteriorPower (R := B.sheaf) n (Scheme.relativeDifferentials qB)) ⟶
      (Scheme.Modules.pushforward f).obj (moduleSheafTensorPower (R := A.sheaf) m
        (moduleSheafExteriorPower (R := A.sheaf) n (Scheme.relativeDifferentials qA))) :=
  tensorPowerPushforwardMap f (exteriorPowerPushforwardMap f (differentialsPullback f h) n) m

/-- Pullback of pluricanonical forms is compatible with composition. -/
theorem pluricanonicalPullback_comp (n m : ℕ) (f : A ⟶ B) (g : B ⟶ C) {qA : A ⟶ S}
    {qB : B ⟶ S} {qC : C ⟶ S} (hf : f ≫ qB = qA) (hg : g ≫ qC = qB)
    (hfg : (f ≫ g) ≫ qC = qA) :
    pluricanonicalPullback n m (f ≫ g) hfg =
      pluricanonicalPullback n m g hg ≫
        (Scheme.Modules.pushforward g).map (pluricanonicalPullback n m f hf) ≫
          (Scheme.Modules.pushforwardComp f g).hom.app _ := by
  unfold pluricanonicalPullback
  rw [differentialsPullback_comp f g hf hg hfg, exteriorPowerPushforwardMap_comp]
  exact tensorPowerPushforwardMap_comp f g _ _ m

/-- On global sections, pullback of pluricanonical forms along a composite `k = f ≫ g` is the
composite of the pullbacks. -/
theorem pluricanonicalPullback_app_top_comp (n m : ℕ) (f : A ⟶ B) (g : B ⟶ C) {k : A ⟶ C}
    (hk : f ≫ g = k) {qA : A ⟶ S} {qB : B ⟶ S} {qC : C ⟶ S} (hf : f ≫ qB = qA)
    (hg : g ≫ qC = qB) (hkq : k ≫ qC = qA)
    (x : (moduleSheafTensorPower (R := C.sheaf) m
      (moduleSheafExteriorPower (R := C.sheaf) n (Scheme.relativeDifferentials qC))).val.obj
        (op ⊤)) :
    (pluricanonicalPullback n m k hkq).val.app (op ⊤) x =
      (pluricanonicalPullback n m f hf).val.app (op ⊤)
        ((pluricanonicalPullback n m g hg).val.app (op ⊤) x) := by
  subst hk
  rw [pluricanonicalPullback_comp n m f g hf hg hkq]
  rfl

theorem pluricanonicalPullback_oneSec (n : ℕ) (f : A ⟶ B) {qA : A ⟶ S} {qB : B ⟶ S}
    (h : f ≫ qB = qA) (U : B.Opensᵒᵖ) :
    (pluricanonicalPullback n 0 f h).val.app U (TensorPowerSectionRing.oneSec (R := B.sheaf)
        (moduleSheafExteriorPower (R := B.sheaf) n (Scheme.relativeDifferentials qB)) U) =
      TensorPowerSectionRing.oneSec (R := A.sheaf)
        (moduleSheafExteriorPower (R := A.sheaf) n (Scheme.relativeDifferentials qA))
        (op (f ⁻¹ᵁ U.unop)) :=
  tensorPowerPushforwardMap_oneSec f _ U

theorem pluricanonicalPullback_mul (n : ℕ) (f : A ⟶ B) {qA : A ⟶ S} {qB : B ⟶ S}
    (h : f ≫ qB = qA) (i j : ℕ) (U : B.Opensᵒᵖ)
    (a : (moduleSheafTensorPower (R := B.sheaf) i
      (moduleSheafExteriorPower (R := B.sheaf) n (Scheme.relativeDifferentials qB))).val.obj U)
    (b : (moduleSheafTensorPower (R := B.sheaf) j
      (moduleSheafExteriorPower (R := B.sheaf) n (Scheme.relativeDifferentials qB))).val.obj U) :
    (pluricanonicalPullback n (i + j) f h).val.app U
        ((moduleSheafTensorPowerMul i _ j).app U a b) =
      (moduleSheafTensorPowerMul i _ j).app (op (f ⁻¹ᵁ U.unop))
        ((pluricanonicalPullback n i f h).val.app U a)
        ((pluricanonicalPullback n j f h).val.app U b) :=
  tensorPowerPushforwardMap_mul f _ i j U a b

end PluricanonicalPullback

section PluricanonicalPullbackOverField

variable {k : Type u} [Field k] {W A B : Scheme.{u}}

/-- Pullback of pluricanonical forms along `f : A ⟶ B` is injective on global sections when `B`
is integral, `T^m ⋀^n Ω_{B/k}` is invertible and `f` is an open immersion on a nonempty open. -/
theorem pluricanonicalPullback_app_top_injective [IsIntegral B] [Nonempty W] (n m : ℕ)
    (f : A ⟶ B) (j : W ⟶ A) [IsOpenImmersion (j ≫ f)] {qA : A ⟶ Spec (.of k)}
    {qB : B ⟶ Spec (.of k)} (h : f ≫ qB = qA)
    (hL : Scheme.Modules.IsInvertible (moduleSheafExteriorPower (R := B.sheaf) n
      (Scheme.relativeDifferentials qB))) :
    Function.Injective ((pluricanonicalPullback n m f h).val.app (op ⊤)) := by
  subst h
  exact injective_app_top_of_comp_eq_unit f j (isInvertible_moduleSheafTensorPower hL m) _ _
    (tensorPowerPushforwardMap_comp_restrictPushforwardMap f j _ _
      (exteriorPowerPullback_comp_openImmersionExteriorPowerMap f j qB n) m)

/-- The identity map `Γ(X, M) → Γ(X, M)` is `k`-linear for two equal structure morphisms. -/
def GlobalSectionsOver.castLinearMap {X : Scheme.{u}} {q₁ q₂ : X ⟶ Spec (.of k)} (h : q₁ = q₂)
    (M : X.Modules) : GlobalSectionsOver q₁ M →ₗ[k] GlobalSectionsOver q₂ M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by
    subst h
    rfl

end PluricanonicalPullbackOverField

section Birational

/-- The graded ring structure on `m ↦ Γ(U, F^{⊗ m})` for a module sheaf `F` on a scheme. -/
noncomputable local instance {Y : Scheme.{u}} (F : Y.Modules) (U : Y.Opensᵒᵖ) :
    DirectSum.GRing (TensorPowerSectionRing.Component (R := Y.sheaf) F U) :=
  TensorPowerSectionRing.gRing (R := Y.sheaf) F U

/-- The graded ring structure on `m ↦ Γ(U, (⋀^n M)^{⊗ m})` for a module sheaf `M` on a scheme. -/
noncomputable local instance {Y : Scheme.{u}} (n : ℕ) (M : Y.Modules) (U : Y.Opensᵒᵖ) :
    DirectSum.GRing (TensorPowerSectionRing.Component (R := Y.sheaf)
      (moduleSheafExteriorPower (R := Y.sheaf) n M) U) :=
  TensorPowerSectionRing.gRing (R := Y.sheaf) _ U

private theorem isSeparated_of_isProper {k : Type u} [Field k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of k)) [IsProper q] : Y.IsSeparated := ⟨by
  rw [show Limits.terminal.from Y = q ≫ Limits.terminal.from _ from
    Limits.terminal.hom_ext _ _]
  infer_instance⟩

variable {k : Type u} [Field k] {X X' : Scheme.{u}} (pX : X ⟶ Spec (.of k))
  (pX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsProper pX'] (e : X.PartialIso X')

/-- The birational map `X ⤏ X'` of a partial isomorphism, as a morphism on its maximal domain of
definition. -/
noncomputable def birationalDomainMap : X.PartialMap X' :=
  haveI := isSeparated_of_isProper pX'
  e.toRationalMap.toPartialMap

theorem source_le_birationalDomainMap_domain :
    e.source ≤ (birationalDomainMap pX' e).domain :=
  e.toPartialMap.le_domain_toRationalMap

theorem homOfLE_birationalDomainMap_hom :
    X.homOfLE (source_le_birationalDomainMap_domain pX' e) ≫ (birationalDomainMap pX' e).hom =
      e.iso.hom ≫ e.target.ι := by
  have := isSeparated_of_isProper pX'
  exact e.toPartialMap.toPartialMap_toRationalMap_restrict

variable {pX'} in
theorem birationalDomainMap_comp_over (he : e.IsOver pX pX') :
    (birationalDomainMap pX' e).hom ≫ pX' = (birationalDomainMap pX' e).domain.ι ≫ pX := by
  let : X.Over (Spec (.of k)) := ⟨pX⟩
  let : X'.Over (Spec (.of k)) := ⟨pX'⟩
  have := isSeparated_of_isProper pX'
  have : e.toPartialMap.IsOver (Spec (.of k)) := ⟨(Category.assoc _ _ _).trans he⟩
  have : (birationalDomainMap pX' e).IsOver (Spec (.of k)) :=
    (inferInstance : e.toRationalMap.toPartialMap.IsOver (Spec (.of k)))
  exact HomIsOver.comp_over (f := (birationalDomainMap pX' e).hom) (S := Spec (.of k))

variable [IsAlgClosed k] [IsProper pX] [IsIntegral X']

variable {pX pX'} in
/-- Restriction of pluricanonical forms of `X` to the domain `V` of the birational map is
bijective on global sections: `X \ V` has codimension at least two. -/
theorem pluricanonicalPullback_domain_bijective (hX : X.IsRegular) (he : e.IsOver pX pX')
    {n : ℕ} (hnX : topologicalKrullDim X = n) (m : ℕ) :
    Function.Bijective ((pluricanonicalPullback n m (birationalDomainMap pX' e).domain.ι
      (rfl : (birationalDomainMap pX' e).domain.ι ≫ pX = _)).val.app (op ⊤)) := by
  let : X.Over (Spec (.of k)) := ⟨pX⟩
  let : X'.Over (Spec (.of k)) := ⟨pX'⟩
  have hpX : FiniteType pX := ⟨inferInstance, inferInstance⟩
  have := isSeparated_of_isProper pX'
  let V : X.Opens := (birationalDomainMap pX' e).domain
  have hcodim : 2 ≤ codim ((V : Set X)ᶜ) :=
    (Scheme.RationalMap.codim_compl_domain_birational (k := k)
      ⟨inferInstance, (inferInstance : IsSeparated pX), (inferInstance : LocallyOfFiniteType pX),
        (inferInstance : QuasiCompact pX)⟩ hX
      ⟨inferInstance, (inferInstance : IsProper pX')⟩ e.toRationalMap ⟨e, he, rfl⟩).2
  have : IsNoetherian X := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pX
    exact {}
  have : IsNormal X := isNormal_of_isRegular hX
  have hLX := canonicalSheaf_isInvertible pX hpX hX n hnX
  rw [canonicalSheaf_eq pX hnX] at hLX
  have himg : V.ι ''ᵁ V.ι ⁻¹ᵁ ⊤ = V := Scheme.Opens.ι_image_top V
  have hρ := Scheme.Modules.bijective_presheaf_map_top_of_two_le_codim (V.ι ''ᵁ V.ι ⁻¹ᵁ ⊤)
    (by rw [himg]; exact hcodim) _ (isInvertible_moduleSheafTensorPower hLX m)
  exact bijective_app_top_of_restrict V.ι _ _
    (tensorPowerPushforwardMap_comp_restrictMap V.ι _ _
      (exteriorPowerPushforwardMap_comp_restrictMap V.ι _ _
        (relativeDifferentialsToPushforwardComp_comp_restrictMap V.ι pX) n) m)
    (restrictLeftComposite_tensorPower V.ι _ _
      (restrictLeftComposite_exteriorPower V.ι _ _
        (restrictLeftComposite_differentials V.ι pX) n) m) hρ

variable {pX pX'} in
/-- **The degree-`m` comparison map** `Γ(X', ω_{X'}^{⊗ m}) → Γ(X, ω_X^{⊗ m})` of a birational map
`X ⤏ X'` over `k`: pull back along the birational map on its domain `V ⊆ X`, then extend across
`X \ V`, which has codimension at least two. -/
noncomputable def pluricanonicalTransfer (hX : X.IsRegular) (he : e.IsOver pX pX') {n : ℕ}
    (hnX : topologicalKrullDim X = n) (m : ℕ) :
    GlobalSectionsOver pX' (moduleSheafTensorPower (R := X'.sheaf) m
        (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX'))) →ₗ[k]
      GlobalSectionsOver pX (moduleSheafTensorPower (R := X.sheaf) m
        (moduleSheafExteriorPower (R := X.sheaf) n (Scheme.relativeDifferentials pX))) :=
  (LinearEquiv.ofBijective (globalSectionsLinearMap _ pX (pluricanonicalPullback n m
      (birationalDomainMap pX' e).domain.ι
      (rfl : (birationalDomainMap pX' e).domain.ι ≫ pX = _)))
    (pluricanonicalPullback_domain_bijective e hX he hnX m)).symm.toLinearMap ∘ₗ
  GlobalSectionsOver.castLinearMap (birationalDomainMap_comp_over pX e he) _ ∘ₗ
  globalSectionsLinearMap _ pX' (pluricanonicalPullback n m (birationalDomainMap pX' e).hom
    (birationalDomainMap_comp_over pX e he))

variable {pX pX'} in
theorem pluricanonicalTransfer_spec (hX : X.IsRegular) (he : e.IsOver pX pX') {n : ℕ}
    (hnX : topologicalKrullDim X = n) (m : ℕ)
    (s : GlobalSectionsOver pX' (moduleSheafTensorPower (R := X'.sheaf) m
        (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX')))) :
    (pluricanonicalPullback n m (birationalDomainMap pX' e).domain.ι
      (rfl : (birationalDomainMap pX' e).domain.ι ≫ pX = _)).val.app (op ⊤)
        (pluricanonicalTransfer e hX he hnX m s) =
      (pluricanonicalPullback n m (birationalDomainMap pX' e).hom
        (birationalDomainMap_comp_over pX e he)).val.app (op ⊤) s :=
  (LinearEquiv.ofBijective (globalSectionsLinearMap _ pX (pluricanonicalPullback n m
      (birationalDomainMap pX' e).domain.ι
      (rfl : (birationalDomainMap pX' e).domain.ι ≫ pX = _)))
    (pluricanonicalPullback_domain_bijective e hX he hnX m)).apply_symm_apply _

variable {pX pX'} in
/-- On the source `U ⊆ X` of the partial isomorphism, the comparison map is pullback along
`U ≅ U' ⊆ X'`. -/
theorem pluricanonicalTransfer_source (hX : X.IsRegular) (he : e.IsOver pX pX') {n : ℕ}
    (hnX : topologicalKrullDim X = n) (m : ℕ)
    (s : GlobalSectionsOver pX' (moduleSheafTensorPower (R := X'.sheaf) m
        (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX')))) :
    (pluricanonicalPullback n m e.source.ι (rfl : e.source.ι ≫ pX = _)).val.app (op ⊤)
        (pluricanonicalTransfer e hX he hnX m s) =
      (pluricanonicalPullback n m (e.iso.hom ≫ e.target.ι)
        ((Category.assoc _ _ _).trans he)).val.app (op ⊤) s := by
  have hle := source_le_birationalDomainMap_domain pX' e
  have hf : X.homOfLE hle ≫ (birationalDomainMap pX' e).domain.ι ≫ pX = e.source.ι ≫ pX := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  refine (pluricanonicalPullback_app_top_comp n m (X.homOfLE hle) _ (Scheme.homOfLE_ι X hle) hf
    rfl _ _).trans ?_
  refine (congrArg _ (pluricanonicalTransfer_spec e hX he hnX m s)).trans ?_
  exact (pluricanonicalPullback_app_top_comp n m (X.homOfLE hle) _
    (homOfLE_birationalDomainMap_hom pX' e) hf (birationalDomainMap_comp_over pX e he) _ s).symm

variable {pX pX'} in
/-- The comparison map of the inverse birational map is a left inverse. -/
theorem pluricanonicalTransfer_symm_apply (hX : X.IsRegular) (hX' : X'.IsRegular)
    (he : e.IsOver pX pX') {n : ℕ} (hnX : topologicalKrullDim X = n)
    (hnX' : topologicalKrullDim X' = n) (m : ℕ)
    (s : GlobalSectionsOver pX' (moduleSheafTensorPower (R := X'.sheaf) m
        (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX')))) :
    pluricanonicalTransfer e.symm hX' he.symm hnX' m (pluricanonicalTransfer e hX he hnX m s) =
      s := by
  have hpX' : FiniteType pX' := ⟨inferInstance, inferInstance⟩
  have : Nonempty e.target := e.dense_target.nonempty.to_subtype
  have hL := canonicalSheaf_isInvertible pX' hpX' hX' n hnX'
  rw [canonicalSheaf_eq pX' hnX'] at hL
  apply pluricanonicalPullback_app_top_injective n m e.target.ι (𝟙 _)
    (rfl : e.target.ι ≫ pX' = _) hL
  refine (pluricanonicalTransfer_source e.symm hX' he.symm hnX' m _).trans ?_
  have hf : e.iso.inv ≫ e.source.ι ≫ pX = e.target.ι ≫ pX' :=
    ((Category.assoc _ _ _).symm.trans he.symm)
  refine (pluricanonicalPullback_app_top_comp n m e.iso.inv e.source.ι rfl hf rfl _ _).trans ?_
  refine (congrArg _ (pluricanonicalTransfer_source e hX he hnX m s)).trans ?_
  exact (pluricanonicalPullback_app_top_comp n m e.iso.inv (e.iso.hom ≫ e.target.ι)
    (Iso.inv_hom_id_assoc _ _) hf _ rfl s).symm

variable {pX pX'} in
/-- The comparison map preserves the unit section. -/
theorem pluricanonicalTransfer_oneSec (hX : X.IsRegular) (he : e.IsOver pX pX') {n : ℕ}
    (hnX : topologicalKrullDim X = n) :
    pluricanonicalTransfer e hX he hnX 0 (TensorPowerSectionRing.oneSec (R := X'.sheaf)
        (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX')) (op ⊤)) =
      TensorPowerSectionRing.oneSec (R := X.sheaf)
        (moduleSheafExteriorPower (R := X.sheaf) n (Scheme.relativeDifferentials pX)) (op ⊤) := by
  apply (pluricanonicalPullback_domain_bijective e hX he hnX 0).1
  refine (pluricanonicalTransfer_spec e hX he hnX 0 _).trans ?_
  exact (pluricanonicalPullback_oneSec n (birationalDomainMap pX' e).hom
    (birationalDomainMap_comp_over pX e he) (op ⊤)).trans
    (pluricanonicalPullback_oneSec n (birationalDomainMap pX' e).domain.ι
      (rfl : (birationalDomainMap pX' e).domain.ι ≫ pX = _) (op ⊤)).symm

variable {pX pX'} in
/-- **The comparison maps preserve products** of pluricanonical sections. -/
theorem pluricanonicalTransfer_mul (hX : X.IsRegular) (he : e.IsOver pX pX') {n : ℕ}
    (hnX : topologicalKrullDim X = n) (i j : ℕ)
    (a : TensorPowerSectionRing.Component (R := X'.sheaf)
      (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX')) (op ⊤) i)
    (b : TensorPowerSectionRing.Component (R := X'.sheaf)
      (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX')) (op ⊤) j) :
    pluricanonicalTransfer e hX he hnX (i + j) (TensorPowerSectionRing.mul _ _ a b) =
      TensorPowerSectionRing.mul _ _ (pluricanonicalTransfer e hX he hnX i a)
        (pluricanonicalTransfer e hX he hnX j b) := by
  apply (pluricanonicalPullback_domain_bijective e hX he hnX (i + j)).1
  refine (pluricanonicalTransfer_spec e hX he hnX (i + j) _).trans ?_
  refine (pluricanonicalPullback_mul n (birationalDomainMap pX' e).hom
    (birationalDomainMap_comp_over pX e he) i j (op ⊤) a b).trans ?_
  refine Eq.trans ?_ (pluricanonicalPullback_mul n (birationalDomainMap pX' e).domain.ι
      (rfl : (birationalDomainMap pX' e).domain.ι ≫ pX = _) i j (op ⊤) _ _).symm
  exact congrArg₂ (fun x y => (moduleSheafTensorPowerMul (R := (birationalDomainMap pX' e).domain.toScheme.sheaf) i
      (moduleSheafExteriorPower (R := (birationalDomainMap pX' e).domain.toScheme.sheaf) n
        (Scheme.relativeDifferentials ((birationalDomainMap pX' e).domain.ι ≫ pX))) j).app
      (op ⊤) x y) (pluricanonicalTransfer_spec e hX he hnX i a).symm
    (pluricanonicalTransfer_spec e hX he hnX j b).symm

variable {pX pX'} in
/-- The comparison maps in all degrees form a graded ring homomorphism
`⨁ₘ Γ(X', T^m ⋀^n Ω_{X'/k}) →+* ⨁ₘ Γ(X, T^m ⋀^n Ω_{X/k})`. -/
noncomputable def pluricanonicalTransferRingHom (hX : X.IsRegular) (he : e.IsOver pX pX')
    {n : ℕ} (hnX : topologicalKrullDim X = n) :
    (⨁ m, TensorPowerSectionRing.Component (R := X'.sheaf)
        (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX')) (op ⊤) m)
      →+* ⨁ m, TensorPowerSectionRing.Component (R := X.sheaf)
        (moduleSheafExteriorPower (R := X.sheaf) n (Scheme.relativeDifferentials pX)) (op ⊤) m :=
  TensorPowerSectionRing.gradedRingHom _ _ _ _
    (fun m => { toFun := pluricanonicalTransfer e hX he hnX m
                map_zero' := map_zero _
                map_add' := map_add _ })
    (pluricanonicalTransfer_oneSec e hX he hnX)
    (pluricanonicalTransfer_mul e hX he hnX)

variable {pX pX'} in
theorem pluricanonicalTransferRingHom_of (hX : X.IsRegular) (he : e.IsOver pX pX') {n : ℕ}
    (hnX : topologicalKrullDim X = n) (m : ℕ)
    (x : TensorPowerSectionRing.Component (R := X'.sheaf)
      (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX')) (op ⊤) m) :
    pluricanonicalTransferRingHom e hX he hnX (DirectSum.of _ m x) =
      DirectSum.of _ m (pluricanonicalTransfer e hX he hnX m x) :=
  TensorPowerSectionRing.gradedRingHom_of _ _ _ _ _ _ _ m x

variable {pX pX'} in
/-- The comparison maps of a birational map and of its inverse are inverse `k`-linear
isomorphisms `Γ(X, T^m ⋀^n Ω_{X/k}) ≃ Γ(X', T^m ⋀^n Ω_{X'/k})`. -/
noncomputable def pluricanonicalTransferEquiv (hX : X.IsRegular) (hX' : X'.IsRegular)
    (he : e.IsOver pX pX') {n : ℕ} (hnX : topologicalKrullDim X = n)
    (hnX' : topologicalKrullDim X' = n) (m : ℕ) :
    GlobalSectionsOver pX (moduleSheafTensorPower (R := X.sheaf) m
        (moduleSheafExteriorPower (R := X.sheaf) n (Scheme.relativeDifferentials pX))) ≃ₗ[k]
      GlobalSectionsOver pX' (moduleSheafTensorPower (R := X'.sheaf) m
        (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX'))) :=
  LinearEquiv.ofLinearMap (pluricanonicalTransfer e.symm hX' he.symm hnX' m)
    (pluricanonicalTransfer e hX he hnX m)
    (LinearMap.ext fun s => pluricanonicalTransfer_symm_apply e hX hX' he hnX hnX' m s)
    (LinearMap.ext fun s => pluricanonicalTransfer_symm_apply e.symm hX' hX he.symm hnX' hnX m s)

/-- **Birational nonsingular varieties have isomorphic canonical rings, through restriction and
extension.** This supplements Hartshorne, V.6 (p. 421), where the Kodaira dimension is said to be
a birational invariant. Let `X` and `X'` be nonsingular varieties of dimension `n`, proper over an
algebraically closed field `k`, and `e : X ⤏ X'` a partial isomorphism over `k`. The degree-`m`
maps `Hartshorne.pluricanonicalTransfer` of the inverse map `e⁻¹` form a ring isomorphism
`⨁ₘ Γ(X, (⋀^n Ω_{X/k})^{⊗ m}) ≃ ⨁ₘ Γ(X', (⋀^n Ω_{X'/k})^{⊗ m})`, which is the canonical ring
`R(X, K_X) ≃ R(X', K_{X'})` since `ω = ⋀^n Ω` in dimension `n`. In degree `m` the map pulls a
section of `ω_X^{⊗ m}` back along `e⁻¹ : V' ⟶ X`, where `V' ⊆ X'` is the domain of definition of
`e⁻¹` (it contains the dense open `e.target`, on which this is pullback along `e.iso`), and extends
the result across `X' \ V'`, which has codimension at least two. Each degree map is `k`-linear and bijective. Here `X`, `X'`
are integral regular schemes proper over `k`, not necessarily projective.

The ring structure on the section rings of `⋀^n Ω` is `TensorPowerSectionRing.gRing`, which this
file installs as a local instance. -/
theorem pluricanonicalSectionRing_ringEquiv_of_birational (hX : X.IsRegular)
    (hX' : X'.IsRegular) (e : X.PartialIso X') (he : e.IsOver pX pX') {n : ℕ}
    (hnX : topologicalKrullDim X = n) (hnX' : topologicalKrullDim X' = n) :
    ∃ E : (⨁ m, TensorPowerSectionRing.Component (R := X.sheaf)
          (moduleSheafExteriorPower (R := X.sheaf) n (Scheme.relativeDifferentials pX)) (op ⊤) m) ≃+*
        ⨁ m, TensorPowerSectionRing.Component (R := X'.sheaf)
          (moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX')) (op ⊤) m,
      (∀ m x, E (DirectSum.of _ m x) =
        DirectSum.of _ m (pluricanonicalTransfer e.symm hX' he.symm hnX' m x)) ∧
      ∀ m, Function.Bijective (pluricanonicalTransfer e.symm hX' he.symm hnX' m) := by
  let ψ := fun m => pluricanonicalTransferEquiv e hX hX' he hnX hnX' m
  exact ⟨RingEquiv.ofBijective (pluricanonicalTransferRingHom e.symm hX' he.symm hnX')
    ⟨TensorPowerSectionRing.gradedRingHom_injective _ _ _ _ _ _ _ fun m => (ψ m).injective,
      TensorPowerSectionRing.gradedRingHom_surjective _ _ _ _ _ _ _ fun m => (ψ m).surjective⟩,
    fun m x => (RingEquiv.ofBijective_apply _ _ _).trans
      (pluricanonicalTransferRingHom_of e.symm hX' he.symm hnX' m x),
    fun m => (ψ m).bijective⟩

/-- **Birational nonsingular varieties have isomorphic canonical rings.** This supplements
Hartshorne, V.6 (p. 421), where the Kodaira dimension is said to be a birational invariant. Let
`X` and `X'` be nonsingular varieties, proper over an algebraically closed field `k` and
birationally equivalent over `k` (a partial isomorphism `X ⤏ X'` over `k`). Then there is a ring
isomorphism `R(X, K_X) ≃ R(X', K_{X'})` of canonical section rings sending each graded piece
`H⁰(X, ω_X^{⊗ m})` to `H⁰(X', ω_{X'}^{⊗ m})` through a `k`-linear isomorphism, i.e. a graded
`k`-algebra isomorphism. That the isomorphism is induced by restriction to dense opens and
extension across codimension-two complements is
`Hartshorne.pluricanonicalSectionRing_ringEquiv_of_birational`. Here `X`, `X'` are integral
regular schemes proper over `k`, not necessarily projective. -/
theorem canonicalSectionRing_ringEquiv_of_birational (hX : X.IsRegular) (hX' : X'.IsRegular)
    (hbir : ∃ e : X.PartialIso X', e.IsOver pX pX') :
    ∃ (E : CanonicalSectionRing pX ≃+* CanonicalSectionRing pX')
      (ψ : ∀ m, GlobalSectionsOver pX (moduleSheafTensorPower (R := X.sheaf) m (canonicalSheaf pX))
        ≃ₗ[k] GlobalSectionsOver pX' (moduleSheafTensorPower (R := X'.sheaf) m (canonicalSheaf pX'))),
      ∀ m (x : CanonicalSectionRing.Component pX m),
        E (DirectSum.of _ m x) = DirectSum.of _ m (ψ m x) := by
  obtain ⟨e, he⟩ := hbir
  have hpX : FiniteType pX := ⟨inferInstance, inferInstance⟩
  have hpX' : FiniteType pX' := ⟨inferInstance, inferInstance⟩
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_nat pX hpX
  have hn' := topologicalKrullDim_eq_of_partialIso pX pX' hpX hpX' e hn
  suffices key : ∀ (F : X.Modules) (F' : X'.Modules),
      F = moduleSheafExteriorPower (R := X.sheaf) n (Scheme.relativeDifferentials pX) →
      F' = moduleSheafExteriorPower (R := X'.sheaf) n (Scheme.relativeDifferentials pX') →
      ∃ (E : (⨁ m, TensorPowerSectionRing.Component (R := X.sheaf) F (op ⊤) m) ≃+*
          ⨁ m, TensorPowerSectionRing.Component (R := X'.sheaf) F' (op ⊤) m)
        (ψ : ∀ m, GlobalSectionsOver pX (moduleSheafTensorPower (R := X.sheaf) m F) ≃ₗ[k]
          GlobalSectionsOver pX' (moduleSheafTensorPower (R := X'.sheaf) m F')),
        ∀ m (x : TensorPowerSectionRing.Component (R := X.sheaf) F (op ⊤) m),
          E (DirectSum.of _ m x) = DirectSum.of _ m (ψ m x) from
    key _ _ (canonicalSheaf_eq pX hn) (canonicalSheaf_eq pX' hn')
  rintro F F' rfl rfl
  let ψ := fun m => pluricanonicalTransferEquiv e hX hX' he hn hn' m
  refine ⟨RingEquiv.ofBijective (pluricanonicalTransferRingHom e.symm hX' he.symm hn')
    ⟨TensorPowerSectionRing.gradedRingHom_injective _ _ _ _ _ _ _ fun m => (ψ m).injective,
      TensorPowerSectionRing.gradedRingHom_surjective _ _ _ _ _ _ _ fun m => (ψ m).surjective⟩,
    ψ, fun m x => (RingEquiv.ofBijective_apply _ _ _).trans
      (pluricanonicalTransferRingHom_of e.symm hX' he.symm hn' m x)⟩

end Birational

end Hartshorne
