/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ClosedImmersionIdealSheaf
import Hartshorne.Scheme.ModuleSheafTensorRestrict
import Hartshorne.Scheme.AffineGlobalSectionsExact
import Hartshorne.Scheme.Differentials.RelativeDifferentialsBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The conormal sheaf of an immersion

Hartshorne, *Algebraic Geometry*, II.8 (pp. 175–176); Stacks Project, Section 29.32.

For a closed immersion `i : Z ⟶ X` with ideal sheaf `I`, the multiplication `I ⊗ I ⟶ I`,
`a ⊗ b ↦ a b`, has cokernel `I/I²`. The unit `I ⟶ i_* i^* I` of the pullback–pushforward
adjunction kills the image of the multiplication, because the `𝒪_X`-action on `i_* i^* I` goes
through `i^♯`, which kills `I`. It therefore factors through a morphism `I/I² ⟶ i_* i^* I`.

This morphism is an isomorphism (`Hartshorne.isIso_idealSheafSqQuotientToPushforward`). On an
affine open `V = Spec A` with `B = Γ(i⁻¹ V) = A/J`, the unit `I(V) ⟶ (i^* I)(i⁻¹ V)` is
`m ↦ 1 ⊗ m ∈ B ⊗_A I(V)`. It is surjective, and its kernel `J · I(V)` is the image of `I ⊗ I` by
`(A/J) ⊗_A M ≅ M/JM`. Both sides are quasi-coherent, so bijectivity on affine sections suffices.

For an immersion `f : Z ⟶ X`, factored as the closed immersion `f.liftCoborder` into the open
subscheme `f.coborderRange` followed by its inclusion, the conormal sheaf is `N^*_f = i'^* I`,
where `i' = f.liftCoborder` and `I` is its ideal sheaf. Then `i'_* N^*_f ≅ I/I²`
(`Hartshorne.immersionConormalPushforwardIso`).
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

section Comparison

open QuasicoherentAbelianAux PullbackQuasicoherent Scheme.Modules
open scoped TensorProduct

/-- On `Spec R`, a morphism between modules of the form `M̃` is an isomorphism as soon as it is
bijective on global sections. -/
theorem isIso_of_bijective_moduleSpecΓ {R : CommRingCat.{u}} {P Q : (Spec R).Modules}
    (hP : (tilde.functor R).essImage P) (hQ : (tilde.functor R).essImage Q) (φ : P ⟶ Q)
    (hφ : Function.Bijective (moduleSpecΓFunctor.map φ)) : IsIso φ := by
  have hP' : IsIso P.fromTildeΓ := isIso_fromTildeΓ_iff.mpr hP
  have hQ' : IsIso Q.fromTildeΓ := isIso_fromTildeΓ_iff.mpr hQ
  have : IsIso (moduleSpecΓFunctor.map φ) := (ConcreteCategory.isIso_iff_bijective _).mpr hφ
  have hA : IsIso ((tilde.functor R).map (moduleSpecΓFunctor.map φ)) :=
    Functor.map_isIso (tilde.functor R) _
  have h : (tilde.functor R).map (moduleSpecΓFunctor.map φ) ≫ Q.fromTildeΓ =
      P.fromTildeΓ ≫ φ := Scheme.Modules.fromTildeΓNatTrans.naturality φ
  have hc : IsIso (P.fromTildeΓ ≫ φ) := h ▸ IsIso.comp_isIso' hA hQ'
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ P.fromTildeΓ φ hP' hc

/-- For a morphism `f : F ⟶ G` of quasi-coherent modules and an affine open `V`, the projection
`G ⟶ coker f` is surjective on sections over `V`. -/
theorem surjective_cokernel_π_app {F G : X.Modules} (f : F ⟶ G) [F.IsQuasicoherent]
    [G.IsQuasicoherent] (V : X.affineOpens) :
    haveI := V.2.isOpenImmersion_fromSpec
    Function.Surjective ((cokernel.π f).app (V.2.fromSpec ''ᵁ ⊤)) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have := isQuasicoherent_cokernel f
  have := isQuasicoherent_kernel (cokernel.π f)
  let S := ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f) (kernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
  have : (S.map (specRestrictFunctor V)).X₁.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have h := shortExact_map_moduleSpecΓ _ (shortExact_specRestrict hS V)
  exact (ModuleCat.epi_iff_surjective
    ((S.map (specRestrictFunctor V)).map moduleSpecΓFunctor).g).mp h.epi_g

/-- For a surjective ring map `ρ : A ⟶ B`, every element of `B ⊗_A M` is of the form `1 ⊗ m`. -/
theorem exists_one_tmul {A B : CommRingCat.{u}} (ρ : A ⟶ B) (hρ : Function.Surjective ρ)
    (M : ModuleCat.{u} A) (z : (ModuleCat.extendScalars ρ.hom).obj M) :
    ∃ m : M, ((1 : B) ⊗ₜ[A] m : (ModuleCat.extendScalars ρ.hom).obj M) = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul b m =>
    obtain ⟨a, rfl⟩ := hρ b
    refine ⟨a • m, ?_⟩
    let B' := (ModuleCat.restrictScalars ρ.hom).obj (ModuleCat.of B B)
    refine (TensorProduct.smul_tmul (R := A) (M := B') a (show B' from (1 : B)) m).symm.trans ?_
    have h1 : (a • (show B' from (1 : B)) : B') = (show B' from ρ a) := mul_one (ρ a)
    exact congrArg (· ⊗ₜ[A] m) h1
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    exact ⟨m + m', TensorProduct.tmul_add _ _ _⟩

/-- For a surjective ring map `ρ : A ⟶ B` with kernel `J`, if `1 ⊗ m = 0` in `B ⊗_A M` then
`m ∈ J M`. -/
theorem mem_ker_smul_top_of_one_tmul_eq_zero {A B : CommRingCat.{u}} (ρ : A ⟶ B)
    (hρ : Function.Surjective ρ) (M : ModuleCat.{u} A) (m : M)
    (h : ((1 : B) ⊗ₜ[A] m : (ModuleCat.extendScalars ρ.hom).obj M) = 0) :
    m ∈ RingHom.ker ρ.hom • (⊤ : Submodule A M) := by
  let e := RingHom.quotientKerEquivOfSurjective (f := ρ.hom) hρ
  let L : (ModuleCat.restrictScalars ρ.hom).obj (ModuleCat.of B B) ≃ₗ[A]
      A ⧸ RingHom.ker ρ.hom :=
    { toFun := fun b => e.symm b
      invFun := fun q => e q
      map_add' := fun b b' => map_add e.symm b b'
      map_smul' := fun a b => by
        change e.symm (ρ a * (show B from b)) = Ideal.Quotient.mk _ a * e.symm b
        rw [map_mul, RingHom.quotientKerEquivOfSurjective_symm_apply]
      left_inv := fun b => e.apply_symm_apply b
      right_inv := fun q => e.symm_apply_apply q }
  have hL : L (show (ModuleCat.restrictScalars ρ.hom).obj (ModuleCat.of B B) from (1 : B)) = 1 :=
    map_one e.symm
  have h3 : TensorProduct.congr L (LinearEquiv.refl A M)
      (((1 : B) ⊗ₜ[A] m : (ModuleCat.extendScalars ρ.hom).obj M)) =
      (1 : A ⧸ RingHom.ker ρ.hom) ⊗ₜ[A] m :=
    (TensorProduct.congr_tmul L (LinearEquiv.refl A M) _ m).trans (congrArg (· ⊗ₜ[A] m) hL)
  have key : TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker ρ.hom)
      (TensorProduct.congr L (LinearEquiv.refl A M)
        (((1 : B) ⊗ₜ[A] m : (ModuleCat.extendScalars ρ.hom).obj M))) =
      Submodule.Quotient.mk m := by
    rw [h3, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  rw [h, map_zero, map_zero] at key
  exact (Submodule.Quotient.mk_eq_zero _).mp key.symm

variable (i : Z ⟶ X) [IsClosedImmersion i] (V : X.affineOpens)

/-- The affine open `i⁻¹ V` of `Z`, for a closed immersion `i : Z ⟶ X` and an affine open `V`. -/
noncomputable abbrev closedImmersionAffinePreimage : Z.affineOpens :=
  ⟨i ⁻¹ᵁ (V : X.Opens), V.2.preimage i⟩

/-- The `Γ(X, V)`-module `I(V)` of sections of the ideal sheaf over an affine open `V`, read on
`Spec Γ(X, V)`. -/
noncomputable abbrev idealSectionsModule : ModuleCat.{u} Γ(X, (V : X.Opens)) :=
  (modulesSpecToSheaf.obj (specRestriction (closedImmersionIdealSheaf i) V)).presheaf.obj (op ⊤)

/-- `M̃ ≅ I|_V` for `M = I(V)`: the counit of the tilde–global sections adjunction, an
isomorphism since `I` is quasi-coherent. -/
noncomputable def idealSectionsTildeIso :
    (tilde.functor Γ(X, (V : X.Opens))).obj (idealSectionsModule i V) ≅
      specRestriction (closedImmersionIdealSheaf i) V :=
  @asIso _ _ _ _ (specRestriction (closedImmersionIdealSheaf i) V).fromTildeΓ
    (isIso_fromTildeΓ_iff.mpr ((isQuasicoherent_iff_forall_essImage _).mp
      (isQuasicoherent_closedImmersionIdealSheaf i) V))

set_option maxHeartbeats 1000000 in
/-- On the affine open `i⁻¹ V`, the pullback `i^* s` of a section `s` of the ideal sheaf `I`
over `V` is `1 ⊗ s ∈ Γ(i⁻¹ V) ⊗_{Γ(V)} I(V)`. -/
theorem closedImmersion_unit_toOpen
    (s : Γ(closedImmersionIdealSheaf i, (haveI := V.2.isOpenImmersion_fromSpec;
      V.2.fromSpec ''ᵁ ⊤)))
    (hT : haveI := V.2.isOpenImmersion_fromSpec
      haveI := (closedImmersionAffinePreimage i V).2.isOpenImmersion_fromSpec
      (closedImmersionAffinePreimage i V).2.fromSpec ''ᵁ ⊤ ≤ i ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤)) :
    haveI := V.2.isOpenImmersion_fromSpec
    (specRestrictionPullbackIso i (closedImmersionIdealSheaf i) V
        (closedImmersionAffinePreimage i V) le_rfl (idealSectionsModule i V)
        (idealSectionsTildeIso i V)).inv.app ⊤
      (((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)).presheaf.map
        (homOfLE hT).op
        (((pullbackPushforwardAdjunction i).unit.app (closedImmersionIdealSheaf i)).app
          (V.2.fromSpec ''ᵁ ⊤) s)) =
      (tilde.toOpen ((ModuleCat.extendScalars (i.appLE V (closedImmersionAffinePreimage i V)
        le_rfl).hom).obj (idealSectionsModule i V)) ⊤).hom
        ((1 : Γ(Z, (closedImmersionAffinePreimage i V : Z.Opens))) ⊗ₜ[Γ(X, (V : X.Opens))]
          (show idealSectionsModule i V from s)) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have hT' : ⊤ ≤ Spec.map (i.appLE V (closedImmersionAffinePreimage i V) le_rfl) ⁻¹ᵁ
      (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤)) := by
    intro x _
    show (Spec.map _).base x ∈ V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤)
    rw [Scheme.Hom.preimage_image_eq]
    trivial
  refine (specRestrictionPullbackIso_inv_unit _ _ _ _ _ _ _ _ _ hT hT').trans ?_
  set N := specRestriction (closedImmersionIdealSheaf i) V
  have r1 : (idealSectionsTildeIso i V).inv.app (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))
      (((restrictAdjunction V.2.fromSpec).unit.app (closedImmersionIdealSheaf i)).app
        (V.2.fromSpec ''ᵁ ⊤) s) =
      (tilde.toOpen (idealSectionsModule i V) (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))).hom s := by
    have h1 := ConcreteCategory.congr_hom
      (Scheme.Modules.toOpen_fromTildeΓ_app N (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))) s
    have h2 : ∀ y, (idealSectionsTildeIso i V).inv.app (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))
        ((idealSectionsTildeIso i V).hom.app (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤)) y) = y :=
      fun y => ConcreteCategory.congr_hom
        (congrArg (fun φ => Hom.app φ _) (idealSectionsTildeIso i V).hom_inv_id) y
    refine Eq.trans ?_ (h2 _)
    refine congrArg _ ?_
    exact h1.symm
  rw [r1]
  refine Eq.trans ?_ (Hartshorne.tildePullbackIso_hom_unit_apply _ _ _)
  refine congrArg _ ?_
  have r3 : (tilde.toOpen (idealSectionsModule i V) (V.2.fromSpec ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤))).hom s =
      ((tilde.functor _).obj (idealSectionsModule i V)).presheaf.map (homOfLE le_top).op
        ((tilde.toOpen (idealSectionsModule i V) ⊤).hom s) := rfl
  rw [r3]
  refine (congrArg _ (app_presheaf_map _ _ _)).trans ((presheaf_map_map _ _ _ (𝟙 _) _).trans ?_)
  exact (ConcreteCategory.congr_hom (CategoryTheory.Functor.map_id _ _) _).trans rfl

omit [IsClosedImmersion i] in
/-- On sections over an affine open `V`, a function `k ∈ Γ(V)` acts on `I(V)` through its
restriction. -/
theorem idealSectionsModule_smul (k : Γ(X, (V : X.Opens))) (y : idealSectionsModule i V)
    (hV : haveI := V.2.isOpenImmersion_fromSpec; V.2.fromSpec ''ᵁ ⊤ ≤ (V : X.Opens)) :
    haveI := V.2.isOpenImmersion_fromSpec
    (k • y : idealSectionsModule i V) =
      (show Γ(X, V.2.fromSpec ''ᵁ ⊤) from X.presheaf.map (homOfLE hV).op k) •
        (show Γ(closedImmersionIdealSheaf i, V.2.fromSpec ''ᵁ ⊤) from y) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have e1 : (V.2.fromSpec.appIso ⊤).hom (X.presheaf.map (homOfLE hV).op k) =
      (Scheme.ΓSpecIso Γ(X, (V : X.Opens))).inv k := by
    refine (RelDiffLocal.fromSpec_appIso_hom_res V ⊤ hV k).trans ?_
    rw [show (⊤ : (Spec Γ(X, (V : X.Opens))).Opens).leTop = 𝟙 ⊤ from Subsingleton.elim _ _,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  have e2 : (V.2.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, (V : X.Opens))).inv k) =
      X.presheaf.map (homOfLE hV).op k := by
    rw [← e1]
    exact Iso.hom_inv_id_apply _ _
  change (show Γ(X, V.2.fromSpec ''ᵁ ⊤) from (V.2.fromSpec.appIso ⊤).inv
      ((Scheme.ΓSpecIso Γ(X, (V : X.Opens))).inv k)) •
      (show Γ(closedImmersionIdealSheaf i, V.2.fromSpec ''ᵁ ⊤) from y) = _
  rw [e2]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- On an affine open `V`, the comparison `I/I² ⟶ i_* i^* I` is bijective on sections. -/
theorem bijective_idealSheafSqQuotientToPushforward_app :
    haveI := V.2.isOpenImmersion_fromSpec
    Function.Bijective ((idealSheafSqQuotientToPushforward i).app (V.2.fromSpec ''ᵁ ⊤)) := by
  have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have := isQuasicoherent_closedImmersionIdealSheaf i
  have : (idealTensor (I := closedImmersionIdealSheaf i)
      (closedImmersionIdealSheaf i)).IsQuasicoherent :=
    isQuasicoherent_moduleSheafTensor _ _
  have : IsOpenImmersion (closedImmersionAffinePreimage i V).2.fromSpec :=
    (closedImmersionAffinePreimage i V).2.isOpenImmersion_fromSpec
  have hρ : Function.Surjective (i.appLE V (closedImmersionAffinePreimage i V) le_rfl) := by
    have h := i.app_surjective (V : X.Opens) V.2
    rwa [Scheme.Hom.app_eq_appLE] at h
  have hTV : V.2.fromSpec ''ᵁ ⊤ = (V : X.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, V.2.opensRange_fromSpec]
  have hWT : (closedImmersionAffinePreimage i V).2.fromSpec ''ᵁ ⊤ =
      i ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤) := by
    rw [Scheme.Hom.image_top_eq_opensRange, (closedImmersionAffinePreimage i V).2.opensRange_fromSpec,
      hTV]
  have hT := hWT.le
  have hTW : i ⁻¹ᵁ (V.2.fromSpec ''ᵁ ⊤) ≤ (closedImmersionAffinePreimage i V : Z.Opens) :=
    fun x hx => by rw [hTV] at hx; exact hx
  -- `G` identifies sections of `i^* I` over `i⁻¹ V` with `Γ(i⁻¹ V) ⊗_{Γ(V)} I(V)`.
  let SR := specRestrictionPullbackIso i (closedImmersionIdealSheaf i) V
    (closedImmersionAffinePreimage i V) le_rfl (idealSectionsModule i V) (idealSectionsTildeIso i V)
  have hR : IsIso (homOfLE hT) := ⟨⟨homOfLE hWT.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  have hSR : Function.Bijective (SR.inv.app ⊤) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨SR.hom.app ⊤, fun y => ?_, fun y => ?_⟩
    · exact ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ ⊤) SR.inv_hom_id) y
    · exact ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ ⊤) SR.hom_inv_id) y
  have hG := hSR.comp (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)).presheaf.map (homOfLE hT).op))
  have hK := closedImmersion_unit_toOpen i V
  have htO := ConcreteCategory.bijective_of_isIso (tilde.toOpen ((ModuleCat.extendScalars
    (i.appLE V (closedImmersionAffinePreimage i V) le_rfl).hom).obj (idealSectionsModule i V)) ⊤)
  -- the unit `I(V) ⟶ (i^* I)(i⁻¹ V)` is surjective
  have hsurj : Function.Surjective (((pullbackPushforwardAdjunction i).unit.app
      (closedImmersionIdealSheaf i)).app (V.2.fromSpec ''ᵁ ⊤)) := by
    intro y
    obtain ⟨z, hz⟩ := htO.2 (SR.inv.app ⊤
      (((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)).presheaf.map
        (homOfLE hT).op y))
    obtain ⟨m, rfl⟩ := exists_one_tmul _ hρ _ z
    exact ⟨m, hG.1 ((hK m hT).trans hz)⟩
  -- its kernel is killed by `I ⟶ I/I²`
  have hker : ∀ s, ((pullbackPushforwardAdjunction i).unit.app
      (closedImmersionIdealSheaf i)).app (V.2.fromSpec ''ᵁ ⊤) s = 0 →
      (cokernel.π (idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i))).app
        (V.2.fromSpec ''ᵁ ⊤) s = 0 := by
    intro s hs
    have h1 : ((1 : Γ(Z, (closedImmersionAffinePreimage i V : Z.Opens))) ⊗ₜ[Γ(X, (V : X.Opens))]
        (show idealSectionsModule i V from s) : (ModuleCat.extendScalars
          (i.appLE V (closedImmersionAffinePreimage i V) le_rfl).hom).obj
            (idealSectionsModule i V)) = 0 := by
      refine htO.1 ((hK s hT).symm.trans ?_)
      rw [hs]
      exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    have h2 := mem_ker_smul_top_of_one_tmul_eq_zero _ hρ _ _ h1
    refine Submodule.smul_induction_on (p := fun x : idealSectionsModule i V =>
      (cokernel.π (idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i))).app
        (V.2.fromSpec ''ᵁ ⊤) x = 0) h2 (fun k hk y _ => ?_) (fun x y hx hy => ?_)
    · have hk0 : i.app (V.2.fromSpec ''ᵁ ⊤) (X.presheaf.map (homOfLE hTV.le).op k) = 0 := by
        have hmor : X.presheaf.map (homOfLE hTV.le).op ≫ i.app (V.2.fromSpec ''ᵁ ⊤) =
            i.appLE V (closedImmersionAffinePreimage i V) le_rfl ≫
              Z.presheaf.map (homOfLE hTW).op := by
          rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
        refine (ConcreteCategory.congr_hom hmor k).trans ?_
        change Z.presheaf.map (homOfLE hTW).op
          (i.appLE V (closedImmersionAffinePreimage i V) le_rfl k) = 0
        rw [RingHom.mem_ker.mp hk, map_zero]
      let S : ShortComplex X.Modules := ShortComplex.mk
        (closedImmersionIdealSheafι i) (structureSheafToPushforward i)
        (kernel.condition (structureSheafToPushforward i))
      have : Mono S.f := inferInstanceAs (Mono (closedImmersionIdealSheafι i))
      obtain ⟨a, ha⟩ := modules_sections_exact (S := S)
        (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) (U := V.2.fromSpec ''ᵁ ⊤)
        (X.presheaf.map (homOfLE hTV.le).op k) hk0
      change (cokernel.π (idealMul (closedImmersionIdealSheafι i)
        (closedImmersionIdealSheaf i))).app (V.2.fromSpec ''ᵁ ⊤)
        (k • y : idealSectionsModule i V) = 0
      rw [idealSectionsModule_smul i V k y hTV.le, ← ha]
      have hb := idealMul_bilinear (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i)
        (V.2.fromSpec ''ᵁ ⊤) a y
      refine (congrArg (fun z => (cokernel.π (idealMul (closedImmersionIdealSheafι i)
        (closedImmersionIdealSheaf i))).app (V.2.fromSpec ''ᵁ ⊤) z) hb.symm).trans ?_
      exact (ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ (V.2.fromSpec ''ᵁ ⊤))
        (cokernel.condition _)) _).trans rfl
    · refine (((cokernel.π (idealMul (closedImmersionIdealSheafι i)
        (closedImmersionIdealSheaf i))).app (V.2.fromSpec ''ᵁ ⊤)).hom.map_add x y).trans ?_
      exact (congrArg₂ (· + ·) hx hy).trans (add_zero 0)
  -- the comparison is bijective, since `π ≫ Ψ = η`
  have hπΨ : ∀ x, (idealSheafSqQuotientToPushforward i).app (V.2.fromSpec ''ᵁ ⊤)
      ((cokernel.π (idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i))).app
        (V.2.fromSpec ''ᵁ ⊤) x) =
      ((pullbackPushforwardAdjunction i).unit.app (closedImmersionIdealSheaf i)).app
        (V.2.fromSpec ''ᵁ ⊤) x := fun x =>
    ConcreteCategory.congr_hom (congrArg (fun φ => Hom.app φ (V.2.fromSpec ''ᵁ ⊤))
      (cokernel.π_desc _ _ (idealMul_comp_unit i))) x
  have hπ := surjective_cokernel_π_app
    (idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i)) V
  refine ⟨(injective_iff_map_eq_zero
    ((idealSheafSqQuotientToPushforward i).app (V.2.fromSpec ''ᵁ ⊤)).hom).mpr fun y hy => ?_,
    fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := hπ y
    exact hker x ((hπΨ x).symm.trans hy)
  · obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨_, hπΨ x⟩

/-- **`i_* i^* I ≅ I/I²` for a closed immersion** `i` with ideal sheaf `I`: the comparison
`I/I² ⟶ i_* i^* I` is an isomorphism. -/
theorem isIso_idealSheafSqQuotientToPushforward :
    IsIso (idealSheafSqQuotientToPushforward i) := by
  have := isQuasicoherent_closedImmersionIdealSheaf i
  have : (idealTensor (I := closedImmersionIdealSheaf i)
      (closedImmersionIdealSheaf i)).IsQuasicoherent :=
    isQuasicoherent_moduleSheafTensor _ _
  have : (idealSheafSqQuotient i).IsQuasicoherent := isQuasicoherent_cokernel _
  have := isQuasicoherent_pullback i (closedImmersionIdealSheaf i)
  have : ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))).IsQuasicoherent :=
    isQuasicoherent_pushforward i (Or.inr ⟨inferInstance, inferInstance⟩) _
  refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map _ fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have := hV.isOpenImmersion_fromSpec
  refine ⟨_, hV.fromSpec, inferInstance, by rw [hV.opensRange_fromSpec]; exact hxV, ?_⟩
  exact isIso_of_bijective_moduleSpecΓ
    ((isQuasicoherent_iff_forall_essImage (idealSheafSqQuotient i)).mp inferInstance ⟨V, hV⟩)
    ((isQuasicoherent_iff_forall_essImage ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)))).mp inferInstance
        ⟨V, hV⟩) _
    (bijective_idealSheafSqQuotientToPushforward_app i ⟨V, hV⟩)

end Comparison

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

/-- **The conormal sheaf of an immersion is `I/I²`**: for an immersion `f : Z ⟶ X`, factored as
the closed immersion `i' = f.liftCoborder` with ideal sheaf `I` followed by an open immersion,
`i'_* N^*_f ≅ I/I²`. -/
noncomputable def immersionConormalPushforwardIso :
    (Scheme.Modules.pushforward f.liftCoborder).obj (immersionConormalSheaf f) ≅
      idealSheafSqQuotient f.liftCoborder :=
  (@asIso _ _ _ _ (idealSheafSqQuotientToPushforward f.liftCoborder)
    (isIso_idealSheafSqQuotientToPushforward f.liftCoborder)).symm

end Immersion

end Hartshorne
