/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ModuleSheafTensor
import Hartshorne.Scheme.AffineTildeLocalization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Tilde commutes with tensor products

Hartshorne, *Algebraic Geometry*, Proposition II.5.2(b).

For a commutative ring `R` and `R`-modules `M`, `N`, we construct the natural isomorphism
`affineTildeTensorIso M N : (M ⊗_R N)~ ≅ M̃ ⊗_{𝒪_{Spec R}} Ñ` of `𝒪_{Spec R}`-modules, where the
right side is the sheaf tensor product `moduleSheafTensor`.

* `affineTildeTensorHom M N` is the morphism adjoint (for the tilde–global sections adjunction)
  to the `R`-linear map `M ⊗_R N → Γ(Spec R, M̃ ⊗ Ñ)`, `m ⊗ n ↦ m ⊗ n`;
  `affineTildeTensorIso_hom_app_tmul` says that on every open `U` it sends `m ⊗ n` to `m ⊗ n`.
* It is an isomorphism because it is one on stalks: at a prime `p`, the stalk map is a map
  `(M ⊗_R N)_p → M_p ⊗_{R_p} N_p` compatible with the localization maps, and both sides are
  localizations of `M ⊗_R N` at `p` (localization commutes with tensor products).
* `affineTildeTensorIso_hom_naturality` is naturality in `M` and `N`, with respect to the
  functoriality `moduleSheafTensorMap` of the sheaf tensor product.
-/

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

namespace Hartshorne

/-- If `A` is a localization of `R` at `S`, and `L`, `P₁`, `P₂` are localizations at `S` of
`M ⊗[R] N`, `M`, `N`, then an additive map `L → P₁ ⊗[A] P₂` which is `R`-linear and sends the
image of `m ⊗ n` to the tensor of the images is bijective. -/
private theorem tensor_bijective_of_isLocalizedModule {R : Type u} [CommRing R] (S : Submonoid R)
    {A : Type u} [CommRing A] [Algebra R A] [IsLocalization S A]
    {M N L P₁ P₂ : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup L] {_ : Module R L}
    [AddCommGroup P₁] {_ : Module R P₁} {_ : Module A P₁}
    [AddCommGroup P₂] {_ : Module R P₂} {_ : Module A P₂}
    (f₁ : M →ₗ[R] P₁) (f₂ : N →ₗ[R] P₂) (g : M ⊗[R] N →ₗ[R] L)
    (h : L →+ P₁ ⊗[A] P₂) (hsmul : ∀ (r : R) (x : L), h (r • x) = algebraMap R A r • h x)
    (hg : ∀ m n, h (g (m ⊗ₜ n)) = f₁ m ⊗ₜ f₂ n)
    (h₁ : ∀ (r : R) (x : P₁), r • x = algebraMap R A r • x)
    (h₂ : ∀ (r : R) (x : P₂), r • x = algebraMap R A r • x)
    (_ : IsLocalizedModule S f₁) (_ : IsLocalizedModule S f₂) (_ : IsLocalizedModule S g) :
    Function.Bijective h := by
  have : IsScalarTower R A P₁ := IsScalarTower.of_algebraMap_smul fun r x => (h₁ r x).symm
  have : IsScalarTower R A P₂ := IsScalarTower.of_algebraMap_smul fun r x => (h₂ r x).symm
  let e := IsLocalization.moduleTensorEquiv S A P₁ P₂
  let k : L →ₗ[R] P₁ ⊗[R] P₂ :=
    { toFun := fun x => e (h x)
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        rw [hsmul, map_smul, RingHom.id_apply, algebraMap_smul] }
  have hk : k = (IsLocalizedModule.linearEquiv S g (TensorProduct.map f₁ f₂)).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S g (TensorProduct.map f₁ f₂)
    apply TensorProduct.ext'
    intro m n
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, IsLocalizedModule.linearEquiv_apply,
      TensorProduct.map_tmul]
    change e (h (g (m ⊗ₜ n))) = _
    rw [hg]
    rfl
  have hb : Function.Bijective k := by
    rw [hk]; exact (IsLocalizedModule.linearEquiv S g (TensorProduct.map f₁ f₂)).bijective
  have : (h : L → P₁ ⊗[A] P₂) = e.symm ∘ k := by
    funext x; simp [k]
  rw [this]
  exact e.symm.bijective.comp hb

section StalkMap

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {F G : SheafOfModules.{u} (ringCatSheafOf R)} (φ : F ⟶ G) (x : X)

/-- The additive map on stalks induced by a morphism of module sheaves. -/
private noncomputable def sheafStalkAddMap : moduleStalk F.val x →+ moduleStalk G.val x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((SheafOfModules.toSheaf _).map φ).hom).hom

private lemma sheafStalkAddMap_germ (U : Opens X) (hU : x ∈ U) (s : F.val.obj (op U)) :
    sheafStalkAddMap φ x (ModuleSheafTensor.sectionGerm F.val x U hU s) =
      ModuleSheafTensor.sectionGerm G.val x U hU (φ.val.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hU
    ((SheafOfModules.toSheaf _).map φ).hom s

open ModuleSheafTensor in
/-- The stalk map of a morphism of module sheaves is linear over the stalk of the ring sheaf. -/
private noncomputable def sheafStalkLinearMap :
    moduleStalk F.val x →ₗ[ringSheafStalk R x] moduleStalk G.val x where
  toFun := sheafStalkAddMap φ x
  map_add' := map_add _
  map_smul' r s := by
    obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm F.val x s
    obtain ⟨W, hWU, hW, c, rfl⟩ := exists_le_ringGerm x r hU
    rw [← sectionGerm_res F.val x (homOfLE hWU) hW t, ← sectionGerm_smul, RingHom.id_apply,
      sheafStalkAddMap_germ, sheafStalkAddMap_germ, ← sectionGerm_smul]
    exact congrArg (sectionGerm G.val x W hW) ((φ.val.app (op W)).hom.map_smul c _)

end StalkMap

section TensorMap

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {F F' G G' : SheafOfModules.{u} (ringCatSheafOf R)}

/-- Functoriality of the tensor product of module sheaves: `a ⊗ b : F ⊗ G ⟶ F' ⊗ G'`. -/
noncomputable def moduleSheafTensorMap (a : F ⟶ F') (b : G ⟶ G') :
    moduleSheafTensor F G ⟶ moduleSheafTensor F' G' :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).map (a.val ⊗ₘ b.val)

/-- The map `a ⊗ b` sends `f ⊗ g` to `a f ⊗ b g`. -/
theorem moduleSheafTensorMap_bilinear (a : F ⟶ F') (b : G ⟶ G') (U : (Opens X)ᵒᵖ)
    (f : F.val.obj U) (g : G.val.obj U) :
    (moduleSheafTensorMap a b).val.app U ((moduleSheafTensorBilinear F G).app U f g) =
      (moduleSheafTensorBilinear F' G').app U (a.val.app U f) (b.val.app U g) :=
  (congrArg (fun k => (k.app U).hom (f ⊗ₜ g))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).unit.naturality
      (a.val ⊗ₘ b.val))).symm

end TensorMap

section Tilde

variable {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)

/-- `M̃ ⊗ Ñ`, viewed as an `𝒪_{Spec R}`-module. -/
private noncomputable abbrev tensorTilde : (Spec R).Modules :=
  moduleSheafTensor (tilde M) (tilde N)

set_option backward.isDefEq.respectTransparency false in
/-- The `R`-bilinear map `M × N → Γ(M̃ ⊗ Ñ)`, `(m, n) ↦ m ⊗ n` on global sections. -/
private noncomputable def tensorGlobalBilinear : M →ₗ[R] N →ₗ[R] Γ(tensorTilde M N, ⊤) :=
  LinearMap.mk₂ R
    (fun m n => (moduleSheafTensorBilinear (tilde M) (tilde N)).app (op ⊤)
      (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n))
    (fun m m' n => by
      rw [map_add, LinearMap.map_add₂])
    (fun r m n => by
      rw [map_smul]
      exact LinearMap.map_smul₂ ((moduleSheafTensorBilinear (tilde M) (tilde N)).app (op ⊤))
        ((Scheme.ΓSpecIso R).inv.hom r) _ _)
    (fun m n n' => by rw [map_add, map_add])
    (fun r m n => by
      rw [map_smul]
      exact ((moduleSheafTensorBilinear (tilde M) (tilde N)).app (op ⊤) _).map_smul
        ((Scheme.ΓSpecIso R).inv.hom r) _)

/-- The `R`-linear map `M ⊗_R N → Γ(M̃ ⊗ Ñ)`. -/
private noncomputable def tensorGlobalHom :
    M ⊗ N ⟶ moduleSpecΓFunctor.obj (tensorTilde M N) :=
  (ModuleCat.ofHom (TensorProduct.lift (tensorGlobalBilinear M N)) :
    ModuleCat.of R (M ⊗[R] N) ⟶ ModuleCat.of R Γ(tensorTilde M N, ⊤))

/-- The comparison morphism `(M ⊗_R N)~ ⟶ M̃ ⊗_{𝒪} Ñ`, adjoint to the map
`M ⊗_R N → Γ(M̃ ⊗ Ñ)`, `m ⊗ n ↦ m ⊗ n`. -/
noncomputable def affineTildeTensorHom :
    tilde (M ⊗ N) ⟶ moduleSheafTensor (tilde M) (tilde N) :=
  (tilde.adjunction.homEquiv _ _).symm (tensorGlobalHom M N)

set_option backward.isDefEq.respectTransparency false in
private lemma affineTildeTensorHom_app (U : (Spec R).Opens) (x : (M ⊗ N : ModuleCat.{u} R)) :
    (affineTildeTensorHom M N).val.app (op U) ((tilde.toOpen (M ⊗ N) U).hom x) =
      (tensorTilde M N).val.map (homOfLE le_top : U ⟶ ⊤).op ((tensorGlobalHom M N).hom x) := by
  have h1 := tilde.toOpen_map_app (tensorGlobalHom M N) U
  have h2 := Scheme.Modules.toOpen_fromTildeΓ_app (tensorTilde M N) U
  have h3 : affineTildeTensorHom M N =
      tilde.map (tensorGlobalHom M N) ≫ Scheme.Modules.fromTildeΓ (tensorTilde M N) := by
    simp [affineTildeTensorHom, Adjunction.homEquiv_counit, tilde.adjunction,
      Scheme.Modules.fromTildeΓNatTrans]
  have h4 := congrArg (fun f => f.hom x) h1
  have h5 := congrArg (fun f => f.hom ((tensorGlobalHom M N).hom x)) h2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h4 h5
  rw [h3]
  exact (congrArg (fun y => ((Scheme.Modules.fromTildeΓ (tensorTilde M N)).val.app (op U)).hom y)
    h4).trans h5

set_option backward.isDefEq.respectTransparency false in
/-- On sections over any open `U`, the comparison morphism sends the section `m ⊗ n` of
`(M ⊗_R N)~` to `m ⊗ n`. -/
theorem affineTildeTensorHom_app_tmul (U : (Spec R).Opens) (m : M) (n : N) :
    (affineTildeTensorHom M N).val.app (op U) ((tilde.toOpen (M ⊗ N) U).hom (m ⊗ₜ n)) =
      (moduleSheafTensorBilinear (tilde M) (tilde N)).app (op U)
        ((tilde.toOpen M U).hom m) ((tilde.toOpen N U).hom n) := by
  rw [affineTildeTensorHom_app]
  exact (moduleSheafTensorBilinear (tilde M) (tilde N)).naturality (homOfLE le_top : U ⟶ ⊤).op _ _

set_option backward.isDefEq.respectTransparency false in
private lemma affineTildeTensorHom_app_top (x : (M ⊗ N : ModuleCat.{u} R)) :
    (affineTildeTensorHom M N).val.app (op ⊤) ((tilde.toOpen (M ⊗ N) ⊤).hom x) =
      (tensorGlobalHom M N).hom x :=
  (affineTildeTensorHom_app M N ⊤ x).trans
    (ConcreteCategory.congr_hom ((tensorTilde M N).val.map_id _) _)

set_option backward.isDefEq.respectTransparency false in
private lemma affineTildeTensorHom_stalk_bijective (p : PrimeSpectrum.Top R) :
    Function.Bijective (sheafStalkAddMap (R := (Spec R).sheaf) (affineTildeTensorHom M N) p) := by
  let _ : Algebra R (ringSheafStalk (Spec R).sheaf p) :=
    (inferInstance : Algebra R ((structurePresheafInCommRingCat R).stalk p))
  have _ : IsLocalization.AtPrime (ringSheafStalk (Spec R).sheaf p) p.asIdeal :=
    (inferInstance : IsLocalization.AtPrime ((structurePresheafInCommRingCat R).stalk p) p.asIdeal)
  have hloc : IsLocalizedModule p.asIdeal.primeCompl (tilde.toStalk (M ⊗ N) p).hom := inferInstance
  let e := moduleSheafTensorStalkIso (tilde M) (tilde N) p
  let σ := sheafStalkAddMap (R := (Spec R).sheaf) (affineTildeTensorHom M N) p
  have hb := tensor_bijective_of_isLocalizedModule p.asIdeal.primeCompl
    (A := ringSheafStalk (Spec R).sheaf p)
    (tilde.toStalk M p).hom (tilde.toStalk N p).hom (tilde.toStalk (M ⊗ N) p).hom
    (e.toAddMonoidHom.comp σ) ?_ ?_
    (fun _ _ => rfl) (fun _ _ => rfl) inferInstance inferInstance hloc
  · have h : (σ : _ → _) = e.symm ∘ (e.toAddMonoidHom.comp σ) :=
      funext fun x => (e.symm_apply_apply _).symm
    rw [h]
    exact e.symm.bijective.comp hb
  · intro r x
    exact (congrArg e ((sheafStalkLinearMap (R := (Spec R).sheaf) (affineTildeTensorHom M N)
      p).map_smul (algebraMap R (ringSheafStalk (Spec R).sheaf p) r) x)).trans (e.map_smul _ _)
  · intro m n
    change e (σ (ModuleSheafTensor.sectionGerm (tilde (M ⊗ N)).val p ⊤ trivial
        ((tilde.toOpen (M ⊗ N) ⊤).hom (m ⊗ₜ n)))) = _
    rw [sheafStalkAddMap_germ]
    refine (congrArg
      (fun y => e (ModuleSheafTensor.sectionGerm (tensorTilde M N).val p ⊤ trivial y))
      (affineTildeTensorHom_app_top M N (m ⊗ₜ n))).trans ?_
    exact moduleSheafTensorStalkIso_germ (tilde M) (tilde N) p ⊤ trivial _ _

/-- The comparison morphism is an isomorphism, since it is one on every stalk. -/
instance : IsIso (affineTildeTensorHom M N) := by
  have : IsIso ((SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).map
      (affineTildeTensorHom M N)) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).2
    intro p
    rw [ConcreteCategory.isIso_iff_bijective]
    exact affineTildeTensorHom_stalk_bijective M N p
  have hr : (SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).ReflectsIsomorphisms :=
    inferInstance
  exact hr.reflects (affineTildeTensorHom M N)

/-- **Hartshorne II.5.2(b).** For `R`-modules `M` and `N`, the natural isomorphism
`(M ⊗_R N)~ ≅ M̃ ⊗_{𝒪_{Spec R}} Ñ`. -/
noncomputable def affineTildeTensorIso :
    tilde (M ⊗ N) ≅ moduleSheafTensor (tilde M) (tilde N) :=
  asIso (affineTildeTensorHom M N)

/-- On sections over any open `U`, the isomorphism `(M ⊗_R N)~ ≅ M̃ ⊗ Ñ` sends the section
`m ⊗ n` to `m ⊗ n`. -/
theorem affineTildeTensorIso_hom_app_tmul (U : (Spec R).Opens) (m : M) (n : N) :
    (affineTildeTensorIso M N).hom.val.app (op U) ((tilde.toOpen (M ⊗ N) U).hom (m ⊗ₜ n)) =
      (moduleSheafTensorBilinear (tilde M) (tilde N)).app (op U)
        ((tilde.toOpen M U).hom m) ((tilde.toOpen N U).hom n) :=
  affineTildeTensorHom_app_tmul M N U m n

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms out of `P̃` agree if they agree on the global sections coming from `P`. -/
private lemma tildeHom_ext {P : ModuleCat.{u} R} {F : (Spec R).Modules} {f f' : tilde P ⟶ F}
    (h : ∀ x : P, f.val.app (op ⊤) ((tilde.toOpen P ⊤).hom x) =
      f'.val.app (op ⊤) ((tilde.toOpen P ⊤).hom x)) : f = f' := by
  apply (tilde.adjunction.homEquiv P F).injective
  ext x
  simp only [Adjunction.homEquiv_unit]
  exact h x

set_option backward.isDefEq.respectTransparency false in
private lemma tilde_map_toOpen_apply {P Q : ModuleCat.{u} R} (k : P ⟶ Q) (U : (Spec R).Opens)
    (x : P) :
    (tilde.map k).val.app (op U) ((tilde.toOpen P U).hom x) = (tilde.toOpen Q U).hom (k.hom x) :=
  congrArg (fun l => l.hom x) (tilde.toOpen_map_app k U)

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality** of `(M ⊗_R N)~ ≅ M̃ ⊗ Ñ` in `M` and `N`. -/
theorem affineTildeTensorIso_hom_naturality {M M' N N' : ModuleCat.{u} R} (f : M ⟶ M')
    (g : N ⟶ N') :
    tilde.map (f ⊗ₘ g) ≫ (affineTildeTensorIso M' N').hom =
      (affineTildeTensorIso M N).hom ≫ moduleSheafTensorMap (tilde.map f) (tilde.map g) := by
  apply tildeHom_ext
  intro x
  refine TensorProduct.induction_on (R := R) (M := M) (N := N) x ?_ ?_ ?_
  · simp only [map_zero]
  · intro m n
    have h1 := tilde_map_toOpen_apply (f ⊗ₘ g) ⊤ (m ⊗ₜ n)
    have h2 := affineTildeTensorIso_hom_app_tmul M' N' ⊤ (f.hom m) (g.hom n)
    have h3 := affineTildeTensorIso_hom_app_tmul M N ⊤ m n
    have h4 := moduleSheafTensorMap_bilinear (tilde.map f) (tilde.map g) (op ⊤)
      ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)
    refine ((congrArg ((affineTildeTensorIso M' N').hom.val.app (op ⊤)).hom h1).trans h2).trans ?_
    refine Eq.trans ?_ (congrArg ((moduleSheafTensorMap (tilde.map f) (tilde.map g)).val.app
      (op ⊤)).hom h3).symm
    exact (h4.trans (congrArg₂ (fun a b => (moduleSheafTensorBilinear (tilde M') (tilde N')).app
      (op ⊤) a b) (tilde_map_toOpen_apply f ⊤ m) (tilde_map_toOpen_apply g ⊤ n))).symm
  · intro x y hx hy
    simp only [map_add, hx, hy]

end Tilde

end Hartshorne
