/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Hartshorne.Scheme.SheafTensorOperations

/-!
# Sheafifying presheaves of algebras

Let `(X, 𝒪_X)` be a ringed space (a topological space `X` with a sheaf `R` of commutative rings),
with `𝒪_X`-modules `SheafOfModules (ringCatSheafOf R)` as in `Hartshorne.Scheme.ModuleSheafTensor`.

A *presheaf of `𝒪_X`-algebras* structure on a presheaf of `𝒪_X`-modules `P`
(`PresheafAlgebra P`) is a family of associative unital `𝒪_X(U)`-bilinear multiplications on the
`P(U)`, compatible with restriction; on a sheaf of `𝒪_X`-modules `A` this is a sheaf of
`𝒪_X`-algebras structure (`ModuleSheafAlgebra A`).

The main construction is `PresheafAlgebra.sheafify`: the sheafification of a presheaf of
`𝒪_X`-algebras is a sheaf of `𝒪_X`-algebras, the multiplication being the unique bilinear
extension of the presheaf multiplication (`PresheafAlgebra.sheafify_mul_unit`). It rests on

* `sheafifyBilinearEquiv`: bilinear maps out of a pair of presheaves into a sheaf extend uniquely
  to their sheafifications (the sheafification of `P ⊗ Q` agrees with that of `aP ⊗ aQ`), proved
  by comparing stalks with `ModuleSheafTensor.presheafTensorStalkIso`;
* `exists_unit_eq_map`: every section of a sheafification is locally the image of a section of the
  presheaf.

For a graded presheaf of algebras (`PresheafAlgebra.IsGraded`: `P(U)` is the direct sum of
the images of `C r (U)`, and the product of elements of degrees `r` and `s` has degree `r + s`), the
sheafification is the direct sum of the sheafifications of the components
(`PresheafAlgebra.IsGraded.isColimit`), and multiplication maps the components in degrees `r` and
`s` to the component in degree `r + s` (`PresheafAlgebra.IsGraded.sheafify_mul_ι`).
-/

universe u

open CategoryTheory MonoidalCategory TopologicalSpace Opposite Limits
open scoped TensorProduct

namespace Hartshorne

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

namespace SheafAlgebraOperations

open ModuleSheafTensor

section Sheafify

/-- The sheafification of a presheaf of `𝒪_X`-modules. -/
noncomputable abbrev sheafify (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    SheafOfModules.{u} (ringCatSheafOf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).obj P

/-- The canonical map from a presheaf of `𝒪_X`-modules to its sheafification. -/
noncomputable abbrev sheafifyUnit
    (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ (sheafify P).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).unit.app P

/-- The morphism of sheafifications induced by a morphism of presheaves of `𝒪_X`-modules. -/
noncomputable abbrev sheafifyMap
    {P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} (f : P ⟶ Q) :
    sheafify P ⟶ sheafify Q :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).map f

variable {P Q M N M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)}

lemma sheafifyMap_unit (f : P ⟶ Q) (U : (Opens X)ᵒᵖ) (p : P.obj U) :
    (sheafifyMap f).val.app U ((sheafifyUnit P).app U p) = (sheafifyUnit Q).app U (f.app U p) :=
  (congrArg (fun φ => (PresheafOfModules.Hom.app φ U).hom p)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).unit.naturality
      f)).symm

/-- The map on stalks induced by a morphism of presheaves of `𝒪_X`-modules. -/
noncomputable def stalkMap (f : M ⟶ N) (x : X) : moduleStalk M x →+ moduleStalk N x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map f)).hom

lemma stalkMap_germ (f : M ⟶ N) (x : X) (U : Opens X) (hU : x ∈ U) (m : M.obj (op U)) :
    stalkMap f x (sectionGerm M x U hU m) = sectionGerm N x U hU (f.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hU
    ((PresheafOfModules.toPresheaf _).map f) m

lemma stalkMap_smul (f : M ⟶ N) (x : X) (r : ringSheafStalk R x) (s : moduleStalk M x) :
    stalkMap f x (r • s) = r • stalkMap f x s := by
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm M x s
  obtain ⟨W, hWU, hW, c, rfl⟩ := exists_le_ringGerm x r hU
  rw [← sectionGerm_res M x (homOfLE hWU) hW t, ← sectionGerm_smul, stalkMap_germ, stalkMap_germ,
    ← sectionGerm_smul]
  exact congrArg (sectionGerm N x W hW) ((f.app (op W)).hom.map_smul c _)

/-- The stalk map of a morphism of presheaves of modules, as an `𝒪_{X,x}`-linear map. -/
noncomputable def stalkMapₗ (f : M ⟶ N) (x : X) :
    moduleStalk M x →ₗ[ringSheafStalk R x] moduleStalk N x where
  toFun := stalkMap f x
  map_add' := map_add _
  map_smul' := stalkMap_smul f x

lemma stalkMap_sheafifyUnit_bijective (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (x : X) : Function.Bijective (stalkMap (sheafifyUnit P) x) := by
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P.presheaf
  exact ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))

lemma presheafTensorStalkIso_stalkMap (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂) (x : X)
    (s : moduleStalk (M₁ ⊗ M₂) x) :
    presheafTensorStalkIso N₁ N₂ x (stalkMap (f ⊗ₘ g) x s) =
      TensorProduct.map (stalkMapₗ f x) (stalkMapₗ g x) (presheafTensorStalkIso M₁ M₂ x s) := by
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm (M₁ ⊗ M₂) x s
  rw [stalkMap_germ]
  refine (presheafTensorStalkToTensor_germ N₁ N₂ x U hU _).trans ?_
  refine Eq.trans ?_ (congrArg _ (presheafTensorStalkToTensor_germ M₁ M₂ x U hU t).symm)
  change M₁.obj (op U) ⊗[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] M₂.obj (op U) at t
  change tensorStalkComponent N₁ N₂ x U hU
    (TensorProduct.map (f.app (op U)).hom (g.app (op U)).hom t) = _
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [TensorProduct.map_tmul, tensorStalkComponent_tmul, tensorStalkComponent_tmul,
      TensorProduct.map_tmul]
    exact congrArg₂ (· ⊗ₜ ·) (stalkMap_germ f x U hU a).symm (stalkMap_germ g x U hU b).symm
  | add a b ha hb => simp only [map_add, ha, hb]

lemma stalkMap_tensorHom_bijective (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂) (x : X)
    (hf : Function.Bijective (stalkMap f x)) (hg : Function.Bijective (stalkMap g x)) :
    Function.Bijective (stalkMap (f ⊗ₘ g) x) := by
  let e := TensorProduct.congr (LinearEquiv.ofBijective (stalkMapₗ f x) hf)
    (LinearEquiv.ofBijective (stalkMapₗ g x) hg)
  have h : ⇑(stalkMap (f ⊗ₘ g) x) =
      (presheafTensorStalkIso N₁ N₂ x).symm ∘ e ∘ presheafTensorStalkIso M₁ M₂ x := by
    funext s
    simp only [Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply, presheafTensorStalkIso_stalkMap]
    rfl
  rw [h]
  exact (presheafTensorStalkIso N₁ N₂ x).symm.bijective.comp
    (e.bijective.comp (presheafTensorStalkIso M₁ M₂ x).bijective)

/-- A morphism of presheaves of modules inducing bijections on all stalks becomes an isomorphism
after sheafification. -/
lemma isIso_sheafifyMap (f : M ⟶ N) (hf : ∀ x, Function.Bijective (stalkMap f x)) :
    IsIso (sheafifyMap f) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (ringCatSheafOf R))]
  let φ := (PresheafOfModules.toPresheaf _).map f
  change IsIso ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map φ)
  have hx : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map φ).hom) := by
    intro x
    have h1 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X) ((PresheafOfModules.toPresheaf _).obj M))) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} M.presheaf
    have h2 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X) ((PresheafOfModules.toPresheaf _).obj N))) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} N.presheaf
    have h3 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ) := by
      have : IsIso ((forget AddCommGrpCat.{u}).map
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ)) :=
        (isIso_iff_bijective _).2 (hf x)
      exact isIso_of_reflects_iso _ (forget AddCommGrpCat.{u})
    have h := congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify_naturality (Opens.grothendieckTopology X) φ)
    rw [Functor.map_comp, Functor.map_comp] at h
    have h4 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (toSheafify (Opens.grothendieckTopology X) ((PresheafOfModules.toPresheaf _).obj N))) :=
      inferInstance
    rw [h] at h4
    exact IsIso.of_isIso_comp_left
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X) ((PresheafOfModules.toPresheaf _).obj M))) _
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

/-- Precomposition with a morphism of presheaves whose sheafification is an isomorphism is a
bijection on morphisms into a sheaf. -/
noncomputable def precompEquiv (f : M ⟶ N) [IsIso (sheafifyMap f)]
    (H : SheafOfModules.{u} (ringCatSheafOf R)) :
    (N ⟶ (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).obj H) ≃
      (M ⟶ (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).obj H) where
  toFun φ := f ≫ φ
  invFun ψ :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).homEquiv N H
      (inv (sheafifyMap f) ≫
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).homEquiv M H).symm
          ψ)
  left_inv φ := by
    simp only
    rw [Adjunction.homEquiv_naturality_left_symm, IsIso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  right_inv ψ := by
    simp only
    rw [← Adjunction.homEquiv_naturality_left, IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply]

/-- Every section of a sheafification is locally the image of a section of the presheaf. -/
lemma exists_unit_eq_map (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    {U : Opens X} (s : (sheafify P).val.obj (op U)) {x : X} (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U) (p : P.obj (op V)),
      (sheafifyUnit P).app (op V) p = (sheafify P).val.map i.op s := by
  obtain ⟨t, ht⟩ := (stalkMap_sheafifyUnit_bijective P x).2 (sectionGerm _ x U hx s)
  obtain ⟨V₁, hV₁, p, rfl⟩ := exists_sectionGerm P x t
  rw [stalkMap_germ] at ht
  obtain ⟨W, hW, iV, iU, e⟩ := TopCat.Presheaf.germ_eq (sheafify P).val.presheaf x hV₁ hx _ _ ht
  refine ⟨W, hW, iU, P.map iV.op p, ?_⟩
  rw [PresheafOfModules.naturality_apply]
  exact e

/-- Sections of a sheaf of modules which agree locally are equal. -/
lemma sheaf_section_ext (H : SheafOfModules.{u} (ringCatSheafOf R)) {U : Opens X}
    (s t : H.val.obj (op U))
    (h : ∀ x ∈ U, ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U), H.val.map i.op s = H.val.map i.op t) :
    s = t :=
  TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf _).obj H) U s t fun x hx => by
    obtain ⟨V, hV, i, e⟩ := h x hx
    exact (TopCat.Presheaf.germ_res_apply H.val.presheaf i x hV s).symm.trans
      ((congrArg _ e).trans (TopCat.Presheaf.germ_res_apply H.val.presheaf i x hV t))

/-- Restricting a local preimage further. -/
lemma map_eq_unit_of_le (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    {U V W : Opens X} {s : (sheafify P).val.obj (op U)} {i : V ⟶ U} {p : P.obj (op V)}
    (e : (sheafifyUnit P).app (op V) p = (sheafify P).val.map i.op s) (j : W ⟶ V) (k : W ⟶ U) :
    ∃ p' : P.obj (op W), (sheafify P).val.map k.op s = (sheafifyUnit P).app (op W) p' := by
  refine ⟨P.map j.op p, ?_⟩
  rw [PresheafOfModules.naturality_apply, e, ← PresheafOfModules.map_comp_apply]
  exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) s

end Sheafify

section Bilinear

/-- A bilinear morphism `P × Q → N` of presheaves of `𝒪_X`-modules: for every open `U`, an
`𝒪_X(U)`-bilinear map `P(U) × Q(U) → N(U)`, compatible with restriction. -/
structure PresheafBilinear (P Q N : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) where
  /-- The bilinear map on sections over `U`. -/
  app (U : (Opens X)ᵒᵖ) :
    P.obj U →ₗ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U]
      Q.obj U →ₗ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U] N.obj U
  /-- Compatibility with restriction. -/
  naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (p : P.obj U) (q : Q.obj U) :
    N.map i (app U p q) = app V (P.map i p) (Q.map i q)

namespace PresheafBilinear

variable {P Q N N' P' Q' : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)}

@[ext]
lemma ext {β γ : PresheafBilinear P Q N} (h : ∀ U p q, β.app U p q = γ.app U p q) : β = γ := by
  cases β; cases γ
  congr
  funext U
  exact LinearMap.ext₂ (h U)

/-- Composition of a bilinear morphism with a morphism of the target. -/
noncomputable def postcomp (β : PresheafBilinear P Q N) (φ : N ⟶ N') : PresheafBilinear P Q N' where
  app U := (β.app U).compr₂ (φ.app U).hom
  naturality i p q :=
    (PresheafOfModules.naturality_apply φ i _).symm.trans (congrArg _ (β.naturality i p q))

@[simp]
lemma postcomp_app (β : PresheafBilinear P Q N) (φ : N ⟶ N') (U : (Opens X)ᵒᵖ) (p : P.obj U)
    (q : Q.obj U) : (β.postcomp φ).app U p q = φ.app U (β.app U p q) := rfl

/-- Composition of a bilinear morphism with morphisms of the sources. -/
noncomputable def precomp (β : PresheafBilinear P Q N) (f : P' ⟶ P) (g : Q' ⟶ Q) :
    PresheafBilinear P' Q' N where
  app U := (β.app U).compl₁₂ (f.app U).hom (g.app U).hom
  naturality i p q :=
    (β.naturality i _ _).trans (congrArg₂ (fun a b => β.app _ a b)
      (PresheafOfModules.naturality_apply f i p).symm (PresheafOfModules.naturality_apply g i q).symm)

@[simp]
lemma precomp_app (β : PresheafBilinear P Q N) (f : P' ⟶ P) (g : Q' ⟶ Q) (U : (Opens X)ᵒᵖ)
    (p : P'.obj U) (q : Q'.obj U) : (β.precomp f g).app U p q = β.app U (f.app U p) (g.app U q) :=
  rfl

variable (P Q N) in
/-- Morphisms out of the presheaf tensor product are the bilinear morphisms. -/
noncomputable def homEquiv : (P ⊗ Q ⟶ N) ≃ PresheafBilinear P Q N where
  toFun ψ :=
    { app U := LinearMap.mk₂ _ (fun p q => (ψ.app U).hom (p ⊗ₜ q))
        (fun p p' q => (congrArg (ψ.app U).hom (TensorProduct.add_tmul p p' q)).trans
          (map_add _ _ _))
        (fun r p q => (congrArg (ψ.app U).hom (TensorProduct.smul_tmul' r p q).symm).trans
          (map_smul _ _ _))
        (fun p q q' => (congrArg (ψ.app U).hom (TensorProduct.tmul_add p q q')).trans
          (map_add _ _ _))
        (fun r p q => (congrArg (ψ.app U).hom (TensorProduct.tmul_smul r p q)).trans
          (map_smul _ _ _))
      naturality i p q := by
        have h := congrArg (fun k => k.hom (p ⊗ₜ q)) (ψ.naturality i)
        exact h.symm }
  invFun β :=
    { app U := ModuleCat.ofHom (TensorProduct.lift (β.app U))
      naturality i := by
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro p q
        exact (β.naturality i p q).symm }
  left_inv ψ := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p q
    rfl
  right_inv β := by
    ext U p q
    rfl

lemma homEquiv_symm_tmul (β : PresheafBilinear P Q N) (U : (Opens X)ᵒᵖ) (p : P.obj U)
    (q : Q.obj U) : ((homEquiv P Q N).symm β).app U (p ⊗ₜ q) = β.app U p q := rfl

end PresheafBilinear

variable {P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)}

instance isIso_sheafifyMap_tensorHom_unit :
    IsIso (sheafifyMap (sheafifyUnit P ⊗ₘ sheafifyUnit Q)) :=
  isIso_sheafifyMap _ fun x => stalkMap_tensorHom_bijective _ _ x
    (stalkMap_sheafifyUnit_bijective P x) (stalkMap_sheafifyUnit_bijective Q x)

variable (P Q) in
/-- **Bilinear maps extend uniquely to sheafifications.** Bilinear morphisms
`aP × aQ → H` into a sheaf `H` correspond to bilinear morphisms `P × Q → H`, by restriction
along the units `P → aP`, `Q → aQ`. -/
noncomputable def sheafifyBilinearEquiv (H : SheafOfModules.{u} (ringCatSheafOf R)) :
    PresheafBilinear (sheafify P).val (sheafify Q).val H.val ≃ PresheafBilinear P Q H.val :=
  ((PresheafBilinear.homEquiv _ _ _).symm.trans
    (precompEquiv (sheafifyUnit P ⊗ₘ sheafifyUnit Q) H)).trans (PresheafBilinear.homEquiv _ _ _)

lemma sheafifyBilinearEquiv_apply {H : SheafOfModules.{u} (ringCatSheafOf R)}
    (γ : PresheafBilinear (sheafify P).val (sheafify Q).val H.val) :
    sheafifyBilinearEquiv P Q H γ = γ.precomp (sheafifyUnit P) (sheafifyUnit Q) := by
  ext U p q
  rfl

/-- The bilinear extension to sheafifications of a bilinear morphism into a sheaf. -/
noncomputable def extendBilinear {H : SheafOfModules.{u} (ringCatSheafOf R)}
    (β : PresheafBilinear P Q H.val) : PresheafBilinear (sheafify P).val (sheafify Q).val H.val :=
  (sheafifyBilinearEquiv P Q H).symm β

@[simp]
lemma extendBilinear_unit {H : SheafOfModules.{u} (ringCatSheafOf R)}
    (β : PresheafBilinear P Q H.val) (U : (Opens X)ᵒᵖ) (p : P.obj U) (q : Q.obj U) :
    (extendBilinear β).app U ((sheafifyUnit P).app U p) ((sheafifyUnit Q).app U q) =
      β.app U p q := by
  have h := sheafifyBilinearEquiv_apply (extendBilinear β)
  rw [extendBilinear, Equiv.apply_symm_apply] at h
  exact (congrArg (fun γ : PresheafBilinear P Q H.val => γ.app U p q) h).symm

lemma bilinear_ext_of_unit {H : SheafOfModules.{u} (ringCatSheafOf R)}
    {γ γ' : PresheafBilinear (sheafify P).val (sheafify Q).val H.val}
    (h : ∀ U p q, γ.app U ((sheafifyUnit P).app U p) ((sheafifyUnit Q).app U q) =
      γ'.app U ((sheafifyUnit P).app U p) ((sheafifyUnit Q).app U q)) : γ = γ' := by
  apply (sheafifyBilinearEquiv P Q H).injective
  rw [sheafifyBilinearEquiv_apply, sheafifyBilinearEquiv_apply]
  ext U p q
  exact h U p q

end Bilinear

section Algebra

/-- A **presheaf of `𝒪_X`-algebras** structure on a presheaf of `𝒪_X`-modules `P`: for every open
`U` an associative, unital, `𝒪_X(U)`-bilinear multiplication on `P(U)`, such that the restriction
maps preserve products and units. (Bilinearity over the commutative ring `𝒪_X(U)` makes `P(U)` an
`𝒪_X(U)`-algebra, not necessarily commutative.) -/
structure PresheafAlgebra (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) where
  /-- The multiplication. -/
  mul : PresheafBilinear P P P
  /-- The unit sections. -/
  one (U : (Opens X)ᵒᵖ) : P.obj U
  map_one {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : P.map i (one U) = one V
  mul_assoc (U : (Opens X)ᵒᵖ) (a b c : P.obj U) :
    mul.app U (mul.app U a b) c = mul.app U a (mul.app U b c)
  one_mul (U : (Opens X)ᵒᵖ) (a : P.obj U) : mul.app U (one U) a = a
  mul_one (U : (Opens X)ᵒᵖ) (a : P.obj U) : mul.app U a (one U) = a

namespace PresheafAlgebra

variable {P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} (S : PresheafAlgebra P)

/-- The multiplication of the sheafification: the bilinear extension of the multiplication. -/
noncomputable def sheafMul : PresheafBilinear (sheafify P).val (sheafify P).val (sheafify P).val :=
  extendBilinear (S.mul.postcomp (sheafifyUnit P))

lemma sheafMul_unit (U : (Opens X)ᵒᵖ) (a b : P.obj U) :
    S.sheafMul.app U ((sheafifyUnit P).app U a) ((sheafifyUnit P).app U b) =
      (sheafifyUnit P).app U (S.mul.app U a b) :=
  extendBilinear_unit _ U a b

lemma sheafMul_assoc (U : (Opens X)ᵒᵖ) (a b c : (sheafify P).val.obj U) :
    S.sheafMul.app U (S.sheafMul.app U a b) c = S.sheafMul.app U a (S.sheafMul.app U b c) := by
  obtain ⟨U⟩ := U
  apply sheaf_section_ext (sheafify P)
  intro x hx
  obtain ⟨V₁, h₁, i₁, p₁, e₁⟩ := exists_unit_eq_map P a hx
  obtain ⟨V₂, h₂, i₂, p₂, e₂⟩ := exists_unit_eq_map P b hx
  obtain ⟨V₃, h₃, i₃, p₃, e₃⟩ := exists_unit_eq_map P c hx
  let W := V₁ ⊓ V₂ ⊓ V₃
  have hW : x ∈ W := ⟨⟨h₁, h₂⟩, h₃⟩
  let k : W ⟶ U := homOfLE (inf_le_left.trans inf_le_left) ≫ i₁
  refine ⟨W, hW, k, ?_⟩
  obtain ⟨q₁, ha⟩ := map_eq_unit_of_le P e₁ (homOfLE (inf_le_left.trans inf_le_left)) k
  obtain ⟨q₂, hb⟩ := map_eq_unit_of_le P e₂ (homOfLE (inf_le_left.trans inf_le_right)) k
  obtain ⟨q₃, hc⟩ := map_eq_unit_of_le P e₃ (homOfLE inf_le_right) k
  rw [S.sheafMul.naturality, S.sheafMul.naturality, S.sheafMul.naturality, S.sheafMul.naturality,
    ha, hb, hc, S.sheafMul_unit, S.sheafMul_unit, S.sheafMul_unit, S.sheafMul_unit, S.mul_assoc]

lemma sheafMul_one_mul (U : (Opens X)ᵒᵖ) (a : (sheafify P).val.obj U) :
    S.sheafMul.app U ((sheafifyUnit P).app U (S.one U)) a = a := by
  obtain ⟨U⟩ := U
  apply sheaf_section_ext (sheafify P)
  intro x hx
  obtain ⟨V, hV, i, p, e⟩ := exists_unit_eq_map P a hx
  refine ⟨V, hV, i, ?_⟩
  rw [S.sheafMul.naturality, ← e, ← PresheafOfModules.naturality_apply, S.map_one, S.sheafMul_unit,
    S.one_mul]

lemma sheafMul_mul_one (U : (Opens X)ᵒᵖ) (a : (sheafify P).val.obj U) :
    S.sheafMul.app U a ((sheafifyUnit P).app U (S.one U)) = a := by
  obtain ⟨U⟩ := U
  apply sheaf_section_ext (sheafify P)
  intro x hx
  obtain ⟨V, hV, i, p, e⟩ := exists_unit_eq_map P a hx
  refine ⟨V, hV, i, ?_⟩
  rw [S.sheafMul.naturality, ← e, ← PresheafOfModules.naturality_apply, S.map_one, S.sheafMul_unit,
    S.mul_one]

/-- **Sheafification of a presheaf of algebras.** The sheafification of a presheaf of
`𝒪_X`-algebras is a sheaf of `𝒪_X`-algebras: its multiplication is the unique bilinear extension of
the multiplication of the presheaf (`sheafification_mul_unit`) and its unit is the image of the unit
of the presheaf. -/
noncomputable def sheafification : PresheafAlgebra (sheafify P).val where
  mul := S.sheafMul
  one U := (sheafifyUnit P).app U (S.one U)
  map_one i := by
    rw [← PresheafOfModules.naturality_apply, S.map_one]
  mul_assoc := S.sheafMul_assoc
  one_mul := S.sheafMul_one_mul
  mul_one := S.sheafMul_mul_one

/-- The canonical map to the sheafification is multiplicative. -/
lemma sheafification_mul_unit (U : (Opens X)ᵒᵖ) (a b : P.obj U) :
    S.sheafification.mul.app U ((sheafifyUnit P).app U a) ((sheafifyUnit P).app U b) =
      (sheafifyUnit P).app U (S.mul.app U a b) :=
  S.sheafMul_unit U a b

/-- The canonical map to the sheafification is unital. -/
lemma sheafification_one (U : (Opens X)ᵒᵖ) :
    S.sheafification.one U = (sheafifyUnit P).app U (S.one U) := rfl

/-- The multiplication of the sheafification is the only bilinear morphism extending the
multiplication of the presheaf. -/
lemma sheafification_mul_unique
    (μ : PresheafBilinear (sheafify P).val (sheafify P).val (sheafify P).val)
    (hμ : ∀ U a b, μ.app U ((sheafifyUnit P).app U a) ((sheafifyUnit P).app U b) =
      (sheafifyUnit P).app U (S.mul.app U a b)) :
    μ = S.sheafification.mul :=
  bilinear_ext_of_unit fun U a b => (hμ U a b).trans (S.sheafification_mul_unit U a b).symm

end PresheafAlgebra

end Algebra

section Graded

/-- A cofan of modules is a coproduct if the induced map from the direct sum is bijective. -/
noncomputable def isColimitCofanMkOfBijective {A : Type u} [Ring A] {Z : ℕ → ModuleCat.{u} A}
    {M : ModuleCat.{u} A} (f : ∀ r, Z r ⟶ M)
    (h : Function.Bijective (DirectSum.toModule A ℕ M (fun r => (f r).hom))) :
    IsColimit (Cofan.mk M f) :=
  IsColimit.ofIsoColimit (ModuleCat.coproductCoconeIsColimit Z)
    (Cofan.ext (LinearEquiv.ofBijective _ h).toModuleIso (fun r => by
      ext x
      exact DirectSum.toModule_lof (M := fun r => Z r) (N := M) (φ := fun r => (f r).hom) A r x))

variable {P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)}

/-- A grading of a presheaf of `𝒪_X`-algebras by subpresheaves `C r → P` (`r : ℕ`): on every
open, `P(U)` is the direct sum of the `C r (U)`, and the product of elements of degrees `r` and `s`
has degree `r + s`. -/
structure PresheafAlgebra.IsGraded (S : PresheafAlgebra P)
    (C : ℕ → PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) (ι : ∀ r, C r ⟶ P) :
    Prop where
  bijective (U : (Opens X)ᵒᵖ) :
    Function.Bijective (DirectSum.toModule _ ℕ (P.obj U) (fun r => ((ι r).app U).hom))
  mul_mem (U : (Opens X)ᵒᵖ) (r s : ℕ) (a : (C r).obj U) (b : (C s).obj U) :
    S.mul.app U ((ι r).app U a) ((ι s).app U b) ∈ LinearMap.range ((ι (r + s)).app U).hom

namespace PresheafAlgebra.IsGraded

variable {S : PresheafAlgebra P}
  {C : ℕ → PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} {ι : ∀ r, C r ⟶ P}
  (hS : S.IsGraded C ι)
include hS

lemma injective (U : (Opens X)ᵒᵖ) (r : ℕ) : Function.Injective ((ι r).app U).hom := by
  intro a b h
  apply DirectSum.of_injective (β := fun r => (C r).obj U) r
  apply (hS.bijective U).1
  rw [← DirectSum.lof_eq_of (R := (R.obj ⋙ forget₂ CommRingCat RingCat).obj U),
    ← DirectSum.lof_eq_of (R := (R.obj ⋙ forget₂ CommRingCat RingCat).obj U),
    DirectSum.toModule_lof, DirectSum.toModule_lof]
  exact h

/-- The multiplication `C r (U) × C s (U) → C (r + s) (U)` of homogeneous elements. -/
noncomputable def presheafMulApp (r s : ℕ) (U : (Opens X)ᵒᵖ) :
    (C r).obj U →ₗ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U]
      (C s).obj U →ₗ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U] (C (r + s)).obj U :=
  LinearMap.codRestrict₂ ((S.mul.app U).compl₁₂ ((ι r).app U).hom ((ι s).app U).hom)
    ((ι (r + s)).app U).hom (hS.injective U (r + s)) (hS.mul_mem U r s)

lemma ι_presheafMulApp (r s : ℕ) (U : (Opens X)ᵒᵖ) (a : (C r).obj U) (b : (C s).obj U) :
    (ι (r + s)).app U (hS.presheafMulApp r s U a b) =
      S.mul.app U ((ι r).app U a) ((ι s).app U b) :=
  LinearMap.codRestrict₂_apply _ _ _ _ a b

/-- The multiplication `C r × C s → C (r + s)` of homogeneous elements. -/
noncomputable def presheafMul (r s : ℕ) : PresheafBilinear (C r) (C s) (C (r + s)) where
  app U := hS.presheafMulApp r s U
  naturality {U V} i a b := hS.injective V (r + s)
    ((PresheafOfModules.naturality_apply (ι (r + s)) i _).trans
      ((congrArg (P.map i) (hS.ι_presheafMulApp r s U a b)).trans
        ((S.mul.naturality i _ _).trans
          ((congrArg₂ (fun a b => S.mul.app V a b) (PresheafOfModules.naturality_apply (ι r) i a).symm
            (PresheafOfModules.naturality_apply (ι s) i b).symm).trans
            (hS.ι_presheafMulApp r s V _ _).symm))))

lemma ι_presheafMul (r s : ℕ) (U : (Opens X)ᵒᵖ) (a : (C r).obj U) (b : (C s).obj U) :
    (ι (r + s)).app U ((hS.presheafMul r s).app U a b) =
      S.mul.app U ((ι r).app U a) ((ι s).app U b) :=
  hS.ι_presheafMulApp r s U a b

/-- The multiplication `a(C r) × a(C s) → a(C (r + s))` of the sheafified components. -/
noncomputable def sheafMul (r s : ℕ) :
    PresheafBilinear (sheafify (C r)).val (sheafify (C s)).val (sheafify (C (r + s))).val :=
  extendBilinear ((hS.presheafMul r s).postcomp (sheafifyUnit (C (r + s))))

lemma sheafMul_unit (r s : ℕ) (U : (Opens X)ᵒᵖ) (a : (C r).obj U) (b : (C s).obj U) :
    (hS.sheafMul r s).app U ((sheafifyUnit (C r)).app U a) ((sheafifyUnit (C s)).app U b) =
      (sheafifyUnit (C (r + s))).app U ((hS.presheafMul r s).app U a b) :=
  extendBilinear_unit _ U a b

/-- In the sheafification, the product of sections of the components of degrees `r` and `s` lies in
the component of degree `r + s`. -/
theorem sheafification_mul_ι (r s : ℕ) (U : (Opens X)ᵒᵖ) (a : (sheafify (C r)).val.obj U)
    (b : (sheafify (C s)).val.obj U) :
    S.sheafification.mul.app U ((sheafifyMap (ι r)).val.app U a) ((sheafifyMap (ι s)).val.app U b) =
      (sheafifyMap (ι (r + s))).val.app U ((hS.sheafMul r s).app U a b) := by
  have h : S.sheafification.mul.precomp (sheafifyMap (ι r)).val (sheafifyMap (ι s)).val =
      (hS.sheafMul r s).postcomp (sheafifyMap (ι (r + s))).val := by
    apply bilinear_ext_of_unit
    intro U p q
    rw [PresheafBilinear.precomp_app, PresheafBilinear.postcomp_app, sheafifyMap_unit,
      sheafifyMap_unit, sheafification_mul_unit, sheafMul_unit, sheafifyMap_unit, ι_presheafMul]
  exact congrArg (fun γ : PresheafBilinear _ _ _ => γ.app U a b) h

/-- The presheaf of algebras is the direct sum of its components. -/
noncomputable def isColimitPresheaf : IsColimit (Cofan.mk P ι) :=
  PresheafOfModules.evaluationJointlyReflectsColimits _ _ fun U =>
    (isColimitMapCoconeCofanMkEquiv (PresheafOfModules.evaluation _ U) _ _).symm
      (isColimitCofanMkOfBijective _ (hS.bijective U))

/-- **The sheafification is the direct sum of the sheafified components.** -/
noncomputable def isColimit :
    IsColimit (Cofan.mk (sheafify P) fun r => sheafifyMap (ι r)) :=
  isColimitCofanMkObjOfIsColimit (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)) C ι
    hS.isColimitPresheaf

end PresheafAlgebra.IsGraded

end Graded

end SheafAlgebraOperations

end Hartshorne
