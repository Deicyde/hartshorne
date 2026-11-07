/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ModuleSheafTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# The monoidal category of module sheaves

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`. We equip the category of `𝒪_X`-modules `SheafOfModules (ringCatSheafOf R)` with a
monoidal category structure whose tensor product is the tensor product of module sheaves
`F ⊗_{𝒪_X} G` (Hartshorne II.5, p. 109) and whose unit is the structure sheaf `𝒪_X`.

The structure is obtained by localization: presheaves of modules form a monoidal category (with
the sectionwise tensor product), sheafification is a localization functor with respect to the
morphisms which become isomorphisms after sheafification (`sheafificationW`), and these
morphisms are stable under tensor products because, on stalks, tensor products of presheaves of
modules are tensor products of stalks. Mathlib's monoidal localization then provides the
associator, the unitors and the coherence axioms, and makes sheafification a monoidal functor.

The forgetful functor from sheaves to presheaves of modules, being right adjoint to the monoidal
sheafification functor, is lax monoidal; its tensor comparison `tensorπ F G`, from the presheaf
`U ↦ F(U) ⊗_{𝒪_X(U)} G(U)` to the underlying presheaf of `F ⊗ G`, sends `f ⊗ g` to the section
`f ⊗ g` (`tmulSection`). We prove:

* `moduleSheafTensorIsoTensor : moduleSheafTensor F G ≅ F ⊗ G`, compatible with the sections
  `f ⊗ g` (`moduleSheafTensorIsoTensor_hom_bilinear`);
* morphisms out of `F ⊗ G` are determined by their values on the sections `f ⊗ g`
  (`tensor_hom_ext`);
* formulas on the sections `f ⊗ g` for whiskering, the associator and the unitors.

For a scheme `X`, `X.Modules` is definitionally `SheafOfModules (ringCatSheafOf X.sheaf)`, and we
give `X.Modules` the corresponding monoidal structure.
-/

universe u

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open scoped TensorProduct

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- Presheaves of `𝒪_X`-modules. -/
local notation "𝓟" => PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

open ModuleSheafTensor

section Stalks

/-- A morphism of presheaves of abelian groups on a topological space becomes an isomorphism
after sheafification if and only if it induces isomorphisms on all stalks. -/
lemma W_iff_forall_isIso_stalk {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (f : P ⟶ Q) :
    (Opens.grothendieckTopology X).W f ↔
      ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) := by
  rw [GrothendieckTopology.W_iff]
  refine (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (C := AddCommGrpCat.{u})
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map f)).trans ?_
  refine forall_congr' fun x => ?_
  have h := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).congr_map
    (toSheafify_naturality (Opens.grothendieckTopology X) f)
  simp only [Functor.map_comp] at h
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} Q
  constructor
  · intro hf
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (sheafifyMap (Opens.grothendieckTopology X) f)) at hf
    have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (toSheafify (Opens.grothendieckTopology X) Q)) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (toSheafify (Opens.grothendieckTopology X) Q))
  · intro hf
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (sheafifyMap (Opens.grothendieckTopology X) f))
    have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (toSheafify (Opens.grothendieckTopology X) P) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (sheafifyMap (Opens.grothendieckTopology X) f)) := by
      rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_left
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (toSheafify (Opens.grothendieckTopology X) P)) _

variable {P Q : 𝓟}

/-- The additive map on stalks induced by a morphism of presheaves of modules. -/
noncomputable def stalkAddMap (g : P ⟶ Q) (x : X) : moduleStalk P x →+ moduleStalk Q x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map g)).hom

/-- The stalk map sends the germ of `s` to the germ of `g s`. -/
lemma stalkAddMap_germ (g : P ⟶ Q) (x : X) (U : Opens X) (hU : x ∈ U) (s : P.obj (op U)) :
    stalkAddMap g x (sectionGerm P x U hU s) = sectionGerm Q x U hU (g.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hU
    ((PresheafOfModules.toPresheaf _).map g) s

/-- The stalk map of a morphism of presheaves of modules is linear over the stalk of the ring
sheaf. -/
noncomputable def stalkLinearMap (g : P ⟶ Q) (x : X) :
    moduleStalk P x →ₗ[ringSheafStalk R x] moduleStalk Q x where
  toFun := stalkAddMap g x
  map_add' := map_add _
  map_smul' r s := by
    obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm P x s
    obtain ⟨W, hWU, hW, c, rfl⟩ := exists_le_ringGerm x r hU
    rw [← sectionGerm_res P x (homOfLE hWU) hW t, ← sectionGerm_smul, RingHom.id_apply,
      stalkAddMap_germ, stalkAddMap_germ, ← sectionGerm_smul]
    exact congrArg (sectionGerm Q x W hW) ((g.app (op W)).hom.map_smul c _)

/-- The linear stalk map has the underlying additive stalk map. -/
lemma stalkLinearMap_apply (g : P ⟶ Q) (x : X) (s : moduleStalk P x) :
    stalkLinearMap g x s = stalkAddMap g x s := rfl

/-- Membership in `J.W` of a morphism of presheaves of modules, in terms of stalks. -/
lemma W_toPresheaf_iff (g : P ⟶ Q) :
    (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map g) ↔
      ∀ x : X, Function.Bijective (stalkAddMap g x) := by
  rw [W_iff_forall_isIso_stalk]
  refine forall_congr' fun x => ?_
  exact ConcreteCategory.isIso_iff_bijective _

/-- On stalks, `F ◁ g` is `id ⊗ gₓ`, through the stalk isomorphism of the presheaf tensor
product. -/
lemma stalkAddMap_whiskerLeft (F : 𝓟) (g : P ⟶ Q) (x : X) (t : moduleStalk (F ⊗ P) x) :
    presheafTensorStalkIso F Q x (stalkAddMap (F ◁ g) x t) =
      TensorProduct.map LinearMap.id (stalkLinearMap g x) (presheafTensorStalkIso F P x t) := by
  obtain ⟨U, hU, s, rfl⟩ := exists_sectionGerm (F ⊗ P) x t
  rw [stalkAddMap_germ]
  change F.obj (op U) ⊗[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] P.obj (op U) at s
  induction s using TensorProduct.induction_on with
  | zero => erw [map_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul f p =>
    change presheafTensorStalkToTensor F Q x (sectionGerm (F ⊗ Q) x U hU (f ⊗ₜ g.app (op U) p)) =
      TensorProduct.map LinearMap.id (stalkLinearMap g x)
        (presheafTensorStalkToTensor F P x (sectionGerm (F ⊗ P) x U hU (f ⊗ₜ p)))
    rw [presheafTensorStalkToTensor_germ, presheafTensorStalkToTensor_germ,
      tensorStalkComponent_tmul, tensorStalkComponent_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, stalkLinearMap_apply, stalkAddMap_germ]
  | add a b ha hb => erw [map_add, map_add, map_add, map_add, map_add, map_add, ha, hb]

/-- On stalks, `g ▷ F` is `gₓ ⊗ id`, through the stalk isomorphism of the presheaf tensor
product. -/
lemma stalkAddMap_whiskerRight (g : P ⟶ Q) (F : 𝓟) (x : X) (t : moduleStalk (P ⊗ F) x) :
    presheafTensorStalkIso Q F x (stalkAddMap (g ▷ F) x t) =
      TensorProduct.map (stalkLinearMap g x) LinearMap.id (presheafTensorStalkIso P F x t) := by
  obtain ⟨U, hU, s, rfl⟩ := exists_sectionGerm (P ⊗ F) x t
  rw [stalkAddMap_germ]
  change P.obj (op U) ⊗[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] F.obj (op U) at s
  induction s using TensorProduct.induction_on with
  | zero => erw [map_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul p f =>
    change presheafTensorStalkToTensor Q F x (sectionGerm (Q ⊗ F) x U hU (g.app (op U) p ⊗ₜ f)) =
      TensorProduct.map (stalkLinearMap g x) LinearMap.id
        (presheafTensorStalkToTensor P F x (sectionGerm (P ⊗ F) x U hU (p ⊗ₜ f)))
    rw [presheafTensorStalkToTensor_germ, presheafTensorStalkToTensor_germ,
      tensorStalkComponent_tmul, tensorStalkComponent_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, stalkLinearMap_apply, stalkAddMap_germ]
  | add a b ha hb => erw [map_add, map_add, map_add, map_add, map_add, map_add, ha, hb]

end Stalks

section Localization

variable (R) in
/-- The morphisms of presheaves of `𝒪_X`-modules which become isomorphisms after
sheafification. -/
def sheafificationW : MorphismProperty 𝓟 :=
  (Opens.grothendieckTopology X).W.inverseImage (PresheafOfModules.toPresheaf _)

/-- A morphism of presheaves of modules becomes an isomorphism after sheafification if and only
if it induces bijections on all stalks. -/
lemma sheafificationW_iff {P Q : 𝓟} (g : P ⟶ Q) :
    sheafificationW R g ↔ ∀ x : X, Function.Bijective (stalkAddMap g x) :=
  W_toPresheaf_iff g

/-- The morphisms inverted by sheafification are stable under tensor products. -/
instance sheafificationW_isMonoidal : (sheafificationW R).IsMonoidal where
  id_mem P := (sheafificationW_iff _).2 fun x => by
    have : stalkAddMap (𝟙 P) x = AddMonoidHom.id _ := by
      ext s
      obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm P x s
      rw [stalkAddMap_germ]
      rfl
    rw [this]
    exact Function.bijective_id
  comp_mem f g hf hg := (sheafificationW_iff _).2 fun x => by
    have : stalkAddMap (f ≫ g) x = (stalkAddMap g x).comp (stalkAddMap f x) := by
      ext s
      obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm _ x s
      rw [AddMonoidHom.comp_apply, stalkAddMap_germ, stalkAddMap_germ, stalkAddMap_germ]
      rfl
    rw [this]
    exact ((sheafificationW_iff g).1 hg x).comp ((sheafificationW_iff f).1 hf x)
  whiskerLeft F P Q g hg := (sheafificationW_iff _).2 fun x => by
    let e := LinearEquiv.ofBijective (stalkLinearMap g x) ((sheafificationW_iff g).1 hg x)
    have h : (stalkAddMap (F ◁ g) x : _ → _) = (presheafTensorStalkIso F Q x).symm ∘
        (TensorProduct.congr (LinearEquiv.refl _ _) e) ∘ presheafTensorStalkIso F P x := by
      funext t
      apply (presheafTensorStalkIso F Q x).injective
      rw [Function.comp_apply, Function.comp_apply, LinearEquiv.apply_symm_apply,
        stalkAddMap_whiskerLeft]
      rfl
    rw [h]
    exact (presheafTensorStalkIso F Q x).symm.bijective.comp
      ((TensorProduct.congr (LinearEquiv.refl _ _) e).bijective.comp
        (presheafTensorStalkIso F P x).bijective)
  whiskerRight {P Q} g hg F := (sheafificationW_iff _).2 fun x => by
    let e := LinearEquiv.ofBijective (stalkLinearMap g x) ((sheafificationW_iff g).1 hg x)
    have h : (stalkAddMap (g ▷ F) x : _ → _) = (presheafTensorStalkIso Q F x).symm ∘
        (TensorProduct.congr e (LinearEquiv.refl _ _)) ∘ presheafTensorStalkIso P F x := by
      funext t
      apply (presheafTensorStalkIso Q F x).injective
      rw [Function.comp_apply, Function.comp_apply, LinearEquiv.apply_symm_apply,
        stalkAddMap_whiskerRight]
      rfl
    rw [h]
    exact (presheafTensorStalkIso Q F x).symm.bijective.comp
      ((TensorProduct.congr e (LinearEquiv.refl _ _)).bijective.comp
        (presheafTensorStalkIso P F x).bijective)

variable (R) in
/-- Sheafification of presheaves of `𝒪_X`-modules. -/
noncomputable abbrev sheafificationFunctor : 𝓟 ⥤ 𝓜 :=
  PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheafOf R).obj)

variable (R) in
/-- The sheafification adjunction for presheaves of `𝒪_X`-modules. -/
noncomputable abbrev sheafificationAdj :
    sheafificationFunctor R ⊣
      SheafOfModules.forget.{u} (ringCatSheafOf R) ⋙
        PresheafOfModules.restrictScalars.{u} (𝟙 (ringCatSheafOf R).obj) :=
  PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringCatSheafOf R).obj)

/-- Sheafification is the localization at the morphisms which it inverts. -/
instance sheafificationFunctor_isLocalization :
    (sheafificationFunctor R).IsLocalization (sheafificationW R) :=
  inferInstanceAs ((PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheafOf R).obj)).IsLocalization
    ((Opens.grothendieckTopology X).W.inverseImage (PresheafOfModules.toPresheaf _)))

/-- The forgetful functor from sheaves to presheaves of modules is full. -/
instance forget_full : (SheafOfModules.forget.{u} (ringCatSheafOf R) ⋙
    PresheafOfModules.restrictScalars.{u} (𝟙 (ringCatSheafOf R).obj)).Full := by
  have := (SheafOfModules.fullyFaithfulForget.{u} (ringCatSheafOf R)).full
  infer_instance

/-- The forgetful functor from sheaves to presheaves of modules is faithful. -/
instance forget_faithful : (SheafOfModules.forget.{u} (ringCatSheafOf R) ⋙
    PresheafOfModules.restrictScalars.{u} (𝟙 (ringCatSheafOf R).obj)).Faithful := by
  have := (SheafOfModules.fullyFaithfulForget.{u} (ringCatSheafOf R)).faithful
  infer_instance

/-- The counit of the sheafification adjunction is an isomorphism. -/
instance isIso_sheafificationAdj_counit_app (F : 𝓜) :
    IsIso ((sheafificationAdj R).counit.app F) :=
  have := (sheafificationAdj R).counit_isIso_of_R_fully_faithful
  NatIso.isIso_app_of_isIso _ F

/-- The counit `(F.val)^# ≅ F` of the sheafification adjunction, for a sheaf of modules `F`. -/
noncomputable def sheafificationCounitIso (F : 𝓜) :
    (sheafificationFunctor R).obj F.val ≅ F :=
  @asIso _ _ _ _ ((sheafificationAdj R).counit.app F) (isIso_sheafificationAdj_counit_app F)

variable (R) in
/-- The sheafification of the unit presheaf is the structure sheaf. -/
noncomputable def sheafificationUnitIso :
    (sheafificationFunctor R).obj (𝟙_ 𝓟) ≅ SheafOfModules.unit (ringCatSheafOf R) :=
  @asIso _ _ _ _ ((sheafificationAdj R).counit.app (SheafOfModules.unit (ringCatSheafOf R)))
    (isIso_sheafificationAdj_counit_app _)

end Localization


section Monoidal

/-- **The monoidal category of `𝒪_X`-modules**, obtained by localizing the monoidal category of
presheaves of modules along sheafification. Its unit is the structure sheaf `𝒪_X` and its tensor
product is isomorphic to the tensor product of module sheaves (`moduleSheafTensorIsoTensor`). -/
noncomputable instance monoidalCategory : MonoidalCategory 𝓜 :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := sheafificationFunctor R) (W := sheafificationW R)
      (sheafificationUnitIso R)))

/-- The unit object is the structure sheaf `𝒪_X`. -/
lemma tensorUnit_eq : 𝟙_ 𝓜 = SheafOfModules.unit (ringCatSheafOf R) := rfl

/-- Sheafification is a monoidal functor. -/
noncomputable instance sheafificationFunctor_monoidal : (sheafificationFunctor R).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := sheafificationFunctor R) (W := sheafificationW R) (sheafificationUnitIso R)).Monoidal

/-- The forgetful functor from sheaves to presheaves of modules is lax monoidal, as the right
adjoint of the monoidal sheafification functor. -/
noncomputable instance forget_laxMonoidal :
    (SheafOfModules.forget.{u} (ringCatSheafOf R) ⋙
      PresheafOfModules.restrictScalars.{u} (𝟙 (ringCatSheafOf R).obj)).LaxMonoidal :=
  (sheafificationAdj R).rightAdjointLaxMonoidal

variable (F G H : 𝓜)

/-- The canonical map from the presheaf tensor product `U ↦ F(U) ⊗_{𝒪_X(U)} G(U)` to the
underlying presheaf of the sheaf tensor product `F ⊗ G`. -/
noncomputable def tensorπ : F.val ⊗ G.val ⟶ (F ⊗ G).val :=
  Functor.LaxMonoidal.μ (SheafOfModules.forget.{u} (ringCatSheafOf R) ⋙
      PresheafOfModules.restrictScalars.{u} (𝟙 (ringCatSheafOf R).obj)) F G

/-- The section `f ⊗ g` of the sheaf tensor product `F ⊗ G`. -/
noncomputable def tmulSection {U : (Opens X)ᵒᵖ} (f : F.val.obj U) (g : G.val.obj U) :
    (F ⊗ G).val.obj U :=
  (tensorπ F G).app U (f ⊗ₜ g)

/-- The comparison isomorphism between the tensor product of module sheaves (defined as the
sheafification of the presheaf tensor product) and the tensor product of the monoidal
structure. -/
noncomputable def moduleSheafTensorIsoTensor : moduleSheafTensor F G ≅ F ⊗ G :=
  (Functor.Monoidal.μIso (sheafificationFunctor R) F.val G.val).symm ≪≫
    tensorIso (sheafificationCounitIso F) (sheafificationCounitIso G)

/-- The comparison isomorphism, precomposed with the sheafification unit, is `tensorπ`. -/
lemma moduleSheafTensorUnit_comp_isoTensor :
    moduleSheafTensorUnit F G ≫ (moduleSheafTensorIsoTensor F G).hom.val = tensorπ F G := by
  simp [tensorπ, moduleSheafTensorUnit, moduleSheafTensorIsoTensor,
    Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
  rfl

/-- The comparison isomorphism sends the section `f ⊗ g` of `moduleSheafTensor F G` to the section
`f ⊗ g` of `F ⊗ G`. -/
theorem moduleSheafTensorIsoTensor_hom_bilinear {U : (Opens X)ᵒᵖ} (f : F.val.obj U)
    (g : G.val.obj U) :
    (moduleSheafTensorIsoTensor F G).hom.val.app U ((moduleSheafTensorBilinear F G).app U f g) =
      tmulSection F G f g :=
  congrArg (fun k => (k.app U).hom (f ⊗ₜ g)) (moduleSheafTensorUnit_comp_isoTensor F G)

variable {F G H}

/-- Morphisms out of `F ⊗ G` are determined by their values on the sections `f ⊗ g`. -/
theorem tensor_hom_ext {φ ψ : F ⊗ G ⟶ H}
    (h : ∀ (U : (Opens X)ᵒᵖ) (f : F.val.obj U) (g : G.val.obj U),
      φ.val.app U (tmulSection F G f g) = ψ.val.app U (tmulSection F G f g)) : φ = ψ := by
  rw [← cancel_epi (moduleSheafTensorIsoTensor F G).hom]
  apply (moduleSheafTensorHomEquiv F G H).injective
  ext U f g
  rw [moduleSheafTensorHomEquiv_apply, moduleSheafTensorHomEquiv_apply,
    ModuleSheafBilinear.postcomp_app, ModuleSheafBilinear.postcomp_app]
  change φ.val.app U ((moduleSheafTensorIsoTensor F G).hom.val.app U
      ((moduleSheafTensorBilinear F G).app U f g)) =
    ψ.val.app U ((moduleSheafTensorIsoTensor F G).hom.val.app U
      ((moduleSheafTensorBilinear F G).app U f g))
  rw [moduleSheafTensorIsoTensor_hom_bilinear]
  exact h U f g

end Monoidal

section Formulas

set_option hygiene false in
/-- The forgetful functor from `𝒪_X`-modules to presheaves of modules, as the right adjoint of
sheafification. -/
local notation "𝓕" => (SheafOfModules.forget.{u} (ringCatSheafOf R) ⋙
  PresheafOfModules.restrictScalars.{u} (𝟙 (ringCatSheafOf R).obj))

variable {F F' G G' : 𝓜}

/-- The unit of the lax monoidal forgetful functor is the identity of the unit presheaf. -/
lemma forget_ε : Functor.LaxMonoidal.ε 𝓕 = 𝟙 _ := by
  change (sheafificationAdj R).homEquiv _ _ (Functor.OplaxMonoidal.η (sheafificationFunctor R)) = _
  have : Functor.OplaxMonoidal.η (sheafificationFunctor R) =
      (sheafificationAdj R).counit.app (SheafOfModules.unit _) := rfl
  rw [this]
  exact ((sheafificationAdj R).homEquiv_unit _ _ _).trans
    ((sheafificationAdj R).right_triangle_components (SheafOfModules.unit _))

/-- `(f + f') ⊗ g = f ⊗ g + f' ⊗ g`. -/
lemma tmulSection_add_left {U : (Opens X)ᵒᵖ} (f f' : F.val.obj U) (g : G.val.obj U) :
    tmulSection F G (f + f') g = tmulSection F G f g + tmulSection F G f' g := by
  simp only [tmulSection, TensorProduct.add_tmul]
  exact map_add ((tensorπ F G).app U).hom (f ⊗ₜ g) (f' ⊗ₜ g)

/-- `f ⊗ (g + g') = f ⊗ g + f ⊗ g'`. -/
lemma tmulSection_add_right {U : (Opens X)ᵒᵖ} (f : F.val.obj U) (g g' : G.val.obj U) :
    tmulSection F G f (g + g') = tmulSection F G f g + tmulSection F G f g' := by
  simp only [tmulSection, TensorProduct.tmul_add]
  exact map_add ((tensorπ F G).app U).hom (f ⊗ₜ g) (f ⊗ₜ g')

/-- `0 ⊗ g = 0`. -/
lemma tmulSection_zero_left {U : (Opens X)ᵒᵖ} (g : G.val.obj U) :
    tmulSection F G 0 g = 0 := by
  simp only [tmulSection, TensorProduct.zero_tmul]
  exact map_zero ((tensorπ F G).app U).hom

/-- `f ⊗ 0 = 0`. -/
lemma tmulSection_zero_right {U : (Opens X)ᵒᵖ} (f : F.val.obj U) :
    tmulSection F G f 0 = 0 := by
  simp only [tmulSection, TensorProduct.tmul_zero]
  exact map_zero ((tensorπ F G).app U).hom

/-- `(φ ⊗ ψ)(f ⊗ g) = φ f ⊗ ψ g`. -/
theorem tensorHom_tmulSection (φ : F ⟶ F') (ψ : G ⟶ G') {U : (Opens X)ᵒᵖ} (f : F.val.obj U)
    (g : G.val.obj U) :
    (φ ⊗ₘ ψ).val.app U (tmulSection F G f g) =
      tmulSection F' G' (φ.val.app U f) (ψ.val.app U g) :=
  (congrArg (fun k => (k.app U).hom (f ⊗ₜ g)) (Functor.LaxMonoidal.μ_natural 𝓕 φ ψ)).symm

/-- `(F ◁ ψ)(f ⊗ g) = f ⊗ ψ g`. -/
theorem whiskerLeft_tmulSection (ψ : G ⟶ G') {U : (Opens X)ᵒᵖ} (f : F.val.obj U)
    (g : G.val.obj U) :
    (F ◁ ψ).val.app U (tmulSection F G f g) = tmulSection F G' f (ψ.val.app U g) :=
  (congrArg (fun k => (k.app U).hom (f ⊗ₜ g)) (Functor.LaxMonoidal.μ_natural_right 𝓕 F ψ)).symm

/-- `(φ ▷ G)(f ⊗ g) = φ f ⊗ g`. -/
theorem whiskerRight_tmulSection (φ : F ⟶ F') {U : (Opens X)ᵒᵖ} (f : F.val.obj U)
    (g : G.val.obj U) :
    (φ ▷ G).val.app U (tmulSection F G f g) = tmulSection F' G (φ.val.app U f) g :=
  (congrArg (fun k => (k.app U).hom (f ⊗ₜ g)) (Functor.LaxMonoidal.μ_natural_left 𝓕 φ G)).symm

variable (F G H : 𝓜)

/-- The associator sends `(f ⊗ g) ⊗ h` to `f ⊗ (g ⊗ h)`. -/
theorem associator_hom_tmulSection {U : (Opens X)ᵒᵖ} (f : F.val.obj U) (g : G.val.obj U)
    (h : H.val.obj U) :
    (α_ F G H).hom.val.app U (tmulSection (F ⊗ G) H (tmulSection F G f g) h) =
      tmulSection F (G ⊗ H) f (tmulSection G H g h) :=
  congrArg (fun k => (k.app U).hom ((f ⊗ₜ g) ⊗ₜ h)) (Functor.LaxMonoidal.associativity 𝓕 F G H)

/-- The left unitor sends `r ⊗ f` to `r • f`. -/
theorem leftUnitor_hom_tmulSection {U : (Opens X)ᵒᵖ}
    (r : (R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (f : F.val.obj U) :
    (λ_ F).hom.val.app U (tmulSection (𝟙_ 𝓜) F r f) = r • f := by
  have e := Functor.LaxMonoidal.left_unitality 𝓕 F
  erw [forget_ε, id_whiskerRight, Category.id_comp] at e
  exact (congrArg (fun k => (k.app U).hom (r ⊗ₜ f)) e).symm

/-- The right unitor sends `f ⊗ r` to `r • f`. -/
theorem rightUnitor_hom_tmulSection {U : (Opens X)ᵒᵖ}
    (r : (R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (f : F.val.obj U) :
    (ρ_ F).hom.val.app U (tmulSection F (𝟙_ 𝓜) f r) = r • f := by
  have e := Functor.LaxMonoidal.right_unitality 𝓕 F
  erw [forget_ε, MonoidalCategory.whiskerLeft_id, Category.id_comp] at e
  exact (congrArg (fun k => (k.app U).hom (f ⊗ₜ r)) e).symm

end Formulas

section Scheme

/-- The monoidal category of `𝒪_X`-modules on a scheme `X`. -/
noncomputable instance schemeModulesMonoidalCategory (Y : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  monoidalCategory

/-! The section formulas, restated for the monoidal structure on `Y.Modules` (so that they can be
used to rewrite terms built from that instance). -/

variable {Y : AlgebraicGeometry.Scheme.{u}} {F F' G G' H : Y.Modules}

/-- `(φ ▷ G)(f ⊗ g) = φ f ⊗ g`, on a scheme. -/
theorem scheme_whiskerRight_tmulSection (φ : F ⟶ F') {U} (f : F.val.obj U)
    (g : G.val.obj U) :
    (φ ▷ G).val.app U (tmulSection F G f g) = tmulSection F' G (φ.val.app U f) g :=
  whiskerRight_tmulSection φ f g

/-- `(F ◁ ψ)(f ⊗ g) = f ⊗ ψ g`, on a scheme. -/
theorem scheme_whiskerLeft_tmulSection (ψ : G ⟶ G') {U} (f : F.val.obj U)
    (g : G.val.obj U) :
    (F ◁ ψ).val.app U (tmulSection F G f g) = tmulSection F G' f (ψ.val.app U g) :=
  whiskerLeft_tmulSection ψ f g

/-- The associator sends `(f ⊗ g) ⊗ h` to `f ⊗ (g ⊗ h)`, on a scheme. -/
theorem scheme_associator_hom_tmulSection {U} (f : F.val.obj U) (g : G.val.obj U)
    (h : H.val.obj U) :
    (α_ F G H).hom.val.app U (tmulSection (F ⊗ G : Y.Modules) H (tmulSection F G f g) h) =
      tmulSection F (G ⊗ H : Y.Modules) f (tmulSection G H g h) :=
  associator_hom_tmulSection F G H f g h

end Scheme

end Ringed

end Hartshorne
