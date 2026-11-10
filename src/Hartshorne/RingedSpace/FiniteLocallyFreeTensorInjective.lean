/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Mathlib.RingTheory.Flat.Basic

/-!
# Tensoring an injective by a finite locally free sheaf on a ringed space

Hartshorne, *Algebraic Geometry*, III, Lemma 6.6.

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`; `𝒪_X`-modules are `SheafOfModules (ringCatSheafOf R)`. If `L` is a locally free
`𝒪_X`-module of finite rank (`Hartshorne.Ringed.IsFiniteLocallyFree`) and `J` is an injective
object of the category of `𝒪_X`-modules, then `L ⊗ J` is injective
(`Hartshorne.Ringed.moduleSheafTensor_injective`).

Proof. Write `M = L^∨`. A local frame of `L` gives the dual local frame of `M`, so `M` admits
frames locally. Hence:

* tensoring with `M` preserves monomorphisms (`modulesTensorMap_mono_of_localFrames`): on an open
  carrying a frame, `M(V)` is a free `𝒪_X(V)`-module, so the presheaf-level map
  `M(V) ⊗ A(V) → M(V) ⊗ B(V)` is injective there; therefore it is injective on stalks, and so is the
  map of sheafified tensor products, which is thus injective on sections;
* by the tensor–Hom adjunction `Hom(M ⊗ -, J) ≃ Hom(-, ℋom(M, J))` the sheaf `ℋom(M, J)` is
  injective (`injective_moduleSheafHom_of_localFrames`);
* finally `L ⊗ J ≅ L^∨∨ ⊗ J ≅ ℋom(L^∨, J)` by the double-dual isomorphism and the canonical
  isomorphism `E^∨ ⊗ F ≅ ℋom(E, F)` for `E = L^∨`, which has frames locally.

For a scheme `X`, `X.Modules` is definitionally `SheafOfModules (ringCatSheafOf X.sheaf)`, so this
applies to schemes with `R := X.sheaf`; `Scheme.Modules.isFiniteLocallyFree_iff` translates the
finiteness hypothesis.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
open scoped TensorProduct

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

set_option hygiene false in
/-- Sections of the structure sheaf over an open. -/
local notation3 "𝒪(" U ")" => R.obj.obj (Opposite.op U)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

section Monos

/-- A monomorphism of `𝒪_X`-modules is injective on the sections over every open. -/
lemma modules_injective_app_of_mono {A B : 𝓜} (f : A ⟶ B) [Mono f] (U : Opens X) :
    Function.Injective (sectionsMap f U) := by
  let G : 𝓜 ⥤ AddCommGrpCat.{u} :=
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _) ⋙ (evaluation _ _).obj (op U)
  have hG : PreservesFiniteLimits G := by
    have hS : ∀ S : Sheaf (Opens.grothendieckTopology X) RingCat.{u},
        PreservesLimits (SheafOfModules.forget.{u} S) := fun _ => inferInstance
    have := hS (ringCatSheafOf R)
    have : PreservesLimits
        (SheafOfModules.forget.{u} (ringCatSheafOf R) ⋙ PresheafOfModules.toPresheaf _) :=
      comp_preservesLimits _ _
    have := PreservesLimitsOfSize.preservesFiniteLimits
      (SheafOfModules.forget.{u} (ringCatSheafOf R) ⋙ PresheafOfModules.toPresheaf _)
    have := PreservesLimitsOfSize.preservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))
    exact comp_preservesFiniteLimits _ _
  exact (AddCommGrpCat.mono_iff_injective _).mp (G.map_mono f)

/-- A morphism of `𝒪_X`-modules injective on the sections over every open is a monomorphism. -/
lemma modules_mono_of_injective_app {A B : 𝓜} (f : A ⟶ B)
    (h : ∀ U : Opens X, Function.Injective (sectionsMap f U)) : Mono f := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective fun U => h U.unop

end Monos

section TensorFunctoriality

variable {E E' E'' F F' F'' : 𝓜}

/-- An isomorphism `E ≅ E'` induces an isomorphism `E ⊗ F ≅ E' ⊗ F`. -/
private noncomputable def modulesTensorIsoLeft (α : E ≅ E') (F : 𝓜) :
    @Iso 𝓜 _ (moduleSheafTensor E F) (moduleSheafTensor E' F) where
  hom := modulesTensorMap α.hom (𝟙 F)
  inv := modulesTensorMap α.inv (𝟙 F)
  hom_inv_id := by
    rw [← modulesTensorMap_comp, α.hom_inv_id, Category.id_comp, modulesTensorMap_id]
  inv_hom_id := by
    rw [← modulesTensorMap_comp, α.inv_hom_id, Category.id_comp, modulesTensorMap_id]

end TensorFunctoriality

section TensorMono

/-- A family of maps of presheaves that is injective on all opens inside a neighbourhood of `x`
is injective on the stalk at `x`. -/
lemma stalkFunctor_map_injective_of_locally_injective {Y : TopCat.{u}}
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} Y} (p : P ⟶ Q) {x : Y} {U : Opens Y} (hx : x ∈ U)
    (hp : ∀ V : Opens Y, V ≤ U → Function.Injective (p.app (op V))) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map p) := by
  intro s t hst
  obtain ⟨V, hVU, hxV, s, rfl⟩ := P.exists_le_germ_eq s hx
  obtain ⟨V', hV'U, hxV', t, rfl⟩ := P.exists_le_germ_eq t hx
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iV, iV', heq⟩ := Q.germ_eq x hxV hxV' _ _ hst
  have hWU : W ≤ U := (leOfHom iV).trans hVU
  have e : ∀ {V₁ V₂ : Opens Y} (i : V₂ ⟶ V₁) (a : ToType (P.obj (op V₁))),
      Q.map i.op (p.app (op V₁) a) = p.app (op V₂) (P.map i.op a) := fun i a => by
    rw [← ConcreteCategory.comp_apply, ← p.naturality, ConcreteCategory.comp_apply]
  rw [e, e] at heq
  have := hp W hWU heq
  rw [← TopCat.Presheaf.germ_res_apply P iV x hxW,
    ← TopCat.Presheaf.germ_res_apply P iV' x hxW, this]

/-- On an open carrying a frame, sections of a module are a free module over the sections of
`𝒪_X`. -/
lemma IsLocalFrame.free_sections {ι : Type u} [Fintype ι] {M : 𝓜} {U : Opens X}
    {e : ι → Γ(M, U)} (hM : IsLocalFrame M U e) {V : Opens X} (h : V ≤ U) :
    Module.Free 𝒪(V) Γ(M, V) :=
  Module.Free.of_equiv (LinearEquiv.ofBijective (localFrameMap M e h) (hM V h))

variable {M A B : 𝓜}

variable (M) in
/-- The presheaf-level map `M(U) ⊗ A(U) → M(U) ⊗ B(U)` induced by `f : A ⟶ B`. -/
noncomputable abbrev presheafTensorWhiskerLeft (f : A ⟶ B) :
    moduleSheafTensorPresheaf M A ⟶ moduleSheafTensorPresheaf M B :=
  @MonoidalCategoryStruct.whiskerLeft
    (PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) _ _ M.val A.val B.val f.val

/-- If `M(V)` is flat over `𝒪_X(V)`, then `M(V) ⊗ A(V) → M(V) ⊗ B(V)` is injective whenever
`A(V) → B(V)` is. -/
lemma presheafTensorWhiskerLeft_app_injective (f : A ⟶ B) (V : Opens X)
    [Module.Flat 𝒪(V) Γ(M, V)] (hf : Function.Injective (sectionsMap f V)) :
    Function.Injective ((presheafTensorWhiskerLeft M f).app (op V)) := by
  let g : Γ(A, V) →ₗ[𝒪(V)] Γ(B, V) := (f.val.app (op V)).hom
  have hg : Function.Injective g := hf
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := Γ(M, V)) g hg

/-- The square relating the sheafification units with `M ◁ f` and `M ⊗ f`. -/
lemma moduleSheafTensorUnit_comp_modulesTensorMap (f : A ⟶ B) :
    moduleSheafTensorUnit M A ≫ (modulesTensorMap (𝟙 M) f).val =
      (presheafTensorWhiskerLeft M f) ≫ moduleSheafTensorUnit M B := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m a
  exact modulesTensorMap_tmul (𝟙 M) f (U := U.unop) m a

/-- **Tensoring with a module having frames locally preserves monomorphisms.** -/
lemma modulesTensorMap_mono_of_localFrames
    (hM : ∀ x : X, ∃ (U : Opens X) (ι : Type u) (_ : Fintype ι) (e : ι → Γ(M, U)),
      x ∈ U ∧ IsLocalFrame M U e)
    (f : A ⟶ B) [Mono f] : Mono (modulesTensorMap (𝟙 M) f) := by
  refine modules_mono_of_injective_app _ fun U => ?_
  let T := modulesTensorMap (𝟙 M) f
  let S : (⟨(moduleSheafTensor M A).val.presheaf,
      (moduleSheafTensor M A).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      ⟨(moduleSheafTensor M B).val.presheaf,
        (moduleSheafTensor M B).isSheaf⟩ := ⟨modulesMapPresheaf T⟩
  refine TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective S.1 U fun x _ => ?_
  obtain ⟨W, ι, _, e, hxW, hMW⟩ := hM x
  -- the presheaf-level map `M ◁ f` is injective on every open inside `W`
  have h1 := stalkFunctor_map_injective_of_locally_injective
    ((PresheafOfModules.toPresheaf _).map (presheafTensorWhiskerLeft M f)) hxW (fun V hV => by
      have := hMW.free_sections hV
      exact presheafTensorWhiskerLeft_app_injective f V (modules_injective_app_of_mono f V))
  have h2 := (ModuleSheafTensor.moduleSheafTensorUnitStalk_bijective M B x).1
  have h3 := (ModuleSheafTensor.moduleSheafTensorUnitStalk_bijective M A x).2
  have e1 : (PresheafOfModules.toPresheaf _).map (moduleSheafTensorUnit M A ≫ T.val) =
      @CategoryStruct.comp (TopCat.Presheaf AddCommGrpCat.{u} X) _ _ _ _
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (moduleSheafTensorPresheaf M A).presheaf) (modulesMapPresheaf T) :=
    (PresheafOfModules.toPresheaf _).map_comp _ _
  have e2 : (PresheafOfModules.toPresheaf _).map
      (presheafTensorWhiskerLeft M f ≫ moduleSheafTensorUnit M B) =
      @CategoryStruct.comp (TopCat.Presheaf AddCommGrpCat.{u} X) _ _ _ _
        ((PresheafOfModules.toPresheaf _).map (presheafTensorWhiskerLeft M f))
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (moduleSheafTensorPresheaf M B).presheaf) :=
    (PresheafOfModules.toPresheaf _).map_comp _ _
  have hs := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp _ _).symm.trans
    ((congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (e1.symm.trans ((congrArg _ (moduleSheafTensorUnit_comp_modulesTensorMap f)).trans e2))).trans
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp _ _))
  have key : ∀ y, (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.1
      (ModuleSheafTensor.moduleSheafTensorUnitStalk M A x y) =
      ModuleSheafTensor.moduleSheafTensorUnitStalk M B x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf _).map (presheafTensorWhiskerLeft M f)) y) :=
    fun y => ConcreteCategory.congr_hom hs y
  intro s t hst
  obtain ⟨s, rfl⟩ := h3 s
  obtain ⟨t, rfl⟩ := h3 t
  rw [key, key] at hst
  exact congrArg _ (h1 (h2 hst))

end TensorMono

section Injective

/-- If `M` admits frames locally and `J` is injective, then `ℋom(M, J)` is injective. -/
theorem injective_moduleSheafHom_of_localFrames {M J : 𝓜} [Injective J]
    (hM : ∀ x : X, ∃ (U : Opens X) (ι : Type u) (_ : Fintype ι) (e : ι → Γ(M, U)),
      x ∈ U ∧ IsLocalFrame M U e) :
    Injective (moduleSheafHom M J) where
  factors {A B} g f _ := by
    have := modulesTensorMap_mono_of_localFrames hM f
    obtain ⟨h, hh⟩ := Injective.factors ((moduleSheafTensorHomAdjunction M A J).symm g)
      (modulesTensorMap (𝟙 M) f)
    refine ⟨moduleSheafTensorHomAdjunction M B J h, ?_⟩
    rw [← moduleSheafTensorHomAdjunction_naturality_right, hh, Equiv.apply_symm_apply]

/-- The dual of a locally free module of finite rank admits frames locally. -/
lemma exists_isLocalFrame_dual_of_isFiniteLocallyFree {L : 𝓜} (hL : IsFiniteLocallyFree L)
    (x : X) :
    ∃ (U : Opens X) (ι : Type u) (_ : Fintype ι) (e : ι → Γ(moduleSheafDual L, U)),
      x ∈ U ∧ IsLocalFrame (moduleSheafDual L) U e := by
  classical
  obtain ⟨U, ι, _, e, hx, hLU⟩ := exists_isLocalFrame_of_isFiniteLocallyFree hL x
  exact ⟨U, ι, inferInstance, _, hx, hLU.dual⟩

/-- **Hartshorne III, Lemma 6.6.** If `L` is a locally free `𝒪_X`-module of finite rank and `J`
is an injective `𝒪_X`-module, then `L ⊗ J` is injective. -/
theorem moduleSheafTensor_injective (L J : 𝓜) (hL : IsFiniteLocallyFree L) [Injective J] :
    Injective (moduleSheafTensor L J) := by
  have hframes := exists_isLocalFrame_dual_of_isFiniteLocallyFree hL
  have := isIso_moduleSheafDualTensorMap_of_localFrames (F := J) hframes
  have hinj : Injective (moduleSheafHom (moduleSheafDual L) J) :=
    injective_moduleSheafHom_of_localFrames hframes
  exact Injective.of_iso
    ((modulesTensorIsoLeft (moduleSheafDoubleDualIso L hL) J).trans
      (asIso (moduleSheafDualTensorMap (moduleSheafDual L) J))).symm hinj

end Injective

end Ringed

end Hartshorne
