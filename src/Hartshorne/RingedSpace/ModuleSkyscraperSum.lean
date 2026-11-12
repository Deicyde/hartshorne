/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleSkyscraper

/-!
# Module sheaves supported at finitely many closed points

Let `(X, 𝒪_X)` be a ringed space and `F` an `𝒪_X`-module. If `F` has zero stalks outside a finite
set `S` of closed points, then `F` is the direct sum of the skyscraper sheaves of its stalks at the
points of `S`: the morphism `F ⟶ ⨁_{x ∈ S} x_*(F_x)` whose components are the units of the
stalk–skyscraper adjunctions is an isomorphism (`moduleSheafIsoBiproductSkyscraper`).

The proof checks the morphism on stalks. The stalk of `x_* N` at a point `y` outside the closure
of `{x}` is zero (`subsingleton_moduleStalk_moduleSkyscraper`), and at `x` itself the unit of the
adjunction induces an isomorphism `F_x ≅ (x_*(F_x))_x`, because the counit `(x_* N)_x ⟶ N` is an
isomorphism (`isIso_moduleStalkSkyscraper_counit`). This supplements Hartshorne IV, Exercise 1.8
(p. 298), where the quotient `Q = ν_* 𝒪_X̃ / 𝒪_X` is written as a sum over points of its stalks.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Hartshorne

namespace Ringed

open ModuleSheafTensor

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor preserves biproducts indexed by a finite type in any universe. -/
lemma preservesBiproductsOfShape_of_additive {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] (J : Type*) [Fintype J] :
    PreservesBiproductsOfShape J F where
  preserves {_} := ⟨fun hb => ⟨isBilimitOfTotal _ (by
    simp_rw [F.mapBicone_π, F.mapBicone_ι, ← F.map_comp]
    erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])⟩⟩

/-- A morphism `g : A ⟶ ⨁ B` is an isomorphism if all summands but `B j₀` are zero and the
component `A ⟶ B j₀` is an isomorphism. -/
lemma isIso_of_isIso_comp_biproduct_π {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type*}
    {B : J → C} [HasBiproduct B] {A : C} (g : A ⟶ ⨁ B) (j₀ : J) (hB : ∀ j, j ≠ j₀ → IsZero (B j))
    (h : IsIso (g ≫ biproduct.π B j₀)) : IsIso g := by
  refine ⟨⟨biproduct.π B j₀ ≫ inv (g ≫ biproduct.π B j₀), ?_, ?_⟩⟩
  · rw [← Category.assoc, IsIso.hom_inv_id]
  refine biproduct.hom_ext _ _ fun j => ?_
  by_cases hj : j = j₀
  · subst hj
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  · exact (hB j hj).eq_of_tgt _ _

/-- A morphism from a zero object into a biproduct of zero objects is an isomorphism. -/
lemma isIso_of_isZero_biproduct {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type*}
    {B : J → C} [HasBiproduct B] {A : C} (g : A ⟶ ⨁ B) (hA : IsZero A) (hB : ∀ j, IsZero (B j)) :
    IsIso g := by
  have hZ : IsZero (⨁ B) := by
    rw [IsZero.iff_id_eq_zero]
    exact biproduct.hom_ext _ _ fun j => (hB j).eq_of_tgt _ _
  exact ⟨⟨0, hA.eq_of_src _ _, hZ.eq_of_src _ _⟩⟩

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

-- Finite biproducts of `𝒪_X`-modules, from finite products in the preadditive category.
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

/-- A morphism of `𝒪_X`-modules inducing isomorphisms on all stalks is an isomorphism. -/
lemma isIso_of_isIso_moduleStalkFunctor_map {A B : 𝓜} (φ : A ⟶ B)
    (h : ∀ y : X, IsIso ((moduleStalkFunctor y).map φ)) : IsIso φ := by
  have : (SheafOfModules.forget (ringCatSheafOf R)).ReflectsIsomorphisms :=
    (SheafOfModules.fullyFaithfulForget _).reflectsIsomorphisms
  have : (SheafOfModules.forget (ringCatSheafOf R) ⋙
      PresheafOfModules.toPresheaf (ringCatSheafOf R).obj).ReflectsIsomorphisms :=
    reflectsIsomorphisms_comp _ _
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget (ringCatSheafOf R) ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro U
  let f : (⟨A.val.presheaf, A.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      ⟨B.val.presheaf, B.isSheaf⟩ := ⟨(PresheafOfModules.toPresheaf _).map φ.val⟩
  have hb := TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f U.unop
    (fun y _ => by
      have hy := (ConcreteCategory.isIso_iff_bijective _).mp (h y)
      exact hy)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

/-- The stalk of the skyscraper sheaf `x_* N` at a point outside the closure of `{x}` is zero. -/
lemma subsingleton_moduleStalk_moduleSkyscraper {x y : X} (hy : y ∉ closure ({x} : Set X))
    (N : ModuleCat.{u} (ringSheafStalk R x)) :
    Subsingleton ((moduleStalkFunctor y).obj ((moduleSkyscraper x).obj N)) := by
  obtain ⟨V, hVo, hyV, hxV⟩ : ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ x ∉ V := by
    by_contra hcon
    push Not at hcon
    exact hy (mem_closure_iff.mpr fun o ho hyo => ⟨x, hcon o ho hyo, rfl⟩)
  suffices h0 : ∀ s : (moduleStalkFunctor y).obj ((moduleSkyscraper x).obj N), s = 0 from
    ⟨fun a b => (h0 a).trans (h0 b).symm⟩
  intro s
  obtain ⟨U, hU, f, rfl⟩ := exists_sectionGerm _ y s
  let W : Opens X := U ⊓ ⟨V, hVo⟩
  have hW : y ∈ W := ⟨hU, hyV⟩
  rw [← sectionGerm_res _ y (homOfLE inf_le_left : W ⟶ U) hW f]
  have hres : res _ (homOfLE inf_le_left : W ⟶ U) f = 0 :=
    funext fun h => absurd h.down.2 hxV
  rw [hres, map_zero]
  rfl

variable (x : X)

/-- The counit `(x_* N)_x ⟶ N` of the stalk–skyscraper adjunction is an isomorphism. -/
lemma isIso_moduleStalkSkyscraper_counit (N : ModuleCat.{u} (ringSheafStalk R x)) :
    IsIso ((moduleStalkSkyscraperAdjunction x).counit.app N) := by
  have key : ∀ (U : Opens X) (h : x ∈ U) (f : ((moduleSkyscraper x).obj N).val.obj (op U)),
      (moduleStalkSkyscraperAdjunction x).counit.app N
        (sectionGerm ((moduleSkyscraper x).obj N).val x U h f) = f ⟨h⟩ :=
    fun U h f => ofSkyscraper_germ (𝟙 _) U h f
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero
    ((moduleStalkSkyscraperAdjunction x).counit.app N).hom).mpr fun a ha => ?_, fun n => ?_⟩
  · obtain ⟨U, hU, f, rfl⟩ := exists_sectionGerm _ x a
    rw [key] at ha
    have hf : f = 0 := funext fun h => ha
    rw [hf, map_zero]
    rfl
  · exact ⟨sectionGerm ((moduleSkyscraper x).obj N).val x ⊤ trivial (fun _ => n),
      key ⊤ trivial _⟩

/-- The unit `F ⟶ x_*(F_x)` of the stalk–skyscraper adjunction induces an isomorphism on stalks
at `x`. -/
lemma isIso_moduleStalkFunctor_map_unit (F : 𝓜) :
    IsIso ((moduleStalkFunctor x).map ((moduleStalkSkyscraperAdjunction x).unit.app F)) := by
  have := isIso_moduleStalkSkyscraper_counit x ((moduleStalkFunctor x).obj F)
  have : IsIso ((moduleStalkFunctor x).map ((moduleStalkSkyscraperAdjunction x).unit.app F) ≫
      (moduleStalkSkyscraperAdjunction x).counit.app ((moduleStalkFunctor x).obj F)) := by
    rw [(moduleStalkSkyscraperAdjunction x).left_triangle_components F]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((moduleStalkSkyscraperAdjunction x).counit.app ((moduleStalkFunctor x).obj F))

variable (F : 𝓜) (S : Finset X)

/-- The morphism `F ⟶ ⨁_{x ∈ S} x_*(F_x)` whose components are the units of the stalk–skyscraper
adjunctions. -/
noncomputable def toBiproductModuleSkyscraper :
    F ⟶ ⨁ fun x : S => (moduleSkyscraper x.1).obj ((moduleStalkFunctor x.1).obj F) :=
  biproduct.lift fun x => (moduleStalkSkyscraperAdjunction x.1).unit.app F

/-- If the points of the finite set `S` are closed and `F` has zero stalks outside `S`, then
`F ⟶ ⨁_{x ∈ S} x_*(F_x)` is an isomorphism. -/
theorem isIso_toBiproductModuleSkyscraper (hS : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hF : ∀ y ∉ S, Subsingleton ((moduleStalkFunctor y).obj F)) :
    IsIso (toBiproductModuleSkyscraper F S) := by
  refine isIso_of_isIso_moduleStalkFunctor_map _ fun y => ?_
  have := preservesBiproductsOfShape_of_additive (moduleStalkFunctor (R := R) y) S
  have hzero : ∀ x : S, x.1 ≠ y → IsZero ((moduleStalkFunctor y).obj
      ((moduleSkyscraper x.1).obj ((moduleStalkFunctor x.1).obj F))) := fun x hx => by
    have hy : y ∉ closure ({x.1} : Set X) := by
      rw [(hS x.1 x.2).closure_eq]
      exact fun h => hx (Set.mem_singleton_iff.mp h).symm
    have := subsingleton_moduleStalk_moduleSkyscraper hy ((moduleStalkFunctor x.1).obj F)
    exact ModuleCat.isZero_of_subsingleton _
  have hcomp := biproduct.map_lift_mapBiprod (moduleStalkFunctor y)
    (fun x : S => (moduleSkyscraper x.1).obj ((moduleStalkFunctor x.1).obj F))
    (fun x => (moduleStalkSkyscraperAdjunction x.1).unit.app F)
  have key : IsIso ((moduleStalkFunctor y).map (toBiproductModuleSkyscraper F S) ≫
      ((moduleStalkFunctor y).mapBiproduct _).hom) := by
    erw [hcomp]
    by_cases hy : y ∈ S
    · refine isIso_of_isIso_comp_biproduct_π _ ⟨y, hy⟩ (fun j hj => hzero j fun h => hj ?_) ?_
      · exact Subtype.ext h
      · rw [biproduct.lift_π]
        exact isIso_moduleStalkFunctor_map_unit y F
    · have := hF y hy
      exact isIso_of_isZero_biproduct _
        (ModuleCat.isZero_of_subsingleton ((moduleStalkFunctor y).obj F))
        fun x => hzero x fun h => hy (h ▸ x.2)
  exact IsIso.of_isIso_comp_right _ ((moduleStalkFunctor y).mapBiproduct _).hom

/-- **A module sheaf supported at finitely many closed points is the direct sum of the skyscraper
sheaves of its stalks.** If `S` is a finite set of closed points of `X` and the `𝒪_X`-module `F`
has zero stalks outside `S`, then `F ≅ ⨁_{x ∈ S} x_*(F_x)`, through the units of the
stalk–skyscraper adjunctions. -/
noncomputable def moduleSheafIsoBiproductSkyscraper (hS : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hF : ∀ y ∉ S, Subsingleton ((moduleStalkFunctor y).obj F)) :
    F ≅ ⨁ fun x : S => (moduleSkyscraper x.1).obj ((moduleStalkFunctor x.1).obj F) :=
  haveI := isIso_toBiproductModuleSkyscraper F S hS hF
  asIso (toBiproductModuleSkyscraper F S)

theorem moduleSheafIsoBiproductSkyscraper_hom (hS : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hF : ∀ y ∉ S, Subsingleton ((moduleStalkFunctor y).obj F)) :
    (moduleSheafIsoBiproductSkyscraper F S hS hF).hom = toBiproductModuleSkyscraper F S :=
  rfl

end Ringed

end Hartshorne
