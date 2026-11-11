/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleGluing
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Gluing sheaves of modules on a scheme

The scheme form of `Hartshorne.ModuleGluing.GluingData.exists_unique_gluing` (the ringed-space
gluing of sheaves of modules, applied to `(X, 𝒪_X)`): gluing data whose pieces are
`𝒪_{U i}`-modules `F i : (U i).Modules` and whose transition isomorphisms are isomorphisms of
`𝒪_{U i ∩ U j}`-modules between restrictions along open immersions
(`Scheme.Modules.restrictFunctor`). It is deduced from the ringed-space theorem for
`X.ringCatSheaf` by transport along Mathlib's equivalences
`Scheme.Modules.overEquiv U : SheafOfModules (X.ringCatSheaf.over U) ≌ U.Modules`.

## Main results

* `Hartshorne.ModuleGluing.SchemeGluingData`: gluing data in `Scheme.Modules` form.
* `Hartshorne.ModuleGluing.SchemeGluingData.Compatible`: compatibility of restrictions
  `ψ i : F|_{U i} ≅ F i` with the transition isomorphisms.
* `Hartshorne.ModuleGluing.SchemeGluingData.exists_unique_gluing`: there is an `𝒪_X`-module `F`
  with compatible isomorphisms `ψ i : F|_{U i} ≅ F i`, unique up to a unique isomorphism
  compatible with the `ψ i`.

## Proof outline

* `resOverEquivIso h M` (Mathlib's `Scheme.Modules.overMapCompOverEquiv`) compares restricting an
  `𝒪_X|_W`-module to `V ≤ W` before and after `overEquiv`. `resOverEquivIso_trans` is its
  compatibility with `T ≤ V ≤ W`, and `restrictInfIso_eq` is the analogous compatibility of
  Mathlib's `overFunctorEquiv` with `overFunctorMap` and `SchemeGluingData.restrictInfIso`. Both
  are checked on sections, where every map is a restriction map of the underlying module (thin
  categories). The definitional unfolding of sections through `overEquiv` is done one step at a
  time (`secRes₂`); a single-step check is very slow.
* `SchemeGluingData.toGluingData` transports the data to `X.ringCatSheaf`: the pieces are
  `(overEquiv (U i)).inverse.obj (F i)` and the transition isomorphisms are preimages under the
  fully faithful `(overEquiv _).functor` (`transportIso`); the cocycle condition follows from
  `map_restrictIso_transportIso_hom`.
* `ofOverIso` / `toOverIso` translate identifications `F|_{U i} ≅ F i` between the two forms;
  `toGluingData_compatible_iff` and `ofOverIso_mapIso` translate compatibility and the uniqueness
  condition.
-/

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry Scheme.Modules

namespace Hartshorne

namespace ModuleGluing

variable {X : Scheme.{u}}

/-- Restriction along `X.homOfLE (T ≤ V ≤ W)` in one step is restriction in two steps. -/
noncomputable def restrictHomOfLETrans {T V W : X.Opens} (hT : T ≤ V) (hW : V ≤ W) :
    restrictFunctor (X.homOfLE (hT.trans hW)) ≅
      restrictFunctor (X.homOfLE hW) ⋙ restrictFunctor (X.homOfLE hT) :=
  restrictFunctorCongr (X.homOfLE_homOfLE hT hW).symm ≪≫ restrictFunctorComp _ _

/-- An isomorphism between restrictions to `V`, restricted further to `T ≤ V`. -/
noncomputable def restrictIsoHomOfLE {T V W W' : X.Opens} (hT : T ≤ V) {hW : V ≤ W}
    {hW' : V ≤ W'} {G : W.toScheme.Modules} {G' : W'.toScheme.Modules}
    (α : G.restrict (X.homOfLE hW) ≅ G'.restrict (X.homOfLE hW')) :
    G.restrict (X.homOfLE (hT.trans hW)) ≅ G'.restrict (X.homOfLE (hT.trans hW')) :=
  (restrictHomOfLETrans hT hW).app G ≪≫ (restrictFunctor (X.homOfLE hT)).mapIso α ≪≫
    ((restrictHomOfLETrans hT hW').app G').symm

variable (X) in
/-- Gluing data for sheaves of modules on a scheme `X`, in `Scheme.Modules` form: an open cover `U`
of `X`, an `𝒪_{U i}`-module `F i` for each `i`, and isomorphisms `φ i j` between the restrictions
of `F i` and `F j` to `U i ⊓ U j`, satisfying the identity and cocycle conditions. -/
structure SchemeGluingData where
  /-- The index type of the cover. -/
  ι : Type u
  /-- The open cover. -/
  U : ι → X.Opens
  /-- The `U i` cover `X`. -/
  iSup_eq_top : iSup U = ⊤
  /-- An `𝒪_{U i}`-module on each open of the cover. -/
  F : ∀ i, (U i).toScheme.Modules
  /-- The gluing isomorphisms `F i |(U i ⊓ U j) ≅ F j |(U i ⊓ U j)`. -/
  φ : ∀ i j, (F i).restrict (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ≅
    (F j).restrict (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))
  /-- The identity condition `φ i i = id`. -/
  φ_self : ∀ i, (φ i i).hom = 𝟙 _
  /-- The cocycle condition `φ i k = φ j k ∘ φ i j` on `U i ⊓ U j ⊓ U k`. -/
  cocycle : ∀ i j k,
    restrictIsoHomOfLE (T := U i ⊓ U j ⊓ U k) inf_le_left (φ i j) ≪≫
      restrictIsoHomOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (φ j k) =
    restrictIsoHomOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (φ i k)

namespace SchemeGluingData

variable (E : SchemeGluingData X)

/-- Restricting an `𝒪_X`-module to `U i ⊓ U j` directly or through `U i`. -/
noncomputable def restrictInfIso (F : X.Modules) {V W : X.Opens} (h : V ≤ W) :
    F.restrict V.ι ≅ (F.restrict W.ι).restrict (X.homOfLE h) :=
  (restrictFunctorCongr (X.homOfLE_ι h)).symm.app F ≪≫ (restrictFunctorComp _ _).app F

/-- A family of isomorphisms `ψ i : F|_{U i} ≅ F i` is compatible with the gluing isomorphisms
when `ψ j = φ i j ∘ ψ i` on `U i ⊓ U j`. -/
def Compatible (F : X.Modules) (ψ : ∀ i, F.restrict (E.U i).ι ≅ E.F i) : Prop :=
  ∀ i j, restrictInfIso F (inf_le_left : E.U i ⊓ E.U j ≤ E.U i) ≪≫
      (restrictFunctor (X.homOfLE inf_le_left)).mapIso (ψ i) ≪≫ E.φ i j =
    restrictInfIso F (inf_le_right : E.U i ⊓ E.U j ≤ E.U j) ≪≫
      (restrictFunctor (X.homOfLE inf_le_right)).mapIso (ψ j)

end SchemeGluingData

/-- For `V ≤ W` and an `𝒪_X|_W`-module `M` (a module over `X.ringCatSheaf.over W`), restricting
`M` to `V` and passing to `V.Modules` agrees with passing to `W.Modules` and restricting along
`V ⟶ W` (Mathlib's `Scheme.Modules.overMapCompOverEquiv`). -/
noncomputable abbrev resOverEquivIso {V W : X.Opens} (h : V ≤ W)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over W)) :
    (overEquiv V).functor.obj ((res X.ringCatSheaf h).obj M) ≅
      ((overEquiv W).functor.obj M).restrict (X.homOfLE h) :=
  (overMapCompOverEquiv (X := X) (homOfLE h)).app M

/-! ### Sections of the comparison isomorphisms

On sections, each comparison isomorphism is a restriction map of the underlying module; since
`Over W` and `Opens X` are thin, such maps are determined by their source and target. The section
lemmas below go through `secRes₂`, which moves a section along the definitional equalities one
step at a time; checking the composite definitional equality in a single step is very slow. -/

instance subsingleton_overOp_hom {W : X.Opens} (A B : (Over W)ᵒᵖ) : Subsingleton (A ⟶ B) :=
  ⟨fun _ _ ↦ Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))⟩

open Opposite

/-- Four restriction maps of a module over `𝒪_X|_W` compose to any restriction map with the same
source and target. -/
theorem map_map_map_map_eq {W : X.Opens} (M : SheafOfModules.{u} (X.ringCatSheaf.over W))
    {A B C D E : (Over W)ᵒᵖ} (g1 : A ⟶ B) (g2 : B ⟶ C) (g3 : C ⟶ D) (g4 : D ⟶ E) (g : A ⟶ E)
    (y : M.val.obj A) :
    M.val.map g4 (M.val.map g3 (M.val.map g2 (M.val.map g1 y))) = M.val.map g y := by
  rw [← M.val.map_comp_apply, ← M.val.map_comp_apply, ← M.val.map_comp_apply]
  exact M.val.congr_map_apply (Subsingleton.elim _ _) _

/-- Sections over `W'` of the restriction of `M` to `T ≤ V ≤ W` in two steps, as sections of `M`. -/
def secRes₂ {T V W : X.Opens} (h1 : T ≤ V) (h2 : V ≤ W)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over W)) (W' : T.toScheme.Opens)
    (y : Γ((overEquiv T).functor.obj ((res X.ringCatSheaf h1).obj ((res X.ringCatSheaf h2).obj M)),
      W')) :
    M.val.obj (op ((Over.map (homOfLE h2)).obj ((Over.map (homOfLE h1)).obj
        ((Opens.overEquivalence T).inverse.obj W')))) :=
  let y₁ : ((res X.ringCatSheaf h1).obj ((res X.ringCatSheaf h2).obj M)).val.obj
      (op ((Opens.overEquivalence T).inverse.obj W')) := y
  let y₂ : ((res X.ringCatSheaf h2).obj M).val.obj
      (op ((Over.map (homOfLE h1)).obj ((Opens.overEquivalence T).inverse.obj W'))) := y₁
  y₂

set_option backward.isDefEq.respectTransparency false in
/-- On sections over `W'`, the composite comparison for `T ≤ V ≤ W` (restrict in two steps, then
reassociate the restriction functors) is a composite of four restriction maps of `M`. -/
theorem exists_resOverEquivIso_trans_lhs_app_eq_map {T V W : X.Opens} (h1 : T ≤ V) (h2 : V ≤ W)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over W)) (W' : T.toScheme.Opens) :
    ∃ (C : (Over W)ᵒᵖ)
      (g1 : op ((Over.map (homOfLE h2)).obj ((Over.map (homOfLE h1)).obj
        ((Opens.overEquivalence T).inverse.obj W'))) ⟶
        op ((Over.map (homOfLE h2)).obj ((Opens.overEquivalence V).inverse.obj
          ((X.homOfLE h1) ''ᵁ W'))))
      (g2 : op ((Over.map (homOfLE h2)).obj ((Opens.overEquivalence V).inverse.obj
          ((X.homOfLE h1) ''ᵁ W'))) ⟶
        op ((Opens.overEquivalence W).inverse.obj ((X.homOfLE h2) ''ᵁ ((X.homOfLE h1) ''ᵁ W'))))
      (g3 : op ((Opens.overEquivalence W).inverse.obj
          ((X.homOfLE h2) ''ᵁ ((X.homOfLE h1) ''ᵁ W'))) ⟶ C)
      (g4 : C ⟶ op ((Opens.overEquivalence W).inverse.obj ((X.homOfLE (le_trans h1 h2)) ''ᵁ W'))),
      ∀ y, ((resOverEquivIso h1 ((res X.ringCatSheaf h2).obj M)).hom ≫
        (restrictFunctor (X.homOfLE h1)).map (resOverEquivIso h2 M).hom ≫
        ((restrictHomOfLETrans h1 h2).app _).inv).app W' y =
        M.val.map g4 (M.val.map g3 (M.val.map g2 (M.val.map g1 (secRes₂ h1 h2 M W' y)))) :=
  ⟨_, _, _, _, _, fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- On sections over `W'`, restricting along `T ≤ W` in one step (after `resComp`) is a
restriction map of `M`. The section map is passed as `f` with its source written as
`(res h1).obj ((res h2).obj M)`, so that it matches the form produced by `hom_ext`. -/
theorem exists_resOverEquivIso_trans_rhs_app_eq_map {T V W : X.Opens} (h1 : T ≤ V) (h2 : V ≤ W)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over W)) (W' : T.toScheme.Opens)
    (f : Γ((overEquiv T).functor.obj ((res X.ringCatSheaf h1).obj ((res X.ringCatSheaf h2).obj M)),
        W') ⟶
      Γ((restrictFunctor (X.homOfLE (le_trans h1 h2))).obj ((overEquiv W).functor.obj M), W'))
    (hf : f = Hom.app ((overEquiv T).functor.map ((resComp X.ringCatSheaf h1 h2).app M).hom ≫
        (resOverEquivIso (le_trans h1 h2) M).hom) W') :
    ∃ g : op ((Over.map (homOfLE h2)).obj ((Over.map (homOfLE h1)).obj
        ((Opens.overEquivalence T).inverse.obj W'))) ⟶
        op ((Opens.overEquivalence W).inverse.obj ((X.homOfLE (le_trans h1 h2)) ''ᵁ W')),
      ∀ y, f y = M.val.map g (secRes₂ h1 h2 M W' y) := by
  subst hf
  exact ⟨_, fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- `resOverEquivIso` is compatible with restricting along `T ≤ V ≤ W` in two steps. -/
theorem resOverEquivIso_trans {T V W : X.Opens} (h1 : T ≤ V) (h2 : V ≤ W)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over W)) :
    (resOverEquivIso h1 ((res X.ringCatSheaf h2).obj M)).hom ≫
      (restrictFunctor (X.homOfLE h1)).map (resOverEquivIso h2 M).hom ≫
      ((restrictHomOfLETrans h1 h2).app _).inv =
    (overEquiv T).functor.map ((resComp X.ringCatSheaf h1 h2).app M).hom ≫
      (resOverEquivIso (le_trans h1 h2) M).hom := by
  apply Scheme.Modules.hom_ext
  intro W'
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  obtain ⟨C, g1, g2, g3, g4, hL⟩ := exists_resOverEquivIso_trans_lhs_app_eq_map h1 h2 M W'
  obtain ⟨g, hR⟩ := exists_resOverEquivIso_trans_rhs_app_eq_map h1 h2 M W' _ rfl
  exact (hL x).trans ((map_map_map_map_eq M g1 g2 g3 g4 g _).trans (hR x).symm)

/-- Restriction maps of an `𝒪_X`-module, read on the underlying presheaf. -/
theorem presheaf_map_eq_val_map (F : X.Modules) {A B : (TopologicalSpace.Opens X)ᵒᵖ}
    (g : A ⟶ B) (y : F.presheaf.obj A) : F.presheaf.map g y = F.val.map g y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On sections over `W'`, `restrictInfIso F h` is a restriction map of `F`. -/
theorem exists_restrictInfIso_hom_app_eq_map {V W : X.Opens} (h : V ≤ W) (F : X.Modules)
    (W' : V.toScheme.Opens) :
    ∃ g : op (V.ι ''ᵁ W') ⟶ op (W.ι ''ᵁ (X.homOfLE h ''ᵁ W')),
      ∀ y, (SchemeGluingData.restrictInfIso F h).hom.app W' y = F.presheaf.map g y := by
  refine ⟨(homOfLE (le_of_eq (by simp [← Scheme.Hom.comp_image]))).op, fun y ↦ ?_⟩
  simp only [SchemeGluingData.restrictInfIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Hom.comp_app, restrictFunctorCongr_inv_app_app, restrictFunctorComp_hom_app_app]
  rw [← Functor.map_comp]
  exact ConcreteCategory.congr_hom (congrArg F.presheaf.map (Subsingleton.elim _ _)) y

set_option backward.isDefEq.respectTransparency false in
/-- On sections over `W'`, the description of `restrictInfIso F h` through `overEquiv` is a
restriction map of `F`. -/
theorem exists_restrictInfIso_overEquiv_app_eq_map {V W : X.Opens} (h : V ≤ W) (F : X.Modules)
    (W' : V.toScheme.Opens) :
    ∃ (g1 : op (V.ι ''ᵁ W') ⟶ op (W.ι ''ᵁ (X.homOfLE h ''ᵁ W'))),
      ∀ y, (((overFunctorEquiv V).app F).inv ≫ (overEquiv V).functor.map
        ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app F).inv ≫
        (resOverEquivIso h ((SheafOfModules.overFunctor X.ringCatSheaf W).obj F)).hom ≫
        (restrictFunctor (X.homOfLE h)).map ((overFunctorEquiv W).app F).hom).app W' y =
        F.val.map g1 y :=
  ⟨_, fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- `restrictInfIso` through `overEquiv`: restricting an `𝒪_X`-module to `V ≤ W` directly or
through `W` agrees with Mathlib's `overFunctorMap` under `overFunctorEquiv` and
`resOverEquivIso`. -/
theorem restrictInfIso_eq {V W : X.Opens} (h : V ≤ W) (F : X.Modules) :
    (SchemeGluingData.restrictInfIso F h).hom = ((overFunctorEquiv V).app F).inv ≫
      (overEquiv V).functor.map
        ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app F).inv ≫
      (resOverEquivIso h ((SheafOfModules.overFunctor X.ringCatSheaf W).obj F)).hom ≫
      (restrictFunctor (X.homOfLE h)).map ((overFunctorEquiv W).app F).hom := by
  apply Scheme.Modules.hom_ext
  intro W'
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  obtain ⟨g, hL⟩ := exists_restrictInfIso_hom_app_eq_map h F W'
  obtain ⟨g', hR⟩ := exists_restrictInfIso_overEquiv_app_eq_map h F W'
  exact (hL x).trans
    (((ConcreteCategory.congr_hom (congrArg F.presheaf.map (Subsingleton.elim g g')) x).trans
    (presheaf_map_eq_val_map F g' x)).trans (hR x).symm)
/-! ### Transport to ringed-space gluing data -/

/-- Naturality of `resOverEquivIso`. -/
@[reassoc]
theorem resOverEquivIso_naturality {V W : X.Opens} (h : V ≤ W)
    {M N : SheafOfModules.{u} (X.ringCatSheaf.over W)} (a : M ⟶ N) :
    (overEquiv V).functor.map ((res X.ringCatSheaf h).map a) ≫ (resOverEquivIso h N).hom =
      (resOverEquivIso h M).hom ≫
        (restrictFunctor (X.homOfLE h)).map ((overEquiv W).functor.map a) :=
  (overMapCompOverEquiv (X := X) (homOfLE h)).hom.naturality a

theorem map_res_map_eq {V W : X.Opens} (h : V ≤ W)
    {M N : SheafOfModules.{u} (X.ringCatSheaf.over W)} (a : M ⟶ N) :
    (overEquiv V).functor.map ((res X.ringCatSheaf h).map a) = (resOverEquivIso h M).hom ≫
      (restrictFunctor (X.homOfLE h)).map ((overEquiv W).functor.map a) ≫
        (resOverEquivIso h N).inv := by
  rw [← resOverEquivIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The comparison `t_h(G)` for an `𝒪_W`-module `G`. -/
noncomputable def transIso {V W : X.Opens} (h : V ≤ W) (G : W.toScheme.Modules) :
    (overEquiv V).functor.obj ((res X.ringCatSheaf h).obj ((overEquiv W).inverse.obj G)) ≅
      G.restrict (X.homOfLE h) :=
  resOverEquivIso h _ ≪≫ (restrictFunctor (X.homOfLE h)).mapIso ((overEquiv W).counitIso.app G)

theorem transIso_trans {T V W : X.Opens} (hT : T ≤ V) (hW : V ≤ W) (G : W.toScheme.Modules) :
    (overEquiv T).functor.map
        ((resComp X.ringCatSheaf hT hW).app ((overEquiv W).inverse.obj G)).inv ≫
      (resOverEquivIso hT ((res X.ringCatSheaf hW).obj ((overEquiv W).inverse.obj G))).hom ≫
      (restrictFunctor (X.homOfLE hT)).map (transIso hW G).hom =
    (transIso (hT.trans hW) G).hom ≫ ((restrictHomOfLETrans hT hW).app G).hom := by
  have key := resOverEquivIso_trans hT hW ((overEquiv W).inverse.obj G)
  rw [← cancel_mono ((restrictHomOfLETrans hT hW).app _).hom] at key
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at key
  simp only [transIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  rw [reassoc_of% key, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc]
  congr 1
  exact ((restrictHomOfLETrans hT hW).hom.naturality _).symm

/-- `transIso_trans` as an equation of isomorphisms. -/
theorem transIso_trans_iso {T V W : X.Opens} (hT : T ≤ V) (hW : V ≤ W) (G : W.toScheme.Modules) :
    (overEquiv T).functor.mapIso
        ((resComp X.ringCatSheaf hT hW).app ((overEquiv W).inverse.obj G)).symm ≪≫
      resOverEquivIso hT ((res X.ringCatSheaf hW).obj ((overEquiv W).inverse.obj G)) ≪≫
      (restrictFunctor (X.homOfLE hT)).mapIso (transIso hW G) =
    transIso (hT.trans hW) G ≪≫ (restrictHomOfLETrans hT hW).app G :=
  Iso.ext (transIso_trans hT hW G)

/-- An isomorphism between restrictions of `𝒪_W`- and `𝒪_{W'}`-modules to `V`, transported to
an isomorphism of `𝒪_X|_V`-modules. -/
noncomputable def transportIso {V W W' : X.Opens} {hW : V ≤ W} {hW' : V ≤ W'}
    {G : W.toScheme.Modules} {G' : W'.toScheme.Modules}
    (β : G.restrict (X.homOfLE hW) ≅ G'.restrict (X.homOfLE hW')) :
    (res X.ringCatSheaf hW).obj ((overEquiv W).inverse.obj G) ≅
      (res X.ringCatSheaf hW').obj ((overEquiv W').inverse.obj G') :=
  (overEquiv V).functor.preimageIso (transIso hW G ≪≫ β ≪≫ (transIso hW' G').symm)

theorem map_transportIso_hom {V W W' : X.Opens} {hW : V ≤ W} {hW' : V ≤ W'}
    {G : W.toScheme.Modules} {G' : W'.toScheme.Modules}
    (β : G.restrict (X.homOfLE hW) ≅ G'.restrict (X.homOfLE hW')) :
    (overEquiv V).functor.map (transportIso β).hom =
      (transIso hW G).hom ≫ β.hom ≫ (transIso hW' G').inv := by
  simp [transportIso]

theorem map_restrictIso_transportIso_hom {T V W W' : X.Opens} (hT : T ≤ V) {hW : V ≤ W}
    {hW' : V ≤ W'} {G : W.toScheme.Modules} {G' : W'.toScheme.Modules}
    (β : G.restrict (X.homOfLE hW) ≅ G'.restrict (X.homOfLE hW')) :
    (overEquiv T).functor.map (restrictIso hT (transportIso β)).hom =
      (transIso (hT.trans hW) G).hom ≫ (restrictIsoHomOfLE hT β).hom ≫
        (transIso (hT.trans hW') G').inv := by
  have h1 := congrArg Iso.hom (transIso_trans_iso hT hW G)
  have h2 := congrArg Iso.inv (transIso_trans_iso hT hW' G')
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom,
    Iso.symm_inv, Category.assoc] at h1 h2
  simp only [restrictIso, restrictIsoHomOfLE, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [map_res_map_eq, map_transportIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, h2]

namespace SchemeGluingData

variable (E : SchemeGluingData X)

/-- The ringed-space gluing data on `(X, 𝒪_X)` corresponding to scheme gluing data. -/
noncomputable def toGluingData : GluingData X X.ringCatSheaf where
  ι := E.ι
  U := E.U
  iSup_eq_top := E.iSup_eq_top
  F i := (overEquiv (E.U i)).inverse.obj (E.F i)
  φ i j := transportIso (E.φ i j)
  φ_self i := by
    apply (overEquiv _).functor.map_injective
    rw [map_transportIso_hom, E.φ_self, Category.id_comp, CategoryTheory.Functor.map_id]
    exact Iso.hom_inv_id _
  cocycle i j k := by
    ext1
    apply (overEquiv _).functor.map_injective
    rw [Iso.trans_hom, Functor.map_comp, map_restrictIso_transportIso_hom,
      map_restrictIso_transportIso_hom, map_restrictIso_transportIso_hom, Category.assoc,
      Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc (restrictIsoHomOfLE _ _).hom,
      ← Iso.trans_hom, E.cocycle i j k]

end SchemeGluingData

/-- An isomorphism `F|_U ≅ e⁻¹ G` of `𝒪_X|_U`-modules, transported to an isomorphism
`F|_U ≅ G` of `𝒪_U`-modules. -/
noncomputable def ofOverIso {U : X.Opens} (F : X.Modules) (G : U.toScheme.Modules)
    (α : (SheafOfModules.overFunctor X.ringCatSheaf U).obj F ≅ (overEquiv U).inverse.obj G) :
    F.restrict U.ι ≅ G :=
  ((overFunctorEquiv U).app F).symm ≪≫ (overEquiv U).functor.mapIso α ≪≫
    (overEquiv U).counitIso.app G

/-- The inverse of `ofOverIso`. -/
noncomputable def toOverIso {U : X.Opens} (F : X.Modules) (G : U.toScheme.Modules)
    (β : F.restrict U.ι ≅ G) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).obj F ≅ (overEquiv U).inverse.obj G :=
  (overEquiv U).functor.preimageIso
    ((overFunctorEquiv U).app F ≪≫ β ≪≫ ((overEquiv U).counitIso.app G).symm)

theorem ofOverIso_toOverIso {U : X.Opens} (F : X.Modules) (G : U.toScheme.Modules)
    (β : F.restrict U.ι ≅ G) : ofOverIso F G (toOverIso F G β) = β := by
  ext1
  simp [ofOverIso, toOverIso]

theorem ofOverIso_injective {U : X.Opens} (F : X.Modules) (G : U.toScheme.Modules) :
    Function.Injective (ofOverIso F G) := by
  intro α α' h
  ext1
  apply (overEquiv U).functor.map_injective
  have h' := congrArg Iso.hom h
  simp only [ofOverIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, cancel_epi] at h'
  rwa [cancel_mono] at h'

theorem ofOverIso_mapIso {U : X.Opens} {F F' : X.Modules} (G : U.toScheme.Modules) (θ : F' ≅ F)
    (α : (SheafOfModules.overFunctor X.ringCatSheaf U).obj F ≅ (overEquiv U).inverse.obj G) :
    ofOverIso F' G ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso θ ≪≫ α) =
      (restrictFunctor U.ι).mapIso θ ≪≫ ofOverIso F G α := by
  have hn : (restrictFunctor U.ι).map θ.hom ≫ ((overFunctorEquiv U).app F).inv =
      ((overFunctorEquiv U).app F').inv ≫
        (overEquiv U).functor.map ((SheafOfModules.overFunctor X.ringCatSheaf U).map θ.hom) :=
    (overFunctorEquiv U).inv.naturality θ.hom
  ext1
  change ((overFunctorEquiv U).app F').inv ≫ (overEquiv U).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map θ.hom ≫ α.hom) ≫
      ((overEquiv U).counitIso.app G).hom = (restrictFunctor U.ι).map θ.hom ≫
      ((overFunctorEquiv U).app F).inv ≫ (overEquiv U).functor.map α.hom ≫
      ((overEquiv U).counitIso.app G).hom
  rw [reassoc_of% hn, Functor.map_comp, Category.assoc]

@[reassoc]
theorem map_overFunctorMap_inv_map_res {V W : X.Opens} (h : V ≤ W) (F : X.Modules)
    (G : W.toScheme.Modules)
    (α : (SheafOfModules.overFunctor X.ringCatSheaf W).obj F ≅ (overEquiv W).inverse.obj G) :
    (overEquiv V).functor.map
        ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app F).inv ≫
      (overEquiv V).functor.map ((res X.ringCatSheaf h).map α.hom) =
    ((overFunctorEquiv V).app F).hom ≫ (SchemeGluingData.restrictInfIso F h).hom ≫
      (restrictFunctor (X.homOfLE h)).map (ofOverIso F G α).hom ≫ (transIso h G).inv := by
  rw [restrictInfIso_eq, map_res_map_eq]
  simp only [ofOverIso, transIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.map_hom_inv_id_assoc]

namespace SchemeGluingData

variable (E : SchemeGluingData X)

theorem toGluingData_compatible_iff (F : X.Modules)
    (α : ∀ i, (SheafOfModules.overFunctor X.ringCatSheaf (E.U i)).obj F ≅
      (overEquiv (E.U i)).inverse.obj (E.F i)) :
    E.toGluingData.Compatible F α ↔ E.Compatible F (fun i ↦ ofOverIso F (E.F i) (α i)) := by
  refine forall₂_congr fun i j ↦ ?_
  rw [Iso.ext_iff, Iso.ext_iff]
  refine (((overEquiv (E.U i ⊓ E.U j)).functor.map_injective).eq_iff).symm.trans ?_
  change (overEquiv (E.U i ⊓ E.U j)).functor.map
      (((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE inf_le_left)).app F).inv ≫
        (res X.ringCatSheaf inf_le_left).map (α i).hom ≫ (transportIso (E.φ i j)).hom) =
    (overEquiv (E.U i ⊓ E.U j)).functor.map
      (((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE inf_le_right)).app F).inv ≫
        (res X.ringCatSheaf inf_le_right).map (α j).hom) ↔ _
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, map_transportIso_hom,
    map_overFunctorMap_inv_map_res_assoc, map_overFunctorMap_inv_map_res]
  simp only [Iso.inv_hom_id_assoc, cancel_epi, Iso.trans_hom, Functor.mapIso_hom]
  simp only [← Category.assoc, cancel_mono]

/-- **Gluing sheaves of modules on a scheme.** Given gluing data `E` for `𝒪`-modules on an open
cover of a scheme `X`, there is an `𝒪_X`-module `F` with isomorphisms `ψ i : F|_{U i} ≅ F i` of
`𝒪_{U i}`-modules such that `ψ j = φ i j ∘ ψ i` on `U i ⊓ U j`, and it is unique up to a unique
isomorphism compatible with these identifications. This is the case `(X, 𝒪_X)` of
`GluingData.exists_unique_gluing` (Hartshorne II, Exercise 1.22, glues sheaves; the module form is
a supplement). -/
theorem exists_unique_gluing :
    ∃ (F : X.Modules) (ψ : ∀ i, F.restrict (E.U i).ι ≅ E.F i), E.Compatible F ψ ∧
      ∀ (G : X.Modules) (ψ' : ∀ i, G.restrict (E.U i).ι ≅ E.F i), E.Compatible G ψ' →
        ∃! θ : G ≅ F, ∀ i, (restrictFunctor (E.U i).ι).mapIso θ ≪≫ ψ i = ψ' i := by
  obtain ⟨F, α, hα, huniq⟩ := E.toGluingData.exists_unique_gluing
  refine ⟨F, fun i ↦ ofOverIso F (E.F i) (α i), (E.toGluingData_compatible_iff F α).1 hα,
    fun G ψ' hψ' ↦ ?_⟩
  have hD : E.toGluingData.Compatible G fun i ↦ toOverIso G (E.F i) (ψ' i) :=
    (E.toGluingData_compatible_iff G _).2 (by simpa only [ofOverIso_toOverIso] using hψ')
  obtain ⟨θ, hθ, hθu⟩ := huniq G _ hD
  refine ⟨θ, fun i ↦ ?_, fun θ' h' ↦ hθu θ' fun i ↦ ?_⟩
  · exact (ofOverIso_mapIso _ θ (α i)).symm.trans
      ((congrArg (ofOverIso G (E.F i)) (hθ i)).trans (ofOverIso_toOverIso G (E.F i) (ψ' i)))
  · refine ofOverIso_injective G (E.F i) ?_
    exact (ofOverIso_mapIso _ θ' (α i)).trans
      ((h' i).trans (ofOverIso_toOverIso G (E.F i) (ψ' i)).symm)

end SchemeGluingData
end ModuleGluing

end Hartshorne
