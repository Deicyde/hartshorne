/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleGluing
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Gluing data for sheaves of modules on a scheme (work in progress)

The scheme form of `Hartshorne.ModuleGluing.GluingData.exists_unique_gluing`: gluing data whose
pieces are `𝒪_{U i}`-modules `F i : (U i).Modules` and whose transition isomorphisms are
isomorphisms of `𝒪_{U i ∩ U j}`-modules between restrictions along open immersions
(`Scheme.Modules.restrictFunctor`).

This module records the data and the comparison isomorphisms used to transport it to the
ringed-space gluing data through Mathlib's `Scheme.Modules.overEquiv`; the transport (and hence the
scheme form of the gluing theorem) is not yet proved (see Status below).

* `Hartshorne.ModuleGluing.SchemeGluingData`: gluing data in `Scheme.Modules` form.
* `Hartshorne.ModuleGluing.SchemeGluingData.Compatible`: compatibility of restrictions
  `ψ i : F|_{U i} ≅ F i` with the transition isomorphisms.
* `Hartshorne.ModuleGluing.resOverEquivIso`: for `V ≤ W` and an `𝒪_X|_W`-module `M`, the
  comparison between restricting `M` to `V` and then passing to `V.Modules`, and passing to
  `W.Modules` and then restricting along `V ⟶ W` (Mathlib's `Scheme.Modules.overMapCompOverEquiv`).
* `Hartshorne.ModuleGluing.exists_resOverEquivIso_hom_app_eq_map` and companions: on sections, the
  comparison isomorphisms are restriction maps of the underlying module.

## Status

The scheme form of the gluing theorem is not yet proved. What remains, in order:

1. `resOverEquivIso_trans` (compatibility of `resOverEquivIso` with `T ≤ V ≤ W`):
   `(resOverEquivIso h1 ((res X.ringCatSheaf h2).obj M)).hom ≫
   (restrictFunctor (X.homOfLE h1)).map (resOverEquivIso h2 M).hom ≫
   ((restrictHomOfLETrans h1 h2).app _).inv =
   (overEquiv T).functor.map ((resComp X.ringCatSheaf h1 h2).app M).hom ≫
   (resOverEquivIso (le_trans h1 h2) M).hom`.
   Route: `apply Scheme.Modules.hom_ext; intro W'; refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_`
   (fast); bring in `exists_resOverEquivIso_trans_lhs_app_eq_map` with `have` and then `obtain`
   (a direct `obtain` times out); `rw [hL x]` works. The obstacle is the right-hand side: after
   `hom_ext` its section map has source `Γ((overEquiv T).functor.obj ((res h1).obj ((res h2).obj
   M)), W')`, while the composite's own type has source `Γ(… (res h2 ⋙ res h1).obj M …)`. These
   are defeq but not syntactically equal, so a lemma stated on the composite does not rewrite, and
   `erw`, `Eq.trans` with it, and type ascription time out or fail. For this reason
   `exists_resOverEquivIso_trans_rhs_app_eq_map` takes the section map as an `f` of the first
   type with `hf : f = Hom.app RHS W'`. Using it as `… _ rfl`, followed by
   `rw [hL x, hR x, ← M.val.map_comp_apply, ← M.val.map_comp_apply, ← M.val.map_comp_apply]` and
   `exact M.val.congr_map_apply (Subsingleton.elim _ _) _` (thin category `Over W`), still times
   out at 4000000 heartbeats. The failing step has not been localized; the likely candidates
   are the `_ rfl` instantiation (a defeq check of the two source types, and of
   `restrictFunctor … |>.obj` against `restrict` in the target) and the final
   `congr_map_apply`. Next step: probe each step separately with `sorry` checkpoints.
2. The analogous compatibility of `overFunctorEquiv` with `overFunctorMap` and
   `SchemeGluingData.restrictInfIso`, by the same section-level method.
3. Transport: `F i := (overEquiv (U i)).inverse.obj (E.F i)`; transition isomorphisms as preimages
   under the fully faithful `(overEquiv _).functor`; the cocycle from step 1; then apply
   `GluingData.exists_unique_gluing` and set
   `ψ i := (overFunctorEquiv (U i)).app F ≪≫ functor.mapIso (ψ' i) ≪≫ counit`, with compatibility
   and uniqueness from step 2.
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

Each comparison isomorphism acts on sections as a restriction map `M.val.map g` of the underlying
`𝒪_X|_W`-module along a morphism `g` of `(Over W)ᵒᵖ`; since `Over W` is thin, such maps are
determined by their source and target. -/

instance subsingleton_overOp_hom {W : X.Opens} (A B : (Over W)ᵒᵖ) : Subsingleton (A ⟶ B) :=
  ⟨fun _ _ ↦ Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))⟩

set_option backward.isDefEq.respectTransparency false in
/-- On sections over `W'`, `resOverEquivIso h M` is a restriction map of `M`. -/
theorem exists_resOverEquivIso_hom_app_eq_map {V W : X.Opens} (h : V ≤ W)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over W)) (W' : V.toScheme.Opens) :
    ∃ g : Opposite.op ((Over.map (homOfLE h)).obj ((Opens.overEquivalence V).inverse.obj W')) ⟶
        Opposite.op ((Opens.overEquivalence W).inverse.obj ((X.homOfLE h) ''ᵁ W')),
      ∀ y, (resOverEquivIso h M).hom.app W' y = M.val.map g y :=
  ⟨_, fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem overEquiv_map_resComp_hom_app_apply {T V W : X.Opens} (h1 : T ≤ V) (h2 : V ≤ W)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over W)) (W' : T.toScheme.Opens) (y) :
    ((overEquiv T).functor.map ((resComp X.ringCatSheaf h1 h2).app M).hom).app W' y = y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrictFunctor_homOfLE_map_app_apply {V W : X.Opens} (h : V ≤ W)
    {A B : W.toScheme.Modules} (φ : A ⟶ B) (W' : V.toScheme.Opens) (y) :
    ((restrictFunctor (X.homOfLE h)).map φ).app W' y = φ.app ((X.homOfLE h) ''ᵁ W') y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem res_val_map_apply {V W : X.Opens} (h : V ≤ W)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over W)) {A B : (Over V)ᵒᵖ} (g : A ⟶ B) (y) :
    ((res X.ringCatSheaf h).obj M).val.map g y = M.val.map ((Over.map (homOfLE h)).op.map g) y :=
  rfl

open Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
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
        M.val.map g4 (M.val.map g3 (M.val.map g2 (M.val.map g1 y))) :=
  ⟨_, _, _, _, _, fun _ ↦ rfl⟩

open Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- On sections over `W'`, restricting along `T ≤ W` in one step (after `resComp`) is a
restriction map of `M`. The section map is passed as `f` with its source written as
`(res h1).obj ((res h2).obj M)`, so that it matches the form produced by `hom_ext`. -/
theorem exists_resOverEquivIso_trans_rhs_app_eq_map {T V W : X.Opens} (h1 : T ≤ V) (h2 : V ≤ W)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over W)) (W' : T.toScheme.Opens)
    (f : Γ((overEquiv T).functor.obj ((res X.ringCatSheaf h1).obj ((res X.ringCatSheaf h2).obj M)),
        W') ⟶ Γ((restrictFunctor (X.homOfLE (le_trans h1 h2))).obj ((overEquiv W).functor.obj M), W'))
    (hf : f = Hom.app ((overEquiv T).functor.map ((resComp X.ringCatSheaf h1 h2).app M).hom ≫
        (resOverEquivIso (le_trans h1 h2) M).hom) W') :
    ∃ g : op ((Over.map (homOfLE h2)).obj ((Over.map (homOfLE h1)).obj
        ((Opens.overEquivalence T).inverse.obj W'))) ⟶
        op ((Opens.overEquivalence W).inverse.obj ((X.homOfLE (le_trans h1 h2)) ''ᵁ W')),
      ∀ y, f y = M.val.map g y := by
  subst hf
  exact ⟨_, fun _ ↦ rfl⟩

end ModuleGluing

end Hartshorne
