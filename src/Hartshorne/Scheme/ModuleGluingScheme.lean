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
scheme form of the gluing theorem) is not yet proved, and this module is not imported by the
library root.

* `Hartshorne.ModuleGluing.SchemeGluingData`: gluing data in `Scheme.Modules` form.
* `Hartshorne.ModuleGluing.SchemeGluingData.Compatible`: compatibility of restrictions
  `ψ i : F|_{U i} ≅ F i` with the transition isomorphisms.
* `Hartshorne.ModuleGluing.resOverEquivIso`: for `V ≤ W` and an `𝒪_X|_W`-module `M`, the
  comparison between restricting `M` to `V` and then passing to `V.Modules`, and passing to
  `W.Modules` and then restricting along `V ⟶ W` (Mathlib's `Scheme.Modules.overMapCompOverEquiv`).
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

end ModuleGluing

end Hartshorne
