/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ModuleSheavesEnoughInjectives
import Hartshorne.RingedSpace.ModuleSheafHomLeftExact
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# The sheaves `ℰxt`

Hartshorne, *Algebraic Geometry*, III.6 (p. 233).

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`. The category of `𝒪_X`-modules is abelian and has enough injectives
(`Hartshorne.moduleSheaves_enoughInjectives`), so it has injective resolutions. For an
`𝒪_X`-module `F`, the sheaf Hom functor `ℋom(F, -)` (`Hartshorne.Ringed.moduleSheafHomFunctor`) is
additive, and we define the `𝒪_X`-module `ℰxtⁿ(F, G)` as its `n`-th right derived functor applied
to `G` (`Hartshorne.Ringed.sheafExt`).

For an injective resolution `G ⟶ I^•`, `ℰxtⁿ(F, G)` is identified with the degree-`n` cohomology
sheaf of the complex `ℋom(F, I^•)` (`Hartshorne.Ringed.sheafExtIsoHomology`), naturally with
respect to morphisms `G ⟶ G'` and chain maps of injective resolutions lying over them
(`Hartshorne.Ringed.sheafExtIsoHomology_hom_naturality`).
-/

universe u

open CategoryTheory

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The `𝒪_X`-modules on a ringed space form an abelian category. This is Mathlib's instance
`SheafOfModules.instAbelian`, recorded as a single constant: the Mathlib instance term carries large
proofs of its sheafification hypotheses, which the kernel would otherwise re-check in every
declaration mentioning the abelian structure. -/
noncomputable instance sheafOfModules_abelian : Abelian (SheafOfModules.{u} (ringCatSheafOf R)) :=
  inferInstance

/- Mathlib's derived-functor API takes the preadditive structure of an abelian category from its
`Abelian` instance; the statements below are elaborated with that same structure, rather than the
definitionally equal one that `SheafOfModules` carries directly, so that the kernel can match them
with Mathlib's lemmas without unfolding the abelian structure. -/
attribute [local instance 2000] Abelian.toPreadditive

/-- The `𝒪_X`-modules on a ringed space have enough injectives (Hartshorne III.2,
Proposition 2.2); together with the abelian structure this provides injective resolutions. -/
instance sheafOfModules_enoughInjectives :
    EnoughInjectives (SheafOfModules.{u} (ringCatSheafOf R)) :=
  moduleSheaves_enoughInjectives X (ringCatSheafOf R)

/-- **The sheaf Ext functor** `ℰxtⁿ(F, -)` (Hartshorne III.6, p. 233). For an `𝒪_X`-module `F`,
`ℰxtⁿ(F, -)` is the `n`-th right derived functor of the sheaf Hom functor `ℋom(F, -)` on the
category of `𝒪_X`-modules; its value at `G` is the `𝒪_X`-module `ℰxtⁿ(F, G)`. -/
noncomputable def sheafExt (F : SheafOfModules.{u} (ringCatSheafOf R)) (n : ℕ) :
    SheafOfModules.{u} (ringCatSheafOf R) ⥤ SheafOfModules.{u} (ringCatSheafOf R) :=
  (moduleSheafHomFunctor F).rightDerived n

lemma sheafExt_eq (F : SheafOfModules.{u} (ringCatSheafOf R)) (n : ℕ) :
    sheafExt F n = (moduleSheafHomFunctor F).rightDerived n := rfl

/-- **`ℰxt` from an injective resolution** (Hartshorne III.6, p. 233). For an injective resolution
`G ⟶ I^•`, the `𝒪_X`-module `ℰxtⁿ(F, G)` is isomorphic to the degree-`n` cohomology sheaf of the
complex `ℋom(F, I^•)`. -/
noncomputable def sheafExtIsoHomology (F : SheafOfModules.{u} (ringCatSheafOf R))
    {G : SheafOfModules.{u} (ringCatSheafOf R)} (I : InjectiveResolution G) (n : ℕ) :
    (sheafExt F n).obj G ≅ (HomologicalComplex.homologyFunctor _ _ n).obj
        (((moduleSheafHomFunctor F).mapHomologicalComplex _).obj I.cocomplex) :=
  I.isoRightDerivedObj (moduleSheafHomFunctor F) n

/-- Naturality of the identification, for any functor `E` equal to `R^n ℋom(F, -)` and any
isomorphisms heterogeneously equal to Mathlib's. Applied with `E := ℰxtⁿ(F, -)`, it lets the kernel
match the statement below with Mathlib's lemma after substitution; comparing `ℰxtⁿ(F, -)` with the
derived functor inside `Functor.map` directly makes the kernel check several times slower. -/
private theorem hom_naturality_of_eq (F : SheafOfModules.{u} (ringCatSheafOf R)) (n : ℕ) (E : SheafOfModules.{u} (ringCatSheafOf R) ⥤ SheafOfModules.{u} (ringCatSheafOf R))
    (hE : (moduleSheafHomFunctor F).rightDerived n = E) {G G' : SheafOfModules.{u} (ringCatSheafOf R)} (f : G ⟶ G')
    (I : InjectiveResolution G) (J : InjectiveResolution G') (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (eI : E.obj G ≅ (HomologicalComplex.homologyFunctor _ _ n).obj
        (((moduleSheafHomFunctor F).mapHomologicalComplex _).obj I.cocomplex))
    (eJ : E.obj G' ≅ (HomologicalComplex.homologyFunctor _ _ n).obj
        (((moduleSheafHomFunctor F).mapHomologicalComplex _).obj J.cocomplex))
    (hI : HEq eI (I.isoRightDerivedObj (moduleSheafHomFunctor F) n))
    (hJ : HEq eJ (J.isoRightDerivedObj (moduleSheafHomFunctor F) n)) :
    E.map f ≫ eJ.hom = eI.hom ≫
      ((moduleSheafHomFunctor F).mapHomologicalComplex _ ⋙
        HomologicalComplex.homologyFunctor _ _ n).map φ := by
  subst hE
  obtain rfl := eq_of_heq hI
  obtain rfl := eq_of_heq hJ
  exact InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm _ n

/-- **Naturality of the identification of `ℰxt`** with the cohomology of `ℋom(F, I^•)`. For a
morphism `f : G ⟶ G'`, injective resolutions `G ⟶ I^•` and `G' ⟶ J^•`, and a chain map
`φ : I^• ⟶ J^•` lying over `f`, the map `ℰxtⁿ(F, f)` corresponds to the map induced by
`ℋom(F, φ)` on degree-`n` cohomology sheaves. -/
theorem sheafExtIsoHomology_hom_naturality (F : SheafOfModules.{u} (ringCatSheafOf R))
    {G G' : SheafOfModules.{u} (ringCatSheafOf R)} (f : G ⟶ G') (I : InjectiveResolution G)
    (J : InjectiveResolution G') (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    (sheafExt F n).map f ≫ (sheafExtIsoHomology F J n).hom =
      (sheafExtIsoHomology F I n).hom ≫
        ((moduleSheafHomFunctor F).mapHomologicalComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ n).map φ :=
  hom_naturality_of_eq F n (sheafExt F n) (sheafExt_eq F n).symm f I J φ comm
    (sheafExtIsoHomology F I n) (sheafExtIsoHomology F J n) HEq.rfl HEq.rfl

end Ringed

end Hartshorne
