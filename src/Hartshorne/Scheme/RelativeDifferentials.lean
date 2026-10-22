/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.CommRingCat

/-! # The relative differential sheaf and its canonical derivation -/

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The genuine inverse-image structure sheaf on the source of a scheme morphism. -/
noncomputable def inverseImageStructureSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf

/-- The structural map from `f⁻¹𝒪_Y` to `𝒪_X`, transposed from the scheme map. -/
noncomputable def inverseImageStructureSheafMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    inverseImageStructureSheaf f ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv
    Y.sheaf X.sheaf).symm (ObjectProperty.homMk f.c)

/-- The pointwise Kähler presheaf for the actual inverse-image structural map. -/
noncomputable def relativeDifferentialsPresheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (inverseImageStructureSheafMap f).hom

/-- The relative differential sheaf, obtained by module sheafification of the Kähler presheaf. -/
noncomputable def relativeDifferentials {X Y : Scheme.{u}} (f : X ⟶ Y) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeDifferentialsPresheaf f)

/-- The canonical derivation, postcomposed with the module-sheafification unit. -/
noncomputable def relativeDifferentialsDerivation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (relativeDifferentials f).val.Derivation' (inverseImageStructureSheafMap f).hom :=
  (PresheafOfModules.DifferentialsConstruction.derivation'
    (inverseImageStructureSheafMap f).hom).postcomp
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (relativeDifferentialsPresheaf f))

/-- The relative differential sheaf together with its canonical relative derivation. -/
noncomputable def relativeDifferentialsWithDerivation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Σ M : X.Modules, M.val.Derivation' (inverseImageStructureSheafMap f).hom :=
  ⟨relativeDifferentials f, relativeDifferentialsDerivation f⟩

/-- The canonical derivation as a morphism of abelian sheaves, not of `𝒪_X`-modules. -/
noncomputable def relativeDifferentialsD {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ RingCat Ab.{u})).obj X.ringCatSheaf ⟶
        (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeDifferentials f) where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom ((relativeDifferentialsDerivation f).d (X := U))
      naturality := by
        intro U V i
        ext a
        exact (relativeDifferentialsDerivation f).d_map i a }

/-- The canonical abelian-sheaf derivation satisfies Leibniz on every open. -/
theorem relativeDifferentialsD_mul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (a b : X.presheaf.obj U) :
    ((relativeDifferentialsD f).hom.app U).hom (a * b) =
      (Modules.smul (U := U.unop) (M := relativeDifferentials f) a).hom
          (((relativeDifferentialsD f).hom.app U).hom b) +
        (Modules.smul (U := U.unop) (M := relativeDifferentials f) b).hom
          (((relativeDifferentialsD f).hom.app U).hom a) :=
  (relativeDifferentialsDerivation f).d_mul a b

/-- The canonical derivation vanishes on the actual inverse-image structure sheaf. -/
theorem relativeDifferentialsD_vanishes {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (a : (inverseImageStructureSheaf f).obj.obj U) :
    ((relativeDifferentialsD f).hom.app U).hom
      ((inverseImageStructureSheafMap f).hom.app U a) = 0 :=
  (relativeDifferentialsDerivation f).d_app a

end AlgebraicGeometry.Scheme
