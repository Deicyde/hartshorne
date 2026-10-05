/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.Flatness.ModuleSheafFlatOverBase
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Stability

/-!
# Transitivity for module sheaves flat over a base

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.2(c) (p. 254).

If an `𝒪_X`-module is flat over `Y` and `Y ⟶ Z` is flat, then it is flat over `Z`
through the composite morphism.
-/

open CategoryTheory

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

/-- **Hartshorne III.9, Proposition 9.2(c).** Flatness of a module sheaf over a base is
transitive along a flat morphism of base schemes. -/
theorem moduleSheaf_flatOver_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules)
    (hF : F.FlatOver f) [Flat g] : F.FlatOver (f ≫ g) := by
  intro x
  dsimp only [Scheme.Modules.FlatOverAt]
  rw [Scheme.Hom.stalkMap_comp]
  let FX : _root_.PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  let M := ↑(TopCat.Presheaf.stalk (C := Ab) FX.presheaf x)
  let _ : Module (X.presheaf.stalk x) M := by infer_instance
  let _ : Module (Y.presheaf.stalk (f x)) M :=
    Module.compHom M (f.stalkMap x).hom
  let _ : Algebra (Z.presheaf.stalk (g (f x)))
      (Y.presheaf.stalk (f x)) :=
    (g.stalkMap (f x)).hom.toAlgebra
  let _ : Module (Z.presheaf.stalk (g (f x))) M :=
    Module.compHom M <|
      (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom
  let _ : IsScalarTower (Z.presheaf.stalk (g (f x)))
      (Y.presheaf.stalk (f x)) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hFx : Module.Flat (Y.presheaf.stalk (f x)) M := by
    simpa only [Scheme.Modules.FlatOverAt] using hF x
  have hgx : Module.Flat (Z.presheaf.stalk (g (f x)))
      (Y.presheaf.stalk (f x)) := by
    rw [← RingHom.flat_algebraMap_iff]
    exact Flat.stalkMap g (f x)
  let _ : Module.Flat (Y.presheaf.stalk (f x)) M := hFx
  let _ : Module.Flat (Z.presheaf.stalk (g (f x)))
      (Y.presheaf.stalk (f x)) := hgx
  exact Module.Flat.trans (Z.presheaf.stalk (g (f x)))
    (Y.presheaf.stalk (f x)) M

end

end Hartshorne
