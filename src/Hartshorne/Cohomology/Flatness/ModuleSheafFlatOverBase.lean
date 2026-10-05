/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.RingTheory.Flat.Basic

/-!
# Module sheaves flat over a base

Hartshorne, *Algebraic Geometry*, III.9 (p. 254).

An `𝒪_X`-module is flat over `Y` at `x : X` when its stalk at `x`, restricted along the
stalk map induced by `f : X ⟶ Y`, is flat over the local ring of `Y` at `f x`.
-/

open CategoryTheory

namespace AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}}

/-- An `𝒪_X`-module is flat over `Y` at `x : X` if its stalk at `x` is flat over
`𝒪_{Y, f(x)}` via the stalk map induced by `f`. -/
def Scheme.Modules.FlatOverAt (f : X ⟶ Y) (F : X.Modules) (x : X) : Prop :=
  let FX : _root_.PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  letI : Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk (C := Ab) FX.presheaf x) := by infer_instance
  letI : Module (Y.presheaf.stalk (f x))
      ↑(TopCat.Presheaf.stalk (C := Ab) FX.presheaf x) :=
    Module.compHom _ (f.stalkMap x).hom
  Module.Flat (Y.presheaf.stalk (f x))
    ↑(TopCat.Presheaf.stalk (C := Ab) FX.presheaf x)

/-- An `𝒪_X`-module is flat over `Y` if it is flat over `Y` at every point of `X`. -/
def Scheme.Modules.FlatOver (f : X ⟶ Y) (F : X.Modules) : Prop :=
  ∀ x, F.FlatOverAt f x

end

end AlgebraicGeometry
