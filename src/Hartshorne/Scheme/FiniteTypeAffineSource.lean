/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteType

/-!
# Affine source opens of a finite-type morphism

Hartshorne, *Algebraic Geometry*, Exercise II.3.3(c) (p. 91).

For a finite-type morphism, the coordinate ring of any affine source open lying
over an affine target open is finitely generated over the target coordinate
ring.
-/

namespace Hartshorne

open CategoryTheory

universe u

open AlgebraicGeometry

/-- **Exercise II.3.3(c).** If `f : X ⟶ Y` is of finite type, `V` is an affine
open of `Y`, and `U` is an affine open of `X` contained in `f ⁻¹ᵁ V`, then
`Γ(X, U)` is a finitely generated `Γ(Y, V)`-algebra. -/
theorem finiteType_affineSource_algebra
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : FiniteType f)
    (V : Y.affineOpens) (U : X.affineOpens)
    (hU : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens)) :
    (f.appLE (V : Y.Opens) (U : X.Opens) hU).hom.FiniteType := by
  let _ : LocallyOfFiniteType f := hf.1
  exact f.finiteType_appLE V.2 U.2 hU

end Hartshorne
