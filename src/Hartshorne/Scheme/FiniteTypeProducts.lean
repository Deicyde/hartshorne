/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteTypeBaseChange

/-!
# Products of schemes of finite type

Hartshorne, *Algebraic Geometry*, Exercise II.3.13 (p. 93).

The fiber product of two schemes of finite type over a common base is again of
finite type over that base.
-/

namespace Hartshorne

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/-- The fiber product of two finite-type morphisms is finite type over their
common target. -/
theorem finiteType_products {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (hf : FiniteType f) (hg : FiniteType g) :
    FiniteType (pullback.fst f g ≫ f) := by
  rw [pullback.condition]
  exact finiteType_comp (pullback.snd f g) g (finiteType_baseExtension f g hf) hg

end Hartshorne
