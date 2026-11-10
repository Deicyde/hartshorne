/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ClosedImmersionIdealSheaf
import Hartshorne.Scheme.Codimension

/-!
# Local complete intersections in an ambient scheme

Hartshorne, *Algebraic Geometry*, II.8 (p. 185), the definition before Theorem 8.21A.

Let `Y` be a closed subscheme of a nonsingular variety `X`, with ideal sheaf `I_Y`. Then `Y` is a
local complete intersection in `X` if `I_Y` can be generated locally by `codim (Y, X)` sections
(`Hartshorne.IsLocalCompleteIntersectionIn`): every point of `X` has an open neighbourhood `U`
such that `I_Y|_U` is generated as an `𝒪_U`-module by a family of sections over `U` indexed by a
set of cardinality `codim (Y, X)`.

The predicate is stated for an arbitrary morphism `i : Y ⟶ X`, with `I_Y` the kernel of
`𝒪_X ⟶ i_* 𝒪_Y` (`Hartshorne.closedImmersionIdealSheaf`) and `codim (Y, X)` the codimension of
the image of `i` (`Hartshorne.codim`); Hartshorne uses it when `i` is a closed immersion into a
nonsingular variety. Cardinality and codimension are compared in `ℕ∞`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

variable {X Y : Scheme.{u}}

/-- **Local complete intersections** (Hartshorne II.8, p. 185). A subscheme `i : Y ⟶ X` is a
local complete intersection in `X` when its ideal sheaf `I_Y` is generated near every point by
`codim (Y, X)` local sections: each `x : X` lies in an open `U` such that `I_Y|_U` has a family
of generating sections over `U` whose index set has cardinality `codim (Y, X)`. -/
def IsLocalCompleteIntersectionIn (i : Y ⟶ X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ σ : ((Scheme.Modules.restrictFunctor U.ι).obj
        (closedImmersionIdealSheaf i)).GeneratingSections,
      ENat.card σ.I = codim (Set.range i.base)

end Hartshorne
