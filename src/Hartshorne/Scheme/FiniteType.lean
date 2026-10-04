/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LocallyFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Morphisms of finite type

Hartshorne, *Algebraic Geometry*, II.3 (p. 84) and Exercise II.3.3(a) (p. 91).

Hartshorne's finite-cover condition is represented by quasi-compactness, so a
morphism is of finite type when it is locally of finite type and quasi-compact.
-/

namespace Hartshorne

open CategoryTheory

universe u

open AlgebraicGeometry

/-- A morphism of schemes is of finite type when it is locally of finite type
and quasi-compact. This is a proposition, not a competing typeclass for the two
component properties supplied by Mathlib. -/
def FiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyOfFiniteType f ∧ QuasiCompact f

end Hartshorne
