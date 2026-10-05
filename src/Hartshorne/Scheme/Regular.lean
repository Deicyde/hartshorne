/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular points and regular schemes

Hartshorne, *Algebraic Geometry*, II.8 (p. 177).

A point of a scheme is regular when its local ring is a regular local ring. A
regular scheme is locally Noetherian and regular at every point. For an
integral separated scheme of finite type over an algebraically closed field,
this all-points condition is Hartshorne's nonsingularity condition.

These predicates concern Mathlib schemes and are distinct from the Chapter-I
predicates on `Hartshorne.Variety`.
-/

namespace AlgebraicGeometry

universe u

/-- A point `x` of a scheme `X` is regular when its local ring is a regular
local ring. -/
def Scheme.IsRegularAt (X : Scheme.{u}) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

/-- A scheme is regular when it is locally Noetherian and all of its points
are regular. -/
def Scheme.IsRegular (X : Scheme.{u}) : Prop :=
  IsLocallyNoetherian X ∧ ∀ x : X, X.IsRegularAt x

end AlgebraicGeometry
