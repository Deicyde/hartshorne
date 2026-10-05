/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Functors

/-!
# Left exactness of direct image for abelian sheaves

Hartshorne, *Algebraic Geometry*, III.8, p. 250.

Direct image of abelian sheaves along a continuous map preserves finite
limits because it is right adjoint to inverse image.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Hartshorne

/-- Direct image along a continuous map preserves finite limits on sheaves of
abelian groups. -/
noncomputable instance abelianSheafPushforwardPreservesFiniteLimits
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) := by
  constructor
  intro J _ _
  exact
    (Adjunction.rightAdjoint_preservesLimits
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).preservesLimitsOfShape

end Hartshorne
