/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Closed range of the diagonal

Hartshorne, *Algebraic Geometry*, II.4, Corollary 4.2, pp. 96--97.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- A scheme morphism is separated exactly when its diagonal has closed
set-theoretic range. -/
theorem isSeparated_iff_isClosed_range_diagonal
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSeparated f ↔ IsClosed (Set.range (pullback.diagonal f)) := by
  rw [isSeparated_iff, IsClosedImmersion.iff_isPreimmersion]
  exact and_iff_right inferInstance

end Hartshorne
