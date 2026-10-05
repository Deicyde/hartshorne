/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BaseExtension
import Hartshorne.Scheme.FiniteType

/-!
# Finite type and base extension

Hartshorne, *Algebraic Geometry*, II.3 (pp. 89–90) and Exercise II.3.13 (p. 93).

Morphisms of finite type remain of finite type after arbitrary base extension.
-/

namespace Hartshorne

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/-- An arbitrary base extension of a morphism of finite type is of finite type. -/
theorem finiteType_baseExtension {S X S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (hf : FiniteType f) :
    FiniteType (baseExtensionProjection f g) := by
  exact
    ⟨locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f g) hf.1,
      quasiCompact_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f g) hf.2⟩

end Hartshorne
