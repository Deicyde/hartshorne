/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness of open immersions

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.2(a) (p. 254).

Mathlib provides flatness of an open immersion as a typeclass instance. This
file records the source-shaped theorem with a stable project declaration name.
-/

namespace Hartshorne

open CategoryTheory
open AlgebraicGeometry

universe u

/-- **Hartshorne III.9, Proposition 9.2(a).** Every open immersion of schemes
is flat. -/
theorem flat_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : Flat f :=
  inferInstance

end Hartshorne
