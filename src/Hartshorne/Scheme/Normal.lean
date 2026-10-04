/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Normal schemes

Hartshorne, *Algebraic Geometry*, Exercise II.3.8 (p. 91).

A scheme is normal when each of its local rings is an integrally closed domain.
The domain and integral-closedness conditions are recorded separately so that
downstream local arguments can obtain either instance directly.
-/

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- A scheme is normal when every stalk of its structure sheaf is an
integrally closed domain. -/
class IsNormal (X : Scheme.{u}) : Prop where
  isDomain_stalk (x : X) : IsDomain (X.presheaf.stalk x)
  isIntegrallyClosed_stalk (x : X) : IsIntegrallyClosed (X.presheaf.stalk x)

attribute [instance] IsNormal.isDomain_stalk IsNormal.isIntegrallyClosed_stalk

end Hartshorne
