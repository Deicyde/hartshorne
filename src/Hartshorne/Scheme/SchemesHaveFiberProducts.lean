/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Fiber products of schemes exist

Hartshorne, *Algebraic Geometry*, II.3, Theorem 3.3 (pp. 87–88).

Mathlib constructs pullbacks of schemes by gluing affine pullbacks. This
theorem gives that anonymous typeclass instance a stable, source-facing name.
-/

namespace Hartshorne

open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/-- Every cospan of schemes has a fiber product. Its universal property also
implies uniqueness up to unique isomorphism. -/
theorem schemesHaveFiberProducts : HasPullbacks Scheme.{u} :=
  inferInstance

end Hartshorne
