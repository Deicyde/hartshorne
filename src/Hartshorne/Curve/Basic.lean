/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.VarietyDimension

/-!
# Curves

Hartshorne, *Algebraic Geometry*, I.2 (p. 13) and I.6 (p. 39).

A curve is a variety of dimension one. For varieties with an affine-open basis,
this is equivalent to the function field having transcendence degree one.
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace Variety

/-- A curve is a variety of topological Krull dimension one. -/
def IsCurve (X : Variety.{u, v} k) : Prop :=
  topologicalKrullDim X.carrier = 1

/-- For a variety with an affine-open basis, being a curve is equivalent to its
function field having transcendence degree one. -/
theorem HasAffineOpenBasis.isCurve_iff_trdeg_eq_one {X : Variety k}
    (hX : X.HasAffineOpenBasis) :
    X.IsCurve ↔ Algebra.trdeg k X.FunctionField = 1 := by
  constructor
  · exact hX.trdeg_eq_of_topologicalKrullDim_eq
  · intro htr
    obtain ⟨r, hdim, htr'⟩ := hX.exists_dimension_eq_trdeg
    have hr : r = 1 := by
      exact_mod_cast htr'.symm.trans htr
    simpa [IsCurve, hr] using hdim

end Variety

end Hartshorne
