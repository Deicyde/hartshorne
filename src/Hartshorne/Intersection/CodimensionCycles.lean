/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Hartshorne.Scheme.Codimension

/-!
# Cycles of fixed codimension

Hartshorne, *Algebraic Geometry*, Appendix A.1 (p. 425).

The codimension-`r` cycles on a scheme are the algebraic cycles with finite support whose generic
points have closures of codimension `r`. This is a subgroup of Mathlib's locally finite algebraic
cycles, rather than a second representation of cycles.
-/

namespace Hartshorne

open AlgebraicGeometry

/-- The subgroup of algebraic cycles with finite support in codimension `r`. -/
noncomputable def codimensionCycles (X : Scheme) (r : ℕ) :
    AddSubgroup (AlgebraicCycle X ℤ) where
  carrier := {c | c.support.Finite ∧
    ∀ x ∈ c.support, codim (closure {x}) = r}
  zero_mem' := by
    constructor
    · change (Function.support (0 : X → ℤ)).Finite
      simp
    · intro x hx
      change x ∈ Function.support (0 : X → ℤ) at hx
      simp at hx
  add_mem' {c d} hc hd := by
    constructor
    · exact (hc.1.union hd.1).subset (Function.support_add _ _)
    · intro x hx
      rcases Function.support_add _ _ hx with hx | hx
      · exact hc.2 x hx
      · exact hd.2 x hx
  neg_mem' {c} hc := by simpa using hc

end Hartshorne
