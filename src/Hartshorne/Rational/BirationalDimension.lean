/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.BirationalCriterion
import Hartshorne.Rational.VarietyDimension

/-!
# Birational invariance of dimension

Hartshorne, *Algebraic Geometry*, I.8, p. 57.

The dimension of a variety is a birational invariant.  For the abstract
variety API, the affine-open-basis hypotheses identify topological dimension
with the transcendence degree of the function field, while birationality
identifies the two function fields.

## Main result

* `Hartshorne.birational_topologicalKrullDim_eq`
-/

namespace Hartshorne

open TopologicalSpace

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Hartshorne I.8.** Birational varieties have the same dimension. -/
theorem birational_topologicalKrullDim_eq
    (X Y : SeparatedVariety.{u, u} k)
    (hXaff : X.toVariety.HasAffineOpenBasis)
    (hYaff : Y.toVariety.HasAffineOpenBasis)
    (hbir : Birational X Y) :
    topologicalKrullDim X.toVariety.carrier =
      topologicalKrullDim Y.toVariety.carrier := by
  obtain ⟨e⟩ : Nonempty
      (X.toVariety.FunctionField ≃ₐ[k] Y.toVariety.FunctionField) :=
    (birational_iff_nonempty_functionField_algEquiv X Y hXaff hYaff).mp hbir
  obtain ⟨rX, hXdim, hXtr⟩ := hXaff.exists_dimension_eq_trdeg
  obtain ⟨rY, hYdim, hYtr⟩ := hYaff.exists_dimension_eq_trdeg
  have hcard : (rX : Cardinal) = rY :=
    hXtr.symm.trans (e.trdeg_eq.trans hYtr)
  have hr : rX = rY := by
    exact_mod_cast hcard
  exact hXdim.trans (hr ▸ hYdim.symm)

end Hartshorne
