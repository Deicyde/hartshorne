/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.ValuationRegularity
import Hartshorne.Rational.OpenSubvariety

/-!
# Abstract nonsingular curves

Hartshorne, *Algebraic Geometry*, I.6 (p. 42).

Every nonempty open subset of the valuation space of a one-dimensional
function field is a variety.  Its regular functions are the residue-valued
functions represented by elements of the ambient function field which belong
to every valuation ring in the open set.

We first equip the whole valuation space with the regular functions constructed
in `Hartshorne.Curve.ValuationRegularFunctions`, using the four axioms proved in
`Hartshorne.Curve.ValuationRegularity`, and then apply the general open
subvariety construction.  In particular, relative empty opens inherit the
explicit empty-open convention of `ValuationSpace.regularFunctions`.
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u v

namespace ValuationSpace

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- The ambient variety on the full valuation space of a one-dimensional
function field, before restriction to a chosen open subset. -/
noncomputable def abstractNonsingularCurveAmbient [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1) : Variety k := by
  let h := regularFunctions_axioms htrdeg
  exact {
    carrier := ValuationSpace k K
    topology := inferInstance
    irreducible := irreducibleSpace_of_trdeg_eq_one htrdeg
    regular := fun V ↦ regularFunctions htrdeg (V : Set (ValuationSpace k K))
    regular_restrict := h.regular_restrict
    isClosed_zeroLocus := h.isClosed_zeroLocus
    regular_div := h.regular_div
    regular_of_locally := h.regular_of_locally
  }

/-- A nonempty open subset of the valuation space of a one-dimensional
function field, equipped with its residue-valued regular functions, is an
abstract nonsingular curve.

The ambient field `K` remains part of the construction: the regular-function
algebras are obtained from intersections of valuation subrings inside this
specific field. -/
noncomputable def abstractNonsingularCurve [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) : Variety k :=
  (abstractNonsingularCurveAmbient htrdeg).restrict U hU

end ValuationSpace

end

end Hartshorne
