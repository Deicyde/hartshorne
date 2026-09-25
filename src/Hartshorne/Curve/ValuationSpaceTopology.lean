/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.FunctionFieldDVR
import Mathlib.Topology.Constructions

/-!
# The cofinite valuation space

Hartshorne, *Algebraic Geometry*, I.6 (p. 42).

We equip the discrete valuation rings of a field extension `K / k` with the
cofinite topology.  No finite-generation or dimension hypothesis is needed
for this definition.
-/

namespace Hartshorne

open Set

universe u v

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/-- The space of discrete valuation rings of `K / k`, with the cofinite
topology. -/
abbrev ValuationSpace : Type v :=
  CofiniteTopology (FunctionFieldDVR k K)

namespace ValuationSpace

/-- The identity equivalence from function-field DVRs to the valuation space. -/
def of : FunctionFieldDVR k K ≃ ValuationSpace k K :=
  CofiniteTopology.of

@[simp]
theorem of_symm_apply_apply (R : FunctionFieldDVR k K) :
    (of k K).symm (of k K R) = R :=
  (of k K).symm_apply_apply R

@[simp]
theorem of_apply_symm_apply (R : ValuationSpace k K) :
    of k K ((of k K).symm R) = R :=
  (of k K).apply_symm_apply R

/-- A subset of the valuation space is open exactly when it is empty or has
finite complement. -/
theorem isOpen_iff {U : Set (ValuationSpace k K)} :
    IsOpen U ↔ U = ∅ ∨ Uᶜ.Finite := by
  exact CofiniteTopology.isOpen_iff'

/-- Equivalently, every nonempty open subset of the valuation space has finite
complement. -/
theorem isOpen_iff_nonempty_imp_compl_finite {U : Set (ValuationSpace k K)} :
    IsOpen U ↔ U.Nonempty → Uᶜ.Finite := by
  exact CofiniteTopology.isOpen_iff

/-- A subset of the valuation space is closed exactly when it is the whole
space or is finite. -/
theorem isClosed_iff {Z : Set (ValuationSpace k K)} :
    IsClosed Z ↔ Z = Set.univ ∨ Z.Finite := by
  exact CofiniteTopology.isClosed_iff

end ValuationSpace

end Hartshorne
