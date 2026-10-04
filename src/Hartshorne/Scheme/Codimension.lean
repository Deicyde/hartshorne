/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.KrullDimension

/-!
# Codimension in a scheme

Hartshorne, *Algebraic Geometry*, II.3 (p. 86).

The codimension of a closed subset is the infimum of the coheights of the
irreducible closed subsets it contains. The definition is made for every
subset of a topological space; for the empty subset, the infimum is over an
empty family and hence equals `⊤` in `ℕ∞`.
-/

namespace Hartshorne

/-- The codimension of `Y` in `X`, defined as the infimum of the coheights of
the irreducible closed subsets of `X` contained in `Y`.

This is intended for closed subsets of schemes, but the same formula makes
sense for any subset of a topological space. -/
noncomputable def codim {X : Type*} [TopologicalSpace X] (Y : Set X) : ℕ∞ :=
  ⨅ (Z : TopologicalSpace.IrreducibleCloseds X) (_ : (Z : Set X) ⊆ Y), Order.coheight Z

end Hartshorne
