/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Dimension
import Mathlib.Topology.KrullDimension

/-!
# The dimension of a quasi-affine variety

Hartshorne, *Algebraic Geometry*, I.1, Proposition 1.10 (p. 6), the easy
inequality.

`dim Y ≤ dim Ȳ` for any subset `Y`, because a chain of irreducible closed
subsets of a subspace is no longer than one upstairs.

Mathlib states this for an inducing map, and the inclusion of `Y` into its
closure is inducing because both carry the topology induced from the ambient
space.

The reverse inequality is the content of Proposition 1.10 and is not proved
here; it needs a maximal chain in `Y` to be read as a chain of primes below a
maximal ideal of `A(Ȳ)`, and then that every maximal ideal has full height.

## Main results

* `Hartshorne.dim_le_dim_closure`
-/

namespace Hartshorne

variable {k : Type*} [Field k] {σ : Type*}

/-- **A subset has dimension at most that of its closure.** -/
theorem dim_le_dim_closure (Y : Set (σ → k)) : dim Y ≤ dim (closure Y) := by
  refine Topology.IsInducing.topologicalKrullDim_le
    (f := fun x : Y => (⟨x.1, subset_closure x.2⟩ : closure Y)) ?_
  refine Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val ?_
  exact Topology.IsInducing.subtypeVal

end Hartshorne
