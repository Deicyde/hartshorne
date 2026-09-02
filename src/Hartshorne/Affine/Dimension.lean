/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Variety
import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Dimension

Hartshorne, *Algebraic Geometry*, I.1, the definitions on pp. 5-6.

The dimension of a topological space is the supremum of the lengths of chains
`Z₀ ⊊ … ⊊ Zₙ` of irreducible closed subsets, and the dimension of a variety is
its dimension as a space. On the ring side, the height of a prime is the
supremum of lengths of chains of primes below it, and the Krull dimension is the
supremum of the heights.

Both notions are already in Mathlib. `topologicalKrullDim T` is
`krullDim (IrreducibleCloseds T)`, which is Hartshorne's definition verbatim,
and `ringKrullDim R` is `krullDim (PrimeSpectrum R)`. This file fixes them as
the project's definitions and specialises the topological one to subsets of
affine space, so later statements can say `dim Y` rather than reintroducing
chains.

Everything is valued in `WithBot ℕ∞`: the empty space has dimension `⊥`, and
infinite-dimensional Noetherian spaces exist, so `dim 𝔸ⁿ = n` is an equation in
`WithBot ℕ∞` and its coercion has to be handled explicitly.

## Main definitions

* `Hartshorne.dim` : the dimension of a subset of affine space.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*}

/-- The dimension of a subset of affine space, computed in the induced Zariski
topology. This is Hartshorne's `dim Y` for `Y` an affine or quasi-affine
variety, but it is defined for any subset. -/
noncomputable def dim (Y : Set (σ → k)) : WithBot ℕ∞ :=
  topologicalKrullDim Y

theorem dim_def (Y : Set (σ → k)) : dim Y = topologicalKrullDim Y := rfl

/-- Dimension is monotone in the subset, since the inclusion of subspaces is
inducing. Hartshorne records this as Exercise 1.10(a). -/
theorem dim_le_of_subset {Y Z : Set (σ → k)} (h : Y ⊆ Z) : dim Y ≤ dim Z :=
  (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-- The dimension of the whole of affine space, as a space rather than a
subset. -/
noncomputable abbrev dimAffineSpace (k σ : Type*) [Field k] : WithBot ℕ∞ :=
  topologicalKrullDim (σ → k)

theorem dim_univ : dim (Set.univ : Set (σ → k)) = dimAffineSpace k σ :=
  IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ (σ → k)).isHomeomorph

end Hartshorne
