/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Filtration

/-!
# The Artin–Rees induced topology

Hartshorne, *Algebraic Geometry*, Proposition III.3.1A (p. 213).

For a submodule `M` of a finite module `N` over a Noetherian ring, the adic
topology on `M` is induced by the adic topology on `N`.
-/

namespace Hartshorne

universe u v

/-- **Proposition III.3.1A.** If `M ⊆ N` are finite modules over a Noetherian
ring and `a` is an ideal, then for every `n` there is an `n' ≥ n` such that
`a ^ n • M` contains `M ∩ (a ^ n' • N)`. -/
theorem artinRees_inducedTopology
    {A : Type u} {N : Type v} [CommRing A] [AddCommGroup N] [Module A N]
    [IsNoetherianRing A] [Module.Finite A N]
    (a : Ideal A) (M : Submodule A N) (n : ℕ) :
    ∃ n' : ℕ, n ≤ n' ∧
      M ⊓ (a ^ n' • (⊤ : Submodule A N)) ≤ a ^ n • M := by
  obtain ⟨k, hk⟩ := a.exists_pow_inf_eq_pow_smul M
  refine ⟨n + k, Nat.le_add_right n k, ?_⟩
  rw [inf_comm, hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right

end Hartshorne
