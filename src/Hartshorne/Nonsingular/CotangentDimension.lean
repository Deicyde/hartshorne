/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The cotangent-dimension bound

Hartshorne, *Algebraic Geometry*, I.5, Proposition 5.2A (p. 33).

For a Noetherian local ring, its Krull dimension is at most the dimension of
its cotangent space over the residue field.

## Main result

* `Hartshorne.ringKrullDim_le_finrank_cotangentSpace`
-/

namespace Hartshorne

/-- **Hartshorne I.5, Proposition 5.2A.** The Krull dimension of a Noetherian
local ring is at most the dimension of its cotangent space over its residue
field. -/
theorem ringKrullDim_le_finrank_cotangentSpace
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤
      (Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.CotangentSpace R) : WithBot ℕ∞) := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

end Hartshorne
