/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Zariski
import Mathlib.Topology.NoetherianSpace

/-!
# Affine space is a Noetherian space

Hartshorne, *Algebraic Geometry*, I.1, the definition on p. 5 and Example 1.4.7.

A descending chain of closed subsets of `𝔸ⁿ` gives an ascending chain of ideals
of `k[x₁,…,xₙ]`, which is Noetherian, and the chain of closed sets is recovered
from the chain of ideals, so it stabilises too.

Formally the cleanest route is to package that argument as a strictly monotone
map from the open sets to the ideals. `NoetherianSpace` is by definition
`WellFoundedGT (Opens α)`, and a strictly monotone map into a `WellFoundedGT`
order reflects the property.

## Main results

* `Hartshorne.instNoetherianSpace` : `𝔸ⁿ` is a Noetherian space.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*}

/-- Sending an open set to the ideal of its complement embeds the open sets of
affine space into the ideals of the polynomial ring, order-preservingly. It is
injective because a closed set is recovered from its vanishing ideal. -/
theorem strictMono_vanishingIdeal_compl :
    StrictMono (fun U : Opens (σ → k) => vanishingIdeal k ((U : Set (σ → k))ᶜ)) := by
  refine Monotone.strictMono_of_injective (fun U V h => ?_) (fun U V h => ?_)
  · exact vanishingIdeal_anti_mono (Set.compl_subset_compl.2 h)
  · have hU : IsAlgebraicSet ((U : Set (σ → k))ᶜ) :=
      isClosed_iff_isAlgebraicSet.1 U.isOpen.isClosed_compl
    have hV : IsAlgebraicSet ((V : Set (σ → k))ᶜ) :=
      isClosed_iff_isAlgebraicSet.1 V.isOpen.isClosed_compl
    have hc : (U : Set (σ → k))ᶜ = (V : Set (σ → k))ᶜ := by
      rw [← hU.zeroLocus_vanishingIdeal, ← hV.zeroLocus_vanishingIdeal, h]
    exact Opens.ext (compl_injective hc)

/-- Example 1.4.7: affine space over finitely many variables is a Noetherian
topological space. -/
instance instNoetherianSpace [Finite σ] : NoetherianSpace (σ → k) :=
  strictMono_vanishingIdeal_compl.wellFoundedGT

end Hartshorne
