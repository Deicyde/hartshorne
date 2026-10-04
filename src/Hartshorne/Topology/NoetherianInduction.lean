/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.NoetherianSpace

/-!
# Noetherian induction

Hartshorne's noetherian induction principle, stated for closed subsets rather
than for Mathlib's bundled type `TopologicalSpace.Closeds`.
-/

open TopologicalSpace Topology

namespace Hartshorne

/-- **Hartshorne II.3, Exercise 3.16**: to prove a property of every closed
subset of a Noetherian space, it suffices to prove it assuming the property for
every proper closed subset. -/
theorem noetherianInduction {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (P : Set X → Prop)
    (step : ∀ Y : Set X, IsClosed Y →
      (∀ Z : Set X, IsClosed Z → Z ⊂ Y → P Z) → P Y) :
    ∀ Y : Set X, IsClosed Y → P Y := by
  intro Y hY
  let Y' : Closeds X := ⟨Y, hY⟩
  change P (Y' : Set X)
  induction Y' using WellFoundedLT.induction with
  | ind Y' ih =>
      apply step (Y' : Set X) Y'.isClosed
      intro Z hZ hZY
      let Z' : Closeds X := ⟨Z, hZ⟩
      exact ih Z' hZY

end Hartshorne
