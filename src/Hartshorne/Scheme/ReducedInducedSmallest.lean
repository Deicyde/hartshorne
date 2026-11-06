/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ReducedInducedSubscheme

/-!
# The reduced induced structure is the smallest closed subscheme structure

Hartshorne, *Algebraic Geometry*, II.3, Example 3.2.6 (p. 86).

Let `Z` be a closed subset of a scheme `X`, and let `i : Z' ⟶ X` be any closed immersion whose
image is exactly `Z`. Then the inclusion of the reduced induced closed subscheme on `Z` factors
uniquely through `i`.

The ideal sheaf of `Z'` has support `Z`, so by the Galois connection between supports and
vanishing ideals it is contained in the vanishing ideal of `Z`, which is the ideal sheaf of the
reduced induced subscheme. The universal property of the closed immersion `i` gives the
factorization, and uniqueness holds because closed immersions are monomorphisms.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hartshorne

universe u

variable {X : Scheme.{u}}

/-- **Hartshorne II, Example 3.2.6.** If `i : Z' ⟶ X` is a closed immersion with underlying set
`Z`, then the reduced induced closed subscheme on `Z` factors uniquely through `i`. -/
theorem existsUnique_reducedInducedSubschemeι_factorization (Z : Closeds X) {Z' : Scheme.{u}}
    (i : Z' ⟶ X) [IsClosedImmersion i] (hi : Set.range i = (Z : Set X)) :
    ∃! g : reducedInducedSubscheme Z ⟶ Z', g ≫ i = reducedInducedSubschemeι Z := by
  have hle : i.ker ≤ (reducedInducedSubschemeι Z).ker := by
    rw [ker_reducedInducedSubschemeι, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    exact i.range_subset_ker_support (hi ▸ hx)
  refine ⟨IsClosedImmersion.lift i _ hle, IsClosedImmersion.lift_fac _ _ _, fun g hg => ?_⟩
  rw [← cancel_mono i, hg, IsClosedImmersion.lift_fac]

end Hartshorne
