/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Variety
import Hartshorne.Affine.QuasiAffineDimension

/-!
# Cutting a chain down to a quasi-affine piece

Toward Hartshorne, *Algebraic Geometry*, I.1, Proposition 1.10 (p. 6).

`Y` quasi-affine sits inside its closure as a dense open piece, and the two
lemmas here say what that does to an irreducible closed subset `V` of the
closure that meets `Y`: `V ∩ Y` is again irreducible, and its closure is `V`
again.

Together they say that intersecting with `Y` is injective and strictly monotone
on such subsets, which is what turns a chain of irreducible closed subsets of
`Ȳ` through a point of `Y` into a chain of the same length inside `Y`. That is
the reverse inequality of Proposition 1.10, whose forward half is
[elsewhere](QuasiAffineDimension.lean).

The hypotheses are stated with the locally closed presentation `Y = V₀ ∩ U`
explicit, since that is what makes `V ∩ Y` an intersection with an *ambient*
open set: `V` already lies inside `V₀`, so the closed half does nothing.

## Main results

* `Hartshorne.isIrreducible_inter_of_subset_closure`
* `Hartshorne.closure_inter_eq_of_subset_closure`
-/

namespace Hartshorne

variable {X : Type*} [TopologicalSpace X] {Y V₀ U V : Set X}

/-- On a subset of the closure, meeting `Y` is the same as meeting the open half
of its presentation. -/
theorem inter_eq_inter_isOpen (hY : Y = V₀ ∩ U) (hV₀ : IsClosed V₀)
    (hV : V ⊆ closure Y) : V ∩ Y = V ∩ U := by
  have hsub : V ⊆ V₀ := by
    refine hV.trans (closure_minimal ?_ hV₀)
    rw [hY]
    exact Set.inter_subset_left
  rw [hY, ← Set.inter_assoc, Set.inter_eq_self_of_subset_left hsub]

/-- **An irreducible closed subset of the closure meets `Y` in an irreducible
set.**

`V ∩ Y` is `V` intersected with an ambient open set, and a nonempty open piece
of an irreducible set is irreducible. -/
theorem isIrreducible_inter_of_subset_closure (hY : Y = V₀ ∩ U) (hV₀ : IsClosed V₀)
    (hU : IsOpen U) (hVirr : IsIrreducible V) (hV : V ⊆ closure Y)
    (hne : (V ∩ Y).Nonempty) : IsIrreducible (V ∩ Y) := by
  refine ⟨hne, ?_⟩
  rw [inter_eq_inter_isOpen hY hV₀ hV]
  exact IsPreirreducible.inter_isOpen hVirr.2 hU

/-- **And that intersection is dense in it.**

So intersecting with `Y` loses no information about `V`: it is injective on the
irreducible closed subsets of `Ȳ` that meet `Y`, and therefore strictly
monotone. -/
theorem closure_inter_eq_of_subset_closure (hY : Y = V₀ ∩ U) (hV₀ : IsClosed V₀)
    (hU : IsOpen U) (hVirr : IsIrreducible V) (hVcl : IsClosed V)
    (hV : V ⊆ closure Y) (hne : (V ∩ Y).Nonempty) : closure (V ∩ Y) = V := by
  refine le_antisymm (closure_minimal Set.inter_subset_left hVcl) ?_
  -- `V ∩ Y` is a nonempty open subset of the irreducible `V`, hence dense in it.
  intro x hx
  rw [mem_closure_iff]
  intro o ho hxo
  have hoV : (V ∩ (o ∩ U)).Nonempty := by
    obtain ⟨y, hyV, hyY⟩ := hne
    refine hVirr.2 o U ho hU ⟨x, hx, hxo⟩ ⟨y, hyV, ?_⟩
    rw [hY] at hyY
    exact hyY.2
  obtain ⟨z, hzV, hzo, hzU⟩ := hoV
  have hsubV0 : V ⊆ V₀ := by
    refine hV.trans (closure_minimal ?_ hV₀)
    rw [hY]
    exact Set.inter_subset_left
  refine ⟨z, hzo, hzV, ?_⟩
  rw [hY]
  exact ⟨hsubV0 hzV, hzU⟩

end Hartshorne
