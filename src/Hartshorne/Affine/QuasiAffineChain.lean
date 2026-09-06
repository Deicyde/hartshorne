/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Variety
import Hartshorne.Affine.QuasiAffineDimension
import Mathlib.Topology.Sets.Closeds

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
* `Hartshorne.restrictToY`, `Hartshorne.strictMono_restrictToY`
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

open TopologicalSpace in
/-- Irreducibility transfers back along the inclusion of a subspace: an embedding
reflects it, because the opens of the subspace are traces of ambient opens. -/
theorem isPreirreducible_preimage_val {Y : Set X} {s : Set Y}
    (h : IsPreirreducible (Subtype.val '' s)) : IsPreirreducible s := by
  rintro u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.1 hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.1 hv
  obtain ⟨z, hz, hzu, hzv⟩ :=
    h u' v' hu' hv' ⟨x.1, ⟨x, hxs, rfl⟩, hxu⟩ ⟨y.1, ⟨y, hys, rfl⟩, hyv⟩
  obtain ⟨w, hws, rfl⟩ := hz
  exact ⟨w, hws, hzu, hzv⟩

theorem isIrreducible_preimage_val {Y : Set X} {s : Set Y}
    (h : IsIrreducible (Subtype.val '' s)) : IsIrreducible s :=
  ⟨Set.image_nonempty.1 h.1, isPreirreducible_preimage_val h.2⟩

open TopologicalSpace in
/-- **Restricting to `Y` an irreducible closed subset of `Ȳ` through a point of
`Y`.** -/
def restrictToY (hY : Y = V₀ ∩ U) (hV₀ : IsClosed V₀) (hU : IsOpen U) {P : X}
    (hP : P ∈ Y)
    (Z : {Z : IrreducibleCloseds X // P ∈ (Z : Set X) ∧ (Z : Set X) ⊆ closure Y}) :
    IrreducibleCloseds Y where
  carrier := Subtype.val ⁻¹' (Z.1 : Set X)
  isIrreducible' := by
    refine isIrreducible_preimage_val ?_
    rw [Subtype.image_preimage_coe, Set.inter_comm]
    exact isIrreducible_inter_of_subset_closure hY hV₀ hU Z.1.isIrreducible' Z.2.2
      ⟨P, Z.2.1, hP⟩
  isClosed' := Z.1.isClosed'.preimage continuous_subtype_val

open TopologicalSpace in
/-- And the restriction is strictly monotone, because each such subset is the
closure of its trace on `Y`. -/
theorem strictMono_restrictToY (hY : Y = V₀ ∩ U) (hV₀ : IsClosed V₀) (hU : IsOpen U)
    {P : X} (hP : P ∈ Y) :
    StrictMono (restrictToY hY hV₀ hU hP) := by
  intro Z W hZW
  have hsub : (Z.1 : Set X) ⊆ (W.1 : Set X) := hZW.le
  refine lt_of_le_of_ne
    (show restrictToY hY hV₀ hU hP Z ≤ restrictToY hY hV₀ hU hP W from
      fun x hx => hsub hx) fun heq => hZW.ne ?_
  have hcar : Subtype.val ⁻¹' (Z.1 : Set X) = Subtype.val ⁻¹' (W.1 : Set X) :=
    congrArg (fun t : TopologicalSpace.IrreducibleCloseds Y => (t : Set Y)) heq
  have himg : Y ∩ (Z.1 : Set X) = Y ∩ (W.1 : Set X) := by
    rw [← Subtype.image_preimage_coe, ← Subtype.image_preimage_coe]
    exact congrArg _ hcar
  have hZc := closure_inter_eq_of_subset_closure (V := (Z.1 : Set X)) hY hV₀ hU
    Z.1.isIrreducible' Z.1.isClosed' Z.2.2 ⟨P, Z.2.1, hP⟩
  have hWc := closure_inter_eq_of_subset_closure (V := (W.1 : Set X)) hY hV₀ hU
    W.1.isIrreducible' W.1.isClosed' W.2.2 ⟨P, W.2.1, hP⟩
  have hsets : (Z.1 : Set X) = (W.1 : Set X) := by
    rw [← hZc, ← hWc, Set.inter_comm (Z.1 : Set X) Y, Set.inter_comm (W.1 : Set X) Y, himg]
  exact Subtype.ext (IrreducibleCloseds.ext hsets)

end Hartshorne
