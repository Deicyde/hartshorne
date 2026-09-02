/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Correspondence

/-!
# Affine and quasi-affine varieties

Hartshorne, *Algebraic Geometry*, I.1, the definitions on p. 3 with Examples
1.1.2-1.1.4.

An *affine variety* is an irreducible closed subset of affine space; a
*quasi-affine variety* is a nonempty open subset of one. Hartshorne's varieties
are irreducible by definition, and the empty set is not irreducible, so both
notions carry nonemptiness.

Mathlib's `IsIrreducible` already matches Hartshorne's notion, including the
exclusion of `∅`, so these are predicates on sets rather than new types.

## Main definitions

* `Hartshorne.IsAffineVariety`
* `Hartshorne.IsQuasiAffineVariety`

## Main results

* `Hartshorne.IsPreirreducible.inter_isOpen` : Example 1.1.3, a nonempty open
  piece of an irreducible set is irreducible.
* `Hartshorne.IsQuasiAffineVariety.closure_eq` : a quasi-affine variety is dense
  in the affine variety containing it, which is what Proposition 1.10 needs.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- An *affine variety* is an irreducible closed subset of affine space. -/
def IsAffineVariety (Y : Set (σ → k)) : Prop :=
  IsIrreducible Y ∧ IsClosed Y

/-- A *quasi-affine variety* is a nonempty open subset of an affine variety,
that is, a nonempty set of the form `V ∩ U` with `V` an affine variety and `U`
open in the ambient space. -/
def IsQuasiAffineVariety (Y : Set (σ → k)) : Prop :=
  Y.Nonempty ∧ ∃ V U : Set (σ → k), IsAffineVariety V ∧ IsOpen U ∧ Y = V ∩ U

theorem IsAffineVariety.isIrreducible {Y : Set (σ → k)} (h : IsAffineVariety Y) :
    IsIrreducible Y := h.1

theorem IsAffineVariety.isClosed {Y : Set (σ → k)} (h : IsAffineVariety Y) :
    IsClosed Y := h.2

theorem IsAffineVariety.isAlgebraicSet {Y : Set (σ → k)} (h : IsAffineVariety Y) :
    IsAlgebraicSet Y := isClosed_iff_isAlgebraicSet.1 h.2

/-- Example 1.1.3, in the form needed for quasi-affine varieties: intersecting a
preirreducible set with an open set stays preirreducible. -/
theorem IsPreirreducible.inter_isOpen {X : Type*} [TopologicalSpace X]
    {V U : Set X} (hV : IsPreirreducible V) (hU : IsOpen U) :
    IsPreirreducible (V ∩ U) := by
  rintro u v hu hv ⟨x, hx, hxu⟩ ⟨y, hy, hyv⟩
  obtain ⟨z, hzV, hz⟩ := hV (u ∩ U) (v ∩ U) (hu.inter hU) (hv.inter hU)
    ⟨x, hx.1, hxu, hx.2⟩ ⟨y, hy.1, hyv, hy.2⟩
  exact ⟨z, ⟨hzV, hz.1.2⟩, hz.1.1, hz.2.1⟩

/-- An affine variety is quasi-affine, taking the open set to be everything. -/
theorem IsAffineVariety.isQuasiAffineVariety {Y : Set (σ → k)}
    (h : IsAffineVariety Y) : IsQuasiAffineVariety Y :=
  ⟨h.1.nonempty, Y, Set.univ, h, isOpen_univ, (Set.inter_univ Y).symm⟩

/-- Example 1.1.3: a quasi-affine variety is irreducible. -/
theorem IsQuasiAffineVariety.isIrreducible {Y : Set (σ → k)}
    (h : IsQuasiAffineVariety Y) : IsIrreducible Y := by
  obtain ⟨hne, V, U, hV, hU, rfl⟩ := h
  exact ⟨hne, IsPreirreducible.inter_isOpen hV.1.2 hU⟩

/-- Example 1.1.3: a quasi-affine variety is dense in the affine variety it came
from. Hartshorne uses this in Proposition 1.10 to compare dimensions. -/
theorem IsQuasiAffineVariety.closure_eq {Y V U : Set (σ → k)} (hne : Y.Nonempty)
    (hV : IsAffineVariety V) (hU : IsOpen U) (hYVU : Y = V ∩ U) :
    closure Y = V := by
  refine le_antisymm (hV.2.closure_subset_iff.2 (hYVU ▸ Set.inter_subset_left)) ?_
  have hdense : V ⊆ closure (V ∩ U) := by
    intro x hx
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨z, hzV, hz⟩ := hV.1.2 o U ho hU ⟨x, hx, hxo⟩ (by
      obtain ⟨y, hy⟩ := hne
      exact ⟨y, (hYVU ▸ hy : y ∈ V ∩ U).1, (hYVU ▸ hy : y ∈ V ∩ U).2⟩)
    exact ⟨z, hz.1, hzV, hz.2⟩
  exact hYVU ▸ hdense

/-- The closure of a quasi-affine variety is an affine variety. -/
theorem IsQuasiAffineVariety.isAffineVariety_closure {Y : Set (σ → k)}
    (h : IsQuasiAffineVariety Y) : IsAffineVariety (closure Y) :=
  ⟨h.isIrreducible.closure, isClosed_closure⟩

end Hartshorne
