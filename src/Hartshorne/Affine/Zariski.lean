/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.AlgebraicSet
import Mathlib.Topology.Order
import Mathlib.Topology.Irreducible

/-!
# The Zariski topology on affine space

Hartshorne, *Algebraic Geometry*, I.1, Proposition 1.1 and the definition
following it (p. 2).

The algebraic sets are closed under finite unions and arbitrary intersections
and contain `∅` and the whole space, so they are the closed sets of a topology.
Only the union case has content: it needs `k` to have no zero divisors, which is
where being a field is used.

## Main results

* `Hartshorne.zeroSet_union_zeroSet` : `Z(T₁) ∪ Z(T₂) = Z(T₁T₂)`, Hartshorne's
  proof of Proposition 1.1.
* `Hartshorne.zariskiTopology` : the resulting topology.
* `Hartshorne.isClosed_iff_isAlgebraicSet` : its closed sets are exactly the
  algebraic sets.
-/

namespace Hartshorne

open MvPolynomial Pointwise

variable {k : Type*} [Field k] {σ : Type*}

/-- An algebraic set is its own zero set of vanishing polynomials. This is the
statement that algebraic sets are the closed points of the `Z`/`I` Galois
connection, and it is what makes intersections work without choice. -/
theorem IsAlgebraicSet.zeroLocus_vanishingIdeal {Y : Set (σ → k)}
    (h : IsAlgebraicSet Y) : zeroLocus k (vanishingIdeal k Y) = Y := by
  obtain ⟨I, rfl⟩ := isAlgebraicSet_iff_exists_ideal.1 h
  refine le_antisymm ?_ (zeroLocus_vanishingIdeal_le _)
  exact zeroLocus_anti_mono (le_vanishingIdeal_zeroLocus I)

/-- The empty set is algebraic: it is cut out by the constant `1`. -/
theorem isAlgebraicSet_empty : IsAlgebraicSet (∅ : Set (σ → k)) := by
  refine ⟨{1}, ?_⟩
  ext x
  simp

/-- The whole space is algebraic: it is cut out by the empty family. -/
theorem isAlgebraicSet_univ : IsAlgebraicSet (Set.univ : Set (σ → k)) :=
  ⟨∅, by ext x; simp⟩

/-- Hartshorne's `Z(T₁) ∪ Z(T₂) = Z(T₁T₂)`, where `T₁T₂` is the set of pairwise
products. The reverse inclusion is where `k` being a domain is used. -/
theorem zeroSet_union_zeroSet (T₁ T₂ : Set (MvPolynomial σ k)) :
    zeroSet T₁ ∪ zeroSet T₂ = zeroSet (T₁ * T₂) := by
  ext x
  simp only [Set.mem_union, mem_zeroSet_iff, Set.mem_mul]
  constructor
  · rintro (h | h) _ ⟨f, hf, g, hg, rfl⟩ <;> simp [h, hf, hg]
  · intro h
    by_contra hx
    push Not at hx
    obtain ⟨⟨f, hf, hfx⟩, ⟨g, hg, hgx⟩⟩ := hx
    exact mul_ne_zero hfx hgx (by simpa using h (f * g) ⟨f, hf, g, hg, rfl⟩)

/-- Algebraic sets are closed under finite unions. -/
theorem IsAlgebraicSet.union {Y Z : Set (σ → k)} (hY : IsAlgebraicSet Y)
    (hZ : IsAlgebraicSet Z) : IsAlgebraicSet (Y ∪ Z) := by
  obtain ⟨T₁, rfl⟩ := hY
  obtain ⟨T₂, rfl⟩ := hZ
  exact ⟨T₁ * T₂, zeroSet_union_zeroSet T₁ T₂⟩

/-- Algebraic sets are closed under arbitrary intersections. The witnessing
family is the union of the vanishing ideals, which avoids choosing a defining
family for each member. -/
theorem isAlgebraicSet_sInter {A : Set (Set (σ → k))}
    (hA : ∀ Y ∈ A, IsAlgebraicSet Y) : IsAlgebraicSet (⋂₀ A) := by
  refine isAlgebraicSet_iff_exists_ideal.2 ⟨⨆ Y ∈ A, vanishingIdeal k Y, ?_⟩
  ext x
  simp only [Set.mem_sInter]
  constructor
  · -- A point of every member kills every polynomial vanishing on some member.
    intro hx
    have hle : (⨆ Y ∈ A, vanishingIdeal k Y) ≤ vanishingIdeal k ({x} : Set (σ → k)) :=
      iSup₂_le fun Y hY => vanishingIdeal_anti_mono (by simpa using hx Y hY)
    exact fun f hf => (mem_vanishingIdeal_singleton_iff x f).1 (hle hf)
  · -- Conversely each member is its own zero locus, so the point lands in it.
    intro hx Y hY
    rw [← (hA Y hY).zeroLocus_vanishingIdeal]
    exact fun f hf => hx f (le_iSup₂ (f := fun Y (_ : Y ∈ A) => vanishingIdeal k Y) Y hY hf)

/-- The **Zariski topology** on affine space: the closed sets are the algebraic
sets.

This is scoped rather than global. Affine space is the bare function type
`σ → k`, which already carries other topologies in Mathlib, so making this an
unconditional instance would silently change unrelated statements. Open the
`Hartshorne` scope to work in Chapter I's setting. -/
scoped instance zariskiTopology : TopologicalSpace (σ → k) :=
  TopologicalSpace.ofClosed {Y | IsAlgebraicSet Y} isAlgebraicSet_empty
    (fun _ hA => isAlgebraicSet_sInter hA)
    (fun _ hY _ hZ => hY.union hZ)

/-- A set is Zariski open exactly when its complement is algebraic. -/
theorem isOpen_iff_isAlgebraicSet_compl {U : Set (σ → k)} :
    IsOpen U ↔ IsAlgebraicSet Uᶜ :=
  Iff.rfl

/-- The closed sets of the Zariski topology are exactly the algebraic sets. -/
theorem isClosed_iff_isAlgebraicSet {Y : Set (σ → k)} :
    IsClosed Y ↔ IsAlgebraicSet Y := by
  rw [← isOpen_compl_iff, isOpen_iff_isAlgebraicSet_compl, compl_compl]

/-- Every zero set is Zariski closed. -/
theorem isClosed_zeroSet (T : Set (MvPolynomial σ k)) : IsClosed (zeroSet T) :=
  isClosed_iff_isAlgebraicSet.2 (isAlgebraicSet_zeroSet T)

end Hartshorne
