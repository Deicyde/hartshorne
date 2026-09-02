/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Irreducible

/-!
# Projective algebraic sets and the Zariski topology on `ℙⁿ`

Hartshorne, *Algebraic Geometry*, I.2, Proposition 2.1 and the definitions
around it (pp. 9-10).

The development mirrors the affine case, with one difference that matters:
the defining family must consist of *homogeneous* polynomials. Dropping that
condition would still produce a topology, but a strictly finer one — the
non-homogeneous `x₀ - 1` cuts out a set that is not Zariski closed — so
homogeneity is carried in the definition rather than left as a side remark.

## Main definitions

* `Hartshorne.projZeroSet` : Hartshorne's `Z(T)` in projective space.
* `Hartshorne.IsProjAlgebraicSet`
* `Hartshorne.projZariskiTopology`

## Main results

* `Hartshorne.projZeroSet_union_projZeroSet` : Proposition 2.1's union case.
-/

namespace Hartshorne

open MvPolynomial Pointwise

variable {k : Type*} [Field k] {σ : Type*}

/-- A set of polynomials all of which are homogeneous of some degree. -/
def IsHomogeneousSet (T : Set (MvPolynomial σ k)) : Prop :=
  ∀ f ∈ T, ∃ n, f.IsHomogeneous n

theorem IsHomogeneousSet.mono {T₁ T₂ : Set (MvPolynomial σ k)} (h : T₁ ⊆ T₂)
    (hT : IsHomogeneousSet T₂) : IsHomogeneousSet T₁ :=
  fun f hf => hT f (h hf)

/-- Products of homogeneous families are homogeneous, which is what makes the
union case of Proposition 2.1 stay inside the homogeneous world. -/
theorem IsHomogeneousSet.mul {T₁ T₂ : Set (MvPolynomial σ k)}
    (h₁ : IsHomogeneousSet T₁) (h₂ : IsHomogeneousSet T₂) :
    IsHomogeneousSet (T₁ * T₂) := by
  rintro _ ⟨f, hf, g, hg, rfl⟩
  obtain ⟨m, hm⟩ := h₁ f hf
  obtain ⟨n, hn⟩ := h₂ g hg
  exact ⟨m + n, hm.mul hn⟩

/-- Hartshorne's `Z(T)`: the points of projective space at which every member of
`T` vanishes. -/
def projZeroSet (T : Set (MvPolynomial σ k)) : Set (ProjectiveSpace k σ) :=
  {P | ∀ f ∈ T, HomogeneousVanish f P}

@[simp]
theorem mem_projZeroSet_iff {T : Set (MvPolynomial σ k)} {P : ProjectiveSpace k σ} :
    P ∈ projZeroSet T ↔ ∀ f ∈ T, HomogeneousVanish f P :=
  Iff.rfl

theorem projZeroSet_anti_mono {T₁ T₂ : Set (MvPolynomial σ k)} (h : T₁ ⊆ T₂) :
    projZeroSet T₂ ⊆ projZeroSet T₁ :=
  fun _ hP f hf => hP f (h hf)

/-- A subset of projective space is an *algebraic set* when it is the zero set
of a family of homogeneous polynomials. -/
def IsProjAlgebraicSet (Y : Set (ProjectiveSpace k σ)) : Prop :=
  ∃ T : Set (MvPolynomial σ k), IsHomogeneousSet T ∧ Y = projZeroSet T

/-- The homogeneous polynomials vanishing on a set. Used the way the affine
development uses the vanishing ideal: it is the largest family cutting the set
out, so intersections can be handled without choosing a family for each
member. -/
def homogeneousVanishingSet (Y : Set (ProjectiveSpace k σ)) : Set (MvPolynomial σ k) :=
  {f | (∃ n, f.IsHomogeneous n) ∧ ∀ P ∈ Y, HomogeneousVanish f P}

theorem isHomogeneousSet_homogeneousVanishingSet (Y : Set (ProjectiveSpace k σ)) :
    IsHomogeneousSet (homogeneousVanishingSet Y) :=
  fun _ hf => hf.1

theorem subset_projZeroSet_homogeneousVanishingSet (Y : Set (ProjectiveSpace k σ)) :
    Y ⊆ projZeroSet (homogeneousVanishingSet Y) :=
  fun _ hP _ hf => hf.2 _ hP

/-- An algebraic set is cut out exactly by the homogeneous polynomials vanishing
on it. -/
theorem IsProjAlgebraicSet.projZeroSet_homogeneousVanishingSet
    {Y : Set (ProjectiveSpace k σ)} (h : IsProjAlgebraicSet Y) :
    projZeroSet (homogeneousVanishingSet Y) = Y := by
  obtain ⟨T, hT, rfl⟩ := h
  refine le_antisymm ?_ (subset_projZeroSet_homogeneousVanishingSet _)
  refine projZeroSet_anti_mono fun f hf => ⟨hT f hf, fun P hP => hP f hf⟩

theorem isProjAlgebraicSet_empty : IsProjAlgebraicSet (∅ : Set (ProjectiveSpace k σ)) := by
  refine ⟨{1}, fun f hf => ⟨0, by simpa using hf ▸ isHomogeneous_one σ k⟩, ?_⟩
  ext P
  simp [projZeroSet, HomogeneousVanish]

theorem isProjAlgebraicSet_univ :
    IsProjAlgebraicSet (Set.univ : Set (ProjectiveSpace k σ)) :=
  ⟨∅, by simp [IsHomogeneousSet], by ext P; simp [projZeroSet]⟩

/-- **Proposition 2.1**, union case: `Z(T₁) ∪ Z(T₂) = Z(T₁T₂)`. As in the affine
case this is the only part with content, and it uses that `k` is a domain. -/
theorem projZeroSet_union_projZeroSet (T₁ T₂ : Set (MvPolynomial σ k)) :
    projZeroSet T₁ ∪ projZeroSet T₂ = projZeroSet (T₁ * T₂) := by
  ext P
  simp only [Set.mem_union, mem_projZeroSet_iff, Set.mem_mul, HomogeneousVanish]
  constructor
  · rintro (h | h) _ ⟨f, hf, g, hg, rfl⟩ <;> simp [map_mul, h, hf, hg]
  · intro h
    by_contra hP
    push Not at hP
    obtain ⟨⟨f, hf, hfP⟩, ⟨g, hg, hgP⟩⟩ := hP
    exact mul_ne_zero hfP hgP (by simpa [map_mul] using h (f * g) ⟨f, hf, g, hg, rfl⟩)

theorem IsProjAlgebraicSet.union {Y Z : Set (ProjectiveSpace k σ)}
    (hY : IsProjAlgebraicSet Y) (hZ : IsProjAlgebraicSet Z) :
    IsProjAlgebraicSet (Y ∪ Z) := by
  obtain ⟨T₁, h₁, rfl⟩ := hY
  obtain ⟨T₂, h₂, rfl⟩ := hZ
  exact ⟨T₁ * T₂, h₁.mul h₂, projZeroSet_union_projZeroSet T₁ T₂⟩

/-- **Proposition 2.1**, intersection case. -/
theorem isProjAlgebraicSet_sInter {A : Set (Set (ProjectiveSpace k σ))}
    (hA : ∀ Y ∈ A, IsProjAlgebraicSet Y) : IsProjAlgebraicSet (⋂₀ A) := by
  refine ⟨⋃ Y ∈ A, homogeneousVanishingSet Y, ?_, ?_⟩
  · rintro f hf
    simp only [Set.mem_iUnion, exists_prop] at hf
    obtain ⟨Y, _, hfY⟩ := hf
    exact hfY.1
  · ext P
    simp only [Set.mem_sInter, mem_projZeroSet_iff, Set.mem_iUnion, exists_prop]
    constructor
    · rintro hP f ⟨Y, hY, hfY⟩
      exact hfY.2 P (hP Y hY)
    · intro hP Y hY
      rw [← (hA Y hY).projZeroSet_homogeneousVanishingSet]
      exact fun f hf => hP f ⟨Y, hY, hf⟩

/-- The **Zariski topology** on projective space: the closed sets are the
algebraic sets. Scoped, for the same reason as the affine one. -/
scoped instance projZariskiTopology : TopologicalSpace (ProjectiveSpace k σ) :=
  TopologicalSpace.ofClosed {Y | IsProjAlgebraicSet Y} isProjAlgebraicSet_empty
    (fun _ hA => isProjAlgebraicSet_sInter hA)
    (fun _ hY _ hZ => hY.union hZ)

theorem isOpen_iff_isProjAlgebraicSet_compl {U : Set (ProjectiveSpace k σ)} :
    IsOpen U ↔ IsProjAlgebraicSet Uᶜ :=
  Iff.rfl

theorem isClosed_iff_isProjAlgebraicSet {Y : Set (ProjectiveSpace k σ)} :
    IsClosed Y ↔ IsProjAlgebraicSet Y := by
  rw [← isOpen_compl_iff, isOpen_iff_isProjAlgebraicSet_compl, compl_compl]

/-- The standard charts are open, since their complements are the hyperplanes
`Z(Xᵢ)`. -/
theorem isOpen_standardChart (i : σ) : IsOpen (standardChart i : Set (ProjectiveSpace k σ)) := by
  rw [isOpen_iff_isProjAlgebraicSet_compl]
  refine ⟨{X i}, fun f hf => ⟨1, by simpa using hf ▸ isHomogeneous_X k i⟩, ?_⟩
  ext P
  simp [standardChart, projZeroSet]

end Hartshorne
