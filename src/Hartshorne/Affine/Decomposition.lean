/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Noetherian
import Hartshorne.Affine.Variety

/-!
# Decomposition into irreducible components

Hartshorne, *Algebraic Geometry*, I.1, Proposition 1.5 and Corollary 1.6 (p. 5).

Every nonempty closed subset of a Noetherian space is a finite union of
irreducible closed subsets, and if no member contains another the members are
uniquely determined. Specialised to affine space, every algebraic set is
uniquely a finite union of affine varieties, none containing another.

Mathlib proves existence, as
`TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`, but
without irredundancy and without uniqueness. Those are the content here.

## Main results

* `Hartshorne.IsIrreducible.exists_mem_subset_of_subset_biUnion` : an irreducible
  set inside a finite union of closed sets lies inside one of them. This is the
  engine for both irredundancy and uniqueness.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

/-- An irreducible set contained in a finite union of closed sets is contained
in one of them.

This is the finite-union form of irreducibility, and it is what makes the
decomposition of Proposition 1.5 unique: it lets two decompositions be compared
member by member. -/
theorem IsIrreducible.exists_mem_subset_of_subset_biUnion {X : Type*} [TopologicalSpace X]
    {Z : Set X} (hZ : IsIrreducible Z) (S : Finset (Set X))
    (hclosed : ∀ t ∈ S, IsClosed t) (hsub : Z ⊆ ⋃ t ∈ S, t) :
    ∃ t ∈ S, Z ⊆ t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hempty : Z ⊆ (∅ : Set X) := by simpa using hsub
      exact absurd (hZ.nonempty.mono hempty) (by simp)
  | insert t S ht ih =>
      rw [Finset.set_biUnion_insert] at hsub
      have hct : IsClosed t := hclosed t (Finset.mem_insert_self t S)
      have hcS : IsClosed (⋃ s ∈ S, s) :=
        S.finite_toSet.isClosed_biUnion fun s hs =>
          hclosed s (Finset.mem_insert_of_mem hs)
      rcases isPreirreducible_iff_isClosed_union_isClosed.1 hZ.2 t (⋃ s ∈ S, s)
        hct hcS hsub with h | h
      · exact ⟨t, Finset.mem_insert_self t S, h⟩
      · obtain ⟨s, hs, hZs⟩ :=
          ih (fun s hs => hclosed s (Finset.mem_insert_of_mem hs)) h
        exact ⟨s, Finset.mem_insert_of_mem hs, hZs⟩

/-- Any finite family can be pruned to an irredundant subfamily with the same
union: repeatedly discard a member contained in another. -/
theorem exists_irredundant_subfamily {X : Type*} (S : Finset (Set X)) :
    ∃ T ⊆ S, (⋃ t ∈ T, t) = (⋃ t ∈ S, t) ∧ ∀ t ∈ T, ∀ u ∈ T, t ⊆ u → t = u := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    by_cases hanti : ∀ t ∈ S, ∀ u ∈ S, t ⊆ u → t = u
    · exact ⟨S, Finset.Subset.refl S, rfl, hanti⟩
    · push Not at hanti
      obtain ⟨t, htS, u, huS, htu, hne⟩ := hanti
      obtain ⟨T, hTsub, hTunion, hTanti⟩ := ih (S.erase t) (Finset.erase_ssubset htS)
      refine ⟨T, hTsub.trans (Finset.erase_subset _ _), ?_, hTanti⟩
      rw [hTunion]
      refine le_antisymm (Set.biUnion_subset_biUnion_left (Finset.erase_subset _ _)) ?_
      intro x hx
      simp only [Set.mem_iUnion, exists_prop] at hx ⊢
      obtain ⟨s, hsS, hxs⟩ := hx
      by_cases hst : s = t
      · exact ⟨u, Finset.mem_erase.2 ⟨fun h => hne h.symm, huS⟩, htu (hst ▸ hxs)⟩
      · exact ⟨s, Finset.mem_erase.2 ⟨hst, hsS⟩, hxs⟩

/-- **Hartshorne 1.5**, uniqueness. Two irredundant decompositions of the same
set into irreducible closed pieces have the same members.

Each member of one decomposition sits inside a member of the other, which sits
inside a member of the first; irredundancy collapses the sandwich. -/
theorem irredundant_decomposition_unique {X : Type*} [TopologicalSpace X]
    {Y : Set X} {S T : Finset (Set X)}
    (hSc : ∀ t ∈ S, IsClosed t) (hSi : ∀ t ∈ S, IsIrreducible t)
    (hSu : Y = ⋃ t ∈ S, t) (hSa : ∀ t ∈ S, ∀ u ∈ S, t ⊆ u → t = u)
    (hTc : ∀ t ∈ T, IsClosed t) (hTi : ∀ t ∈ T, IsIrreducible t)
    (hTu : Y = ⋃ t ∈ T, t) (hTa : ∀ t ∈ T, ∀ u ∈ T, t ⊆ u → t = u) :
    S = T := by
  have mem_union : ∀ (A : Finset (Set X)) (t : Set X), t ∈ A → t ⊆ ⋃ s ∈ A, s := by
    intro A t htA x hx
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨t, htA, hx⟩
  have key : ∀ (A B : Finset (Set X)),
      (∀ t ∈ A, IsClosed t) → (∀ t ∈ A, IsIrreducible t) → (Y = ⋃ t ∈ A, t) →
      (∀ t ∈ A, ∀ u ∈ A, t ⊆ u → t = u) →
      (∀ t ∈ B, IsClosed t) → (∀ t ∈ B, IsIrreducible t) → (Y = ⋃ t ∈ B, t) →
      A ⊆ B := by
    intro A B hAc hAi hAu hAa hBc hBi hBu t htA
    -- `t` lands inside some member `u` of `B` ...
    have htB : t ⊆ ⋃ s ∈ B, s := by rw [← hBu, hAu]; exact mem_union A t htA
    obtain ⟨u, huB, htu⟩ :=
      IsIrreducible.exists_mem_subset_of_subset_biUnion (hAi t htA) B hBc htB
    -- ... and that `u` lands inside some member `v` of `A`.
    have huA : u ⊆ ⋃ s ∈ A, s := by rw [← hAu, hBu]; exact mem_union B u huB
    obtain ⟨v, hvA, huv⟩ :=
      IsIrreducible.exists_mem_subset_of_subset_biUnion (hBi u huB) A hAc huA
    -- `t ⊆ u ⊆ v` with `t, v ∈ A`, so irredundancy of `A` collapses the sandwich.
    have htv : t = v := hAa t htA v hvA (htu.trans huv)
    have hut : u = t := subset_antisymm (htv ▸ huv) htu
    exact hut ▸ huB
  exact Finset.Subset.antisymm
    (key S T hSc hSi hSu hSa hTc hTi hTu) (key T S hTc hTi hTu hTa hSc hSi hSu)

/-- **Hartshorne 1.5**: in a Noetherian space every closed set is a finite union
of irreducible closed sets, irredundantly, and the family is unique. -/
theorem exists_unique_irredundant_decomposition {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {Y : Set X} (hY : IsClosed Y) :
    ∃! S : Finset (Set X), (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧
      Y = ⋃ t ∈ S, t ∧ ∀ t ∈ S, ∀ u ∈ S, t ⊆ u → t = u := by
  classical
  obtain ⟨S₀, hfin, hcl, hirr, hUn⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hY
  lift S₀ to Finset (Set X) using hfin
  obtain ⟨T, hTsub, hTunion, hTanti⟩ := exists_irredundant_subfamily S₀
  have hYT : Y = ⋃ t ∈ T, t := by
    rw [hTunion, hUn, Set.sUnion_eq_biUnion]
    simp
  refine ⟨T, ⟨fun t ht => hcl t (hTsub ht), fun t ht => hirr t (hTsub ht), hYT, hTanti⟩, ?_⟩
  rintro S ⟨hSc, hSi, hSu, hSa⟩
  exact irredundant_decomposition_unique hSc hSi hSu hSa
    (fun t ht => hcl t (hTsub ht)) (fun t ht => hirr t (hTsub ht)) hYT hTanti

variable {k : Type*} [Field k] {σ : Type*}

/-- **Hartshorne 1.6**: every algebraic set in affine space is uniquely a finite
union of affine varieties, none containing another. -/
theorem IsAlgebraicSet.exists_unique_decomposition [Finite σ] {Y : Set (σ → k)}
    (hY : IsAlgebraicSet Y) :
    ∃! S : Finset (Set (σ → k)), (∀ t ∈ S, IsAffineVariety t) ∧
      Y = ⋃ t ∈ S, t ∧ ∀ t ∈ S, ∀ u ∈ S, t ⊆ u → t = u := by
  obtain ⟨S, ⟨hSc, hSi, hSu, hSa⟩, huniq⟩ :=
    exists_unique_irredundant_decomposition (isClosed_iff_isAlgebraicSet.2 hY)
  refine ⟨S, ⟨fun t ht => ⟨hSi t ht, hSc t ht⟩, hSu, hSa⟩, ?_⟩
  rintro T ⟨hTv, hTu, hTa⟩
  exact huniq T ⟨fun t ht => (hTv t ht).2, fun t ht => (hTv t ht).1, hTu, hTa⟩

end Hartshorne
