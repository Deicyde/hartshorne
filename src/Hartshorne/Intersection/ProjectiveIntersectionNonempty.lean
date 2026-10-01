/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.AffineConeDimension
import Hartshorne.Intersection.AffineDimensionTheorem

/-!
# Projective varieties of complementary dimension meet

Hartshorne, *Algebraic Geometry*, I.7, Theorem 7.2 (pp. 48–49),
nonemptiness clause.

If projective varieties `Y, Z ⊆ P^n` have natural dimensions `r, s` and
`n ≤ r + s`, then `Y ∩ Z` is nonempty.
-/

namespace Hartshorne

open Set TopologicalSpace Topology

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Theorem I.7.2, nonemptiness clause.** Two projective varieties in
`P^n` whose natural dimensions sum to at least `n` meet. -/
theorem projective_inter_nonempty_of_dim
    {n r s : Nat}
    {Y Z : Set (ProjectiveSpace k (Fin (n + 1)))}
    (hY : IsProjVariety Y) (hZ : IsProjVariety Z)
    (hYdim : projDim Y = (r : WithBot ENat))
    (hZdim : projDim Z = (s : WithBot ENat))
    (hdim : n ≤ r + s) :
    (Y ∩ Z).Nonempty := by
  classical
  let CY := affineCone Y
  let CZ := affineCone Z
  have hCY : IsAffineVariety CY := hY.isAffineVariety_affineCone
  have hCZ : IsAffineVariety CZ := hZ.isAffineVariety_affineCone
  have hzeroY : (0 : Fin (n + 1) → k) ∈ CY := by
    exact Or.inl rfl
  have hzeroZ : (0 : Fin (n + 1) → k) ∈ CZ := by
    exact Or.inl rfl
  let zeroPoint : ↥(CY ∩ CZ) := ⟨0, hzeroY, hzeroZ⟩
  let W : irreducibleComponents ↥(CY ∩ CZ) :=
    ⟨irreducibleComponent zeroPoint,
      irreducibleComponent_mem_irreducibleComponents zeroPoint⟩
  have hbound := affine_dimension_theorem hCY hCZ W
  have hCYdim : dim CY = ((r + 1 : Nat) : WithBot ENat) := by
    rw [show CY = affineCone Y from rfl,
      dim_affineCone hY.isProjAlgebraicSet hY.1.nonempty, hYdim]
    push_cast
    ring
  have hCZdim : dim CZ = ((s + 1 : Nat) : WithBot ENat) := by
    rw [show CZ = affineCone Z from rfl,
      dim_affineCone hZ.isProjAlgebraicSet hZ.1.nonempty, hZdim]
    push_cast
    ring
  rw [hCYdim, hCZdim, Nat.card_fin] at hbound

  have hnonzero : ∃ v ∈ affineComponentCarrier W.1, v ≠ 0 := by
    by_contra h
    push Not at h
    have hsub : affineComponentCarrier W.1 ⊆
        ({0} : Set (Fin (n + 1) → k)) := by
      intro v hv
      exact Set.mem_singleton_iff.mpr (h v hv)
    have hdimSingleton : dim ({0} : Set (Fin (n + 1) → k)) ≤ 0 := by
      change topologicalKrullDim ({0} : Set (Fin (n + 1) → k)) ≤ 0
      exact topologicalKrullDim_zero_of_discreteTopology _
    have hcomponentZero : dim (affineComponentCarrier W.1) ≤ 0 :=
      (dim_le_of_subset hsub).trans hdimSingleton
    have hnumeric := hbound.trans (add_le_add_left hcomponentZero (n + 1))
    have hnat : r + 1 + (s + 1) ≤ 0 + (n + 1) := by
      exact_mod_cast hnumeric
    omega

  obtain ⟨v, hvW, hvne⟩ := hnonzero
  obtain ⟨w, hwW, rfl⟩ := hvW
  have hwCone : (w : Fin (n + 1) → k) ∈ CY ∩ CZ := w.2
  have hwY : Projectivization.mk k w.1 hvne ∈ Y := by
    rcases hwCone.1 with hw0 | ⟨_, hwY⟩
    · exact absurd hw0 hvne
    · exact hwY
  have hwZ : Projectivization.mk k w.1 hvne ∈ Z := by
    rcases hwCone.2 with hw0 | ⟨_, hwZ⟩
    · exact absurd hw0 hvne
    · exact hwZ
  exact ⟨Projectivization.mk k w.1 hvne, hwY, hwZ⟩

end

end Hartshorne
