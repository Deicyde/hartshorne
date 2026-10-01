/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.AffineConeIrreducible
import Hartshorne.Projective.ProjChartDimension

/-!
# Dimension of the affine cone

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.10(c) (p. 12).

For a nonempty projective algebraic set `Y`, its affine cone has dimension
`projDim Y + 1`.  The irreducible case follows by identifying the affine
coordinate ring of the cone with the homogeneous coordinate ring of `Y`.
The general case follows from the finite irreducible decomposition and the
fact that the dimension of a finite closed union is the maximum of the
dimensions of its members.

## Main result

* `Hartshorne.dim_affineCone`
-/

namespace Hartshorne

open MvPolynomial Set TopologicalSpace

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {σ : Type} [Finite σ]

/-- The dimension of a nonempty finite union of closed subsets is attained by
one of the subsets. -/
private theorem exists_topologicalKrullDim_eq_of_finite_closed_iUnion
    {X : Type*} [TopologicalSpace X] (S : Finset (Set X))
    (hS : S.Nonempty) (hclosed : ∀ t ∈ S, IsClosed t) :
    ∃ t ∈ S,
      topologicalKrullDim (⋃ t ∈ S, t) = topologicalKrullDim t := by
  classical
  obtain ⟨t, htS, htmax⟩ :=
    Finset.exists_max_image S (fun t : Set X => topologicalKrullDim t) hS
  refine ⟨t, htS, le_antisymm ?_ ?_⟩
  · have hUclosed : IsClosed (⋃ u ∈ S, u) :=
      S.finite_toSet.isClosed_biUnion fun u hu => hclosed u hu
    rw [topologicalKrullDim_subtype_eq hUclosed, Order.krullDim]
    refine iSup_le fun p => ?_
    obtain ⟨u, huS, hlast⟩ :=
      IsIrreducible.exists_mem_subset_of_subset_biUnion
        p.last.1.isIrreducible S hclosed p.last.2
    let q : LTSeries
        {Z : IrreducibleCloseds X // (Z : Set X) ⊆ u} :=
      LTSeries.mk p.length
        (fun i => ⟨(p i).1,
          (show ((p i).1 : Set X) ⊆ (p.last).1 from
            p.monotone (Fin.le_last i)).trans hlast⟩)
        (fun _ _ hij => p.strictMono hij)
    have hp_u : (p.length : WithBot ℕ∞) ≤ topologicalKrullDim u := by
      rw [topologicalKrullDim_subtype_eq (hclosed u huS), Order.krullDim]
      exact le_iSup_of_le q (le_of_eq rfl)
    exact hp_u.trans (htmax u huS)
  · have hsub : t ⊆ ⋃ u ∈ S, u := by
      intro x hx
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨t, htS, hx⟩
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le

/-- The affine cone over a projective variety has dimension one more than the
variety. -/
private theorem dim_affineCone_of_isProjVariety
    {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y) :
    dim (affineCone Y) = projDim Y + 1 := by
  classical
  rw [dim_eq_ringKrullDim_coordinateRing
      (isAlgebraicSet_affineCone hY.isProjAlgebraicSet hY.1.nonempty)]
  let e : coordinateRing (affineCone Y) ≃+* homogeneousCoordinateRing Y :=
    Ideal.quotEquivOfEq
      (vanishingIdeal_affineCone hY.isProjAlgebraicSet hY.1.nonempty)
  rw [ringKrullDim_eq_of_ringEquiv e,
    ringKrullDim_homogeneousCoordinateRing_eq_projDim_add_one hY]

/-- **Exercise I.2.10(c).** The affine cone over a nonempty projective
algebraic set has dimension one more than the projective algebraic set. -/
theorem dim_affineCone {Y : Set (ProjectiveSpace k σ)}
    (hY : IsProjAlgebraicSet Y) (hne : Y.Nonempty) :
    dim (affineCone Y) = projDim Y + 1 := by
  classical
  obtain ⟨S, ⟨hSvariety, hYunion, -⟩, -⟩ := hY.exists_unique_decomposition
  have hS : S.Nonempty := by
    obtain ⟨P, hPY⟩ := hne
    have hPunion : P ∈ ⋃ t ∈ S, t := by
      rw [← hYunion]
      exact hPY
    simp only [Set.mem_iUnion, exists_prop] at hPunion
    obtain ⟨t, htS, -⟩ := hPunion
    exact ⟨t, htS⟩

  obtain ⟨V, hVS, hdimV⟩ :=
    exists_topologicalKrullDim_eq_of_finite_closed_iUnion S hS
      (fun t ht => (hSvariety t ht).2)
  have hprojV : projDim Y = projDim V := by
    change topologicalKrullDim Y = topologicalKrullDim V
    rw [hYunion]
    exact hdimV

  have hconeUnionDirect : affineCone Y = ⋃ t ∈ S, affineCone t := by
    ext v
    change (v = 0 ∨ ∃ hv : v ≠ 0, Projectivization.mk k v hv ∈ Y) ↔ _
    constructor
    · rintro (rfl | ⟨hv, hvY⟩)
      · obtain ⟨t, htS⟩ := hS
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨t, htS, Or.inl rfl⟩
      · have hvUnion : Projectivization.mk k v hv ∈ ⋃ t ∈ S, t := by
          rw [← hYunion]
          exact hvY
        simp only [Set.mem_iUnion, exists_prop] at hvUnion ⊢
        obtain ⟨t, htS, hvt⟩ := hvUnion
        exact ⟨t, htS, Or.inr ⟨hv, hvt⟩⟩
    · simp only [Set.mem_iUnion, exists_prop]
      rintro ⟨t, htS, rfl | ⟨hv, hvt⟩⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨hv, ?_⟩
        rw [hYunion]
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨t, htS, hvt⟩

  let C : Finset (Set (σ → k)) := S.image affineCone
  have hC : C.Nonempty := hS.image affineCone
  have hCclosed : ∀ c ∈ C, IsClosed c := by
    intro c hc
    obtain ⟨t, htS, rfl⟩ := Finset.mem_image.1 hc
    exact (hSvariety t htS).isAffineVariety_affineCone.2
  obtain ⟨c, hcC, hdimc⟩ :=
    exists_topologicalKrullDim_eq_of_finite_closed_iUnion C hC hCclosed
  obtain ⟨W, hWS, rfl⟩ := Finset.mem_image.1 hcC
  have hconeUnion : affineCone Y = ⋃ c ∈ C, c := by
    rw [hconeUnionDirect]
    ext v
    simp only [C, Finset.mem_image, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨t, htS, hvt⟩
      exact ⟨affineCone t, ⟨t, htS, rfl⟩, hvt⟩
    · rintro ⟨_, ⟨t, htS, rfl⟩, hvt⟩
      exact ⟨t, htS, hvt⟩
  have hconeW : dim (affineCone Y) = dim (affineCone W) := by
    change topologicalKrullDim (affineCone Y) = topologicalKrullDim (affineCone W)
    rw [hconeUnion]
    exact hdimc

  have hVY : V ⊆ Y := by
    rw [hYunion]
    intro P hPV
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨V, hVS, hPV⟩
  have hWY : W ⊆ Y := by
    rw [hYunion]
    intro P hPW
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨W, hWS, hPW⟩
  have hconeVY : affineCone V ⊆ affineCone Y := by
    intro v hv
    change v = 0 ∨ ∃ hv : v ≠ 0, Projectivization.mk k v hv ∈ V at hv
    change v = 0 ∨ ∃ hv : v ≠ 0, Projectivization.mk k v hv ∈ Y
    exact hv.imp_right fun ⟨hv, hvV⟩ => ⟨hv, hVY hvV⟩
  have hdimConeVle : dim (affineCone V) ≤ dim (affineCone Y) :=
    (Topology.IsEmbedding.inclusion hconeVY).isInducing.topologicalKrullDim_le
  have hprojWle : projDim W ≤ projDim Y :=
    (Topology.IsEmbedding.inclusion hWY).isInducing.topologicalKrullDim_le

  apply le_antisymm
  · calc
      dim (affineCone Y) = dim (affineCone W) := hconeW
      _ = projDim W + 1 := dim_affineCone_of_isProjVariety (hSvariety W hWS)
      _ ≤ projDim Y + 1 := add_le_add_left hprojWle 1
  · calc
      projDim Y + 1 = projDim V + 1 := by rw [hprojV]
      _ = dim (affineCone V) :=
        (dim_affineCone_of_isProjVariety (hSvariety V hVS)).symm
      _ ≤ dim (affineCone Y) := hdimConeVle

end

end Hartshorne
