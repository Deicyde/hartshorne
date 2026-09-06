/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ConeDimension

/-!
# `dim Y = dim Yᵢ`, and `dim S(Y) = dim Y + 1`

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.6 (pp. 11-12).

A projective variety has the dimension of any nonempty chart piece, so the
algebraic computation `dim S(Y) = dim Yᵢ + 1` is a statement about `Y` itself.

One inequality is the general fact that a subspace has no larger dimension. The
other is where the charts have to be used together. A chain of irreducible
closed subsets of `Y` need not meet a *given* chart — its bottom term can be a
point outside `Uᵢ` — but it meets *some* chart, because the charts cover `ℙⁿ`
and every term of the chain contains the bottom one. So each chain is bounded by
`dim Y_j` for a `j` depending on the chain, and the algebraic computation is what
says all those bounds are the same number.

Mathlib supplies the step that would otherwise be the work: for an open
embedding, the irreducible closed subsets of the source correspond to those of
the target that meet it. Restricting a chain and taking closures back is
`IrreducibleCloseds.orderIsoOfIsOpenEmbedding`.

## Main results

* `Hartshorne.projDim_eq_dim_chart`
* `Hartshorne.ringKrullDim_homogeneousCoordinateRing_eq_projDim_add_one`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace Topology

section Chart

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- `φᵢ` is a homeomorphism from `Y ∩ Uᵢ` onto its image. -/
noncomputable def chartPieceHomeomorph (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    ↥(Y ∩ standardChart i) ≃ₜ ↥(chartMap i '' (Y ∩ standardChart i)) where
  toFun P := ⟨chartMap i P.1, ⟨P.1, P.2, rfl⟩⟩
  invFun y := ⟨chartInv i y.1,
    (chartMap_image_eq_chartInv_preimage i Y).subset y.2,
    chartInv_mem_standardChart i y.1⟩
  left_inv P := Subtype.ext (chartInv_chartMap P.2.2)
  right_inv y := Subtype.ext (chartMap_chartInv i y.1)
  continuous_toFun :=
    ((continuous_chartMap_restrict i).comp
      (continuous_inclusion (Set.inter_subset_right))).subtype_mk _
  continuous_invFun := ((continuous_chartInv i).comp continuous_subtype_val).subtype_mk _

/-- So the chart piece and its image have the same dimension. -/
theorem topologicalKrullDim_chartPiece (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    topologicalKrullDim ↥(Y ∩ standardChart i)
      = dim (chartMap i '' (Y ∩ standardChart i)) :=
  IsHomeomorph.topologicalKrullDim_eq _ (chartPieceHomeomorph i Y).isHomeomorph

omit [DecidableEq σ] in
/-- `Y ∩ Uᵢ` sits inside `Y` as an open subspace. -/
theorem isOpenEmbedding_chartInclusion (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    IsOpenEmbedding
      (Set.inclusion (Set.inter_subset_left : Y ∩ standardChart i ⊆ Y)) := by
  refine ⟨IsEmbedding.inclusion _, ?_⟩
  have hrange : Set.range (Set.inclusion (Set.inter_subset_left : Y ∩ standardChart i ⊆ Y))
      = Subtype.val ⁻¹' (standardChart i : Set (ProjectiveSpace k σ)) := by
    ext y
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.2.2, fun hy => ⟨⟨y.1, y.2, hy⟩, rfl⟩⟩
  rw [hrange]
  exact (isOpen_standardChart i).preimage continuous_subtype_val

/-- **The chart piece measures the irreducible closed subsets of `Y` that meet
it.** This is Mathlib's open-embedding correspondence, which is what makes the
chain argument below one line rather than a construction. -/
theorem topologicalKrullDim_chartPiece_eq_krullDim_meeting (i : σ)
    (Y : Set (ProjectiveSpace k σ)) :
    topologicalKrullDim ↥(Y ∩ standardChart i)
      = Order.krullDim {V : IrreducibleCloseds ↥Y |
          (Set.inclusion (Set.inter_subset_left : Y ∩ standardChart i ⊆ Y)
            ⁻¹' (V : Set ↥Y)).Nonempty} :=
  Order.krullDim_eq_of_orderIso
    (IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ (isOpenEmbedding_chartInclusion i Y))

end Chart

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {σ : Type} [Finite σ] [DecidableEq σ]
  {Y : Set (ProjectiveSpace k σ)}

/-- **All nonempty chart pieces of a projective variety have the same
dimension**, because each computes `dim S(Y) − 1`. -/
theorem dim_chart_eq_dim_chart (hY : IsProjVariety Y) (i j : σ)
    (hi : (Y ∩ standardChart i).Nonempty) (hj : (Y ∩ standardChart j).Nonempty) :
    dim (chartMap j '' (Y ∩ standardChart j)) = dim (chartMap i '' (Y ∩ standardChart i)) := by
  have hdi : IsDomain (coordinateRing (chartMap i '' (Y ∩ standardChart i))) :=
    isDomain_coordinateRing (isAffineVariety_chartMap_image i hY hi)
  have hdj : IsDomain (coordinateRing (chartMap j '' (Y ∩ standardChart j))) :=
    isDomain_coordinateRing (isAffineVariety_chartMap_image j hY hj)
  obtain ⟨mi, hmi, -⟩ := exists_ringKrullDim_eq_trdeg k
    (coordinateRing (chartMap i '' (Y ∩ standardChart i)))
    (FractionRing (coordinateRing (chartMap i '' (Y ∩ standardChart i))))
  obtain ⟨mj, hmj, -⟩ := exists_ringKrullDim_eq_trdeg k
    (coordinateRing (chartMap j '' (Y ∩ standardChart j)))
    (FractionRing (coordinateRing (chartMap j '' (Y ∩ standardChart j))))
  rw [← dim_eq_ringKrullDim_coordinateRing
    (isAffineVariety_chartMap_image i hY hi).isAlgebraicSet] at hmi
  rw [← dim_eq_ringKrullDim_coordinateRing
    (isAffineVariety_chartMap_image j hY hj).isAlgebraicSet] at hmj
  have hform := (ringKrullDim_homogeneousCoordinateRing j hY hj).symm.trans
    (ringKrullDim_homogeneousCoordinateRing i hY hi)
  rw [hmi, hmj] at hform ⊢
  have hnat : ((mj + 1 : ℕ) : WithBot ℕ∞) = ((mi + 1 : ℕ) : WithBot ℕ∞) := by
    push_cast
    exact hform
  have hsucc : mj + 1 = mi + 1 := by exact_mod_cast hnat
  have : mj = mi := by omega
  rw [this]

/-- **`dim Y ≤ dim Yᵢ`.**

A chain of irreducible closed subsets of `Y` meets whichever chart contains a
point of its bottom term, and every term of the chain contains that point. The
bound that chart gives is the same for every chart. -/
theorem projDim_le_dim_chart (hY : IsProjVariety Y) (i : σ)
    (hne : (Y ∩ standardChart i).Nonempty) :
    projDim Y ≤ dim (chartMap i '' (Y ∩ standardChart i)) := by
  rw [projDim_def, topologicalKrullDim, Order.krullDim]
  refine iSup_le fun l => ?_
  obtain ⟨P, hP⟩ := (l 0).isIrreducible.nonempty
  obtain ⟨j, hj⟩ := exists_mem_standardChart (P : ProjectiveSpace k σ)
  have hjne : (Y ∩ standardChart j).Nonempty := ⟨P.1, P.2, hj⟩
  have hmeet : ∀ m, (Set.inclusion (Set.inter_subset_left : Y ∩ standardChart j ⊆ Y)
      ⁻¹' (l m : Set ↥Y)).Nonempty := by
    intro m
    refine ⟨⟨P.1, P.2, hj⟩, ?_⟩
    show (⟨P.1, _⟩ : ↥Y) ∈ (l m : Set ↥Y)
    have : (⟨P.1, Set.inter_subset_left (⟨P.2, hj⟩ : (P : ProjectiveSpace k σ) ∈
        Y ∩ standardChart j)⟩ : ↥Y) = P := Subtype.ext rfl
    rw [this]
    exact l.monotone (Fin.zero_le m) hP
  have hchain : (l.length : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Y ∩ standardChart j) := by
    rw [topologicalKrullDim_chartPiece_eq_krullDim_meeting j Y]
    exact Order.LTSeries.length_le_krullDim
      ⟨l.length, fun m => ⟨l m, hmeet m⟩, fun m => l.step m⟩
  rw [topologicalKrullDim_chartPiece] at hchain
  exact hchain.trans (le_of_eq (dim_chart_eq_dim_chart hY i j hne hjne))

/-- **Exercise 2.6, geometric half**: a projective variety has the dimension of
any nonempty chart piece. -/
theorem projDim_eq_dim_chart (hY : IsProjVariety Y) (i : σ)
    (hne : (Y ∩ standardChart i).Nonempty) :
    projDim Y = dim (chartMap i '' (Y ∩ standardChart i)) := by
  refine le_antisymm (projDim_le_dim_chart hY i hne) ?_
  rw [← topologicalKrullDim_chartPiece, projDim_def]
  exact (IsEmbedding.inclusion
    (Set.inter_subset_left : Y ∩ standardChart i ⊆ Y)).isInducing.topologicalKrullDim_le

/-- **Exercise 2.6**: `dim S(Y) = dim Y + 1`. -/
theorem ringKrullDim_homogeneousCoordinateRing_eq_projDim_add_one (hY : IsProjVariety Y) :
    ringKrullDim (homogeneousCoordinateRing Y) = projDim Y + 1 := by
  obtain ⟨P, hP⟩ := hY.1.1
  obtain ⟨i, hi⟩ := exists_mem_standardChart P
  have hne : (Y ∩ standardChart i).Nonempty := ⟨P, hP, hi⟩
  rw [ringKrullDim_homogeneousCoordinateRing i hY hne, projDim_eq_dim_chart hY i hne]

end Hartshorne
