/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ProjChartDimension
import Hartshorne.Projective.IrreducibleSpace
import Hartshorne.Affine.QuasiAffineChainMap
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# `dim ℙⁿ = n`, and dimension is insensitive to closure

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.7 (p. 12).

Both halves fall out of Exercise 2.6.

For `ℙⁿ` itself, `J(ℙⁿ) = 0`, so `S(ℙⁿ)` is the polynomial ring in `n + 1`
variables, of dimension `n + 1`; subtracting the one from Exercise 2.6 leaves
`n`.

For a quasi-projective `Y`, one inequality is again that a subspace has no
larger dimension. The other goes through a chart: `φᵢ(Y ∩ Uᵢ)` is quasi-affine
and its closure is `φᵢ(Ȳ ∩ Uᵢ)`, because `φᵢ` is an open embedding and `Y ∩ Uᵢ`
is dense in `Y`. Proposition 1.10 says those two have the same dimension, and
Exercise 2.6 identifies the second with `dim Ȳ`.

So dimension can be computed on whichever of `Y` and `Ȳ` is convenient, which is
what later sections use.

## Main results

* `Hartshorne.projDim_univ_add_one`
* `Hartshorne.projDim_univ_fin`
* `Hartshorne.projDim_eq_projDim_closure`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace Topology

section Chart

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- `φᵢ⁻¹ : 𝔸ⁿ → ℙⁿ` is an open map, being a homeomorphism onto the open set
`Uᵢ`. -/
theorem isOpenMap_chartInv (i : σ) : IsOpenMap (chartInv (k := k) i) :=
  (IsOpen.isOpenMap_subtype_val (isOpen_standardChart i)).comp
    (chartHomeomorph i).symm.isOpenMap

/-- **Taking the closure commutes with restricting to a chart.**

`φᵢ` is an open embedding, so preimages along `φᵢ⁻¹` commute with closure, and
the chart piece is a preimage. -/
theorem closure_chartMap_image (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    closure (chartMap i '' (Y ∩ standardChart i))
      = chartMap i '' (closure Y ∩ standardChart i) := by
  rw [chartMap_image_eq_chartInv_preimage, chartMap_image_eq_chartInv_preimage]
  exact ((isOpenMap_chartInv i).preimage_closure_eq_closure_preimage
    (continuous_chartInv i) Y).symm

end Chart

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {σ : Type} [Finite σ] [DecidableEq σ]

/-- `S(ℙⁿ)` is the polynomial ring, `J(ℙⁿ)` being zero. -/
noncomputable def homogeneousCoordinateRingUnivEquiv [Nonempty σ] :
    homogeneousCoordinateRing (Set.univ : Set (ProjectiveSpace k σ)) ≃+* MvPolynomial σ k :=
  (Ideal.quotEquivOfEq homogeneousVanishingIdeal_univ).trans (RingEquiv.quotientBot _)

omit [Finite σ] [IsAlgClosed k] in
/-- Every chart of `ℙⁿ` is the whole of `𝔸ⁿ`. -/
theorem chartMap_image_univ (i : σ) :
    chartMap i '' ((Set.univ : Set (ProjectiveSpace k σ)) ∩ standardChart i) = Set.univ := by
  rw [chartMap_image_eq_chartInv_preimage, Set.preimage_univ]

omit [IsAlgClosed k] in
/-- Dropping one variable drops the count by one. -/
theorem card_subtype_ne_add_one (i : σ) : Nat.card {j : σ // j ≠ i} + 1 = Nat.card σ := by
  haveI : Fintype σ := Fintype.ofFinite σ
  haveI : Nonempty σ := ⟨i⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have := Fintype.card_pos (α := σ)
  omega

/-- **Exercise 2.7, first half**: `dim ℙⁿ = n`.

Every chart of `ℙⁿ` is all of `𝔸ⁿ`, so Exercise 2.6 reads off the dimension from
the affine space with one variable fewer. -/
theorem projDim_univ (i : σ) :
    projDim (Set.univ : Set (ProjectiveSpace k σ))
      = (Nat.card {j : σ // j ≠ i} : WithBot ℕ∞) := by
  have : Nonempty σ := ⟨i⟩
  have hne : ((Set.univ : Set (ProjectiveSpace k σ)) ∩ standardChart i).Nonempty :=
    ⟨chartInv i 0, Set.mem_univ _, chartInv_mem_standardChart i 0⟩
  rw [projDim_eq_dim_chart isProjVariety_univ i hne, chartMap_image_univ, dim_univ,
    dimAffineSpace_eq]

/-- The same, in the form `dim ℙⁿ + 1 = n + 1`. -/
theorem projDim_univ_add_one (i : σ) :
    projDim (Set.univ : Set (ProjectiveSpace k σ)) + 1 = (Nat.card σ : WithBot ℕ∞) := by
  rw [projDim_univ i, ← card_subtype_ne_add_one i]
  push_cast
  ring

/-- **`dim ℙⁿ = n`**, with the variables named. -/
theorem projDim_univ_fin (n : ℕ) :
    projDim (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) = (n : WithBot ℕ∞) := by
  rw [projDim_univ (0 : Fin (n + 1))]
  have hcard : Nat.card {j : Fin (n + 1) // j ≠ 0} = n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    simp
  rw [hcard]

/-- **Exercise 2.7, second half**: a quasi-projective variety has the dimension
of its closure. -/
theorem projDim_eq_projDim_closure {Y : Set (ProjectiveSpace k σ)}
    (hY : IsQuasiProjVariety Y) : projDim Y = projDim (closure Y) := by
  obtain ⟨P, hP⟩ := hY.isIrreducible.nonempty
  obtain ⟨i, hi⟩ := exists_mem_standardChart P
  have hne : (Y ∩ standardChart i).Nonempty := ⟨P, hP, hi⟩
  have hcl : IsProjVariety (closure Y) := ⟨hY.isIrreducible.closure, isClosed_closure⟩
  have hclne : (closure Y ∩ standardChart i).Nonempty := ⟨P, subset_closure hP, hi⟩
  refine le_antisymm ?_ ?_
  · rw [projDim_def, projDim_def]
    exact (IsEmbedding.inclusion
      (subset_closure : Y ⊆ closure Y)).isInducing.topologicalKrullDim_le
  · -- On the chart, Proposition 1.10 identifies the two dimensions.
    have hqa : IsQuasiAffineVariety (chartMap i '' (Y ∩ standardChart i)) :=
      isQuasiAffineVariety_chartMap_image i hY hne
    have hchart : dim (chartMap i '' (closure Y ∩ standardChart i))
        = dim (chartMap i '' (Y ∩ standardChart i)) := by
      rw [← closure_chartMap_image]
      exact (dim_eq_dim_closure hqa).symm
    rw [projDim_eq_dim_chart hcl i hclne, hchart, ← topologicalKrullDim_chartPiece,
      projDim_def]
    exact (IsEmbedding.inclusion
      (Set.inter_subset_left : Y ∩ standardChart i ⊆ Y)).isInducing.topologicalKrullDim_le

end Hartshorne
