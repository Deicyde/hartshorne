/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Homogenize
import Hartshorne.Projective.Variety
import Hartshorne.Affine.Variety

/-!
# Varieties are covered by affine pieces

Hartshorne, *Algebraic Geometry*, I.2, Corollary 2.3 (p. 11).

Every projective variety is covered by the open sets `Y ∩ Uᵢ`, and each is
carried by `φᵢ` to an affine variety; for quasi-projective `Y` the pieces are
quasi-affine. Together with Proposition 2.2 this is the statement that
projective geometry is locally affine, which organises the rest of the book.

The image `φᵢ(Y ∩ Uᵢ)` is just `φᵢ⁻¹⁻¹(Y)`, so closedness comes straight from
continuity of `φᵢ⁻¹` rather than from any image-of-closed argument.

## Main results

* `Hartshorne.iUnion_standardChart` : the charts cover `ℙⁿ`.
* `Hartshorne.isAffineVariety_chartMap_image` : Corollary 2.3.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- The standard charts cover projective space. -/
theorem iUnion_standardChart :
    (⋃ i : σ, standardChart i : Set (ProjectiveSpace k σ)) = Set.univ := by
  ext P
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact exists_mem_standardChart P

/-- The chart image of `Y ∩ Uᵢ` is the preimage of `Y` under `φᵢ⁻¹`.

This is the observation that makes Corollary 2.3 short: closedness of the image
becomes continuity of `φᵢ⁻¹`, with no image-of-a-closed-set argument. -/
theorem chartMap_image_eq_chartInv_preimage (i : σ) (Y : Set (ProjectiveSpace k σ)) :
    chartMap i '' (Y ∩ standardChart i) = chartInv i ⁻¹' Y := by
  ext y
  constructor
  · rintro ⟨P, ⟨hPY, hPc⟩, rfl⟩
    rw [Set.mem_preimage, chartInv_chartMap hPc]
    exact hPY
  · intro hy
    exact ⟨chartInv i y, ⟨hy, chartInv_mem_standardChart i y⟩, chartMap_chartInv i y⟩

/-- `φᵢ` is continuous on its chart. -/
theorem continuousOn_chartMap (i : σ) :
    ContinuousOn (chartMap (k := k) i) (standardChart i) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_chartMap_restrict i

/-- **Corollary 2.3**: each nonempty piece `Y ∩ Uᵢ` of a projective variety is
carried by `φᵢ` to an affine variety. -/
theorem isAffineVariety_chartMap_image (i : σ) {Y : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) (hne : (Y ∩ standardChart i).Nonempty) :
    IsAffineVariety (chartMap i '' (Y ∩ standardChart i)) := by
  refine ⟨?_, ?_⟩
  · refine IsIrreducible.image ⟨hne, ?_⟩ _
      ((continuousOn_chartMap i).mono Set.inter_subset_right)
    exact IsPreirreducible.inter_isOpen hY.1.2 (isOpen_standardChart i)
  · rw [chartMap_image_eq_chartInv_preimage]
    exact hY.2.preimage (continuous_chartInv i)

/-- The quasi-projective case: each nonempty piece is carried to a quasi-affine
variety. -/
theorem isQuasiAffineVariety_chartMap_image (i : σ) {Y : Set (ProjectiveSpace k σ)}
    (hY : IsQuasiProjVariety Y) (hne : (Y ∩ standardChart i).Nonempty) :
    IsQuasiAffineVariety (chartMap i '' (Y ∩ standardChart i)) := by
  obtain ⟨-, V, U, hV, hU, rfl⟩ := hY
  have hVne : (V ∩ standardChart i).Nonempty :=
    hne.mono fun _ hx => ⟨hx.1.1, hx.2⟩
  refine ⟨hne.image _, chartMap i '' (V ∩ standardChart i),
    chartInv i ⁻¹' U, isAffineVariety_chartMap_image i hV hVne,
    hU.preimage (continuous_chartInv i), ?_⟩
  rw [chartMap_image_eq_chartInv_preimage, chartMap_image_eq_chartInv_preimage,
    Set.preimage_inter]

end Hartshorne
