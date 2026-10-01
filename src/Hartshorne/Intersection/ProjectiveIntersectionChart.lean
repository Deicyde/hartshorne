/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ProjChartDimension

/-!
# Projective intersection components on an affine chart

Hartshorne, *Algebraic Geometry*, I.7, proof of Theorem 7.2 (p. 48).

An irreducible component of a projective intersection remains an irreducible
component after restriction to any standard affine chart that it meets.  The
chart homeomorphism transports that component to the intersection of the two
affine chart pieces, and all three projective varieties keep their dimensions.

## Main result

* `Hartshorne.projectiveIntersectionComponent_chart`
-/

namespace Hartshorne

open MvPolynomial Set TopologicalSpace Topology

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {σ : Type} [Finite σ] [DecidableEq σ]

/-- The ambient carrier of a subset of a subspace. -/
def projectiveComponentCarrier {S : Set (ProjectiveSpace k σ)}
    (W : Set S) : Set (ProjectiveSpace k σ) :=
  Subtype.val '' W

/-- The chart homeomorphism, with its range written as the intersection of
the two affine chart pieces. -/
def projectiveIntersectionChartHomeomorph (i : σ)
    (Y Z : Set (ProjectiveSpace k σ)) :
    ↥((Y ∩ Z) ∩ standardChart i) ≃ₜ
      ↥((chartMap i '' (Y ∩ standardChart i)) ∩
        (chartMap i '' (Z ∩ standardChart i))) where
  toFun P := ⟨chartMap i P.1, ⟨
    ⟨P.1, ⟨P.2.1.1, P.2.2⟩, rfl⟩,
    ⟨P.1, ⟨P.2.1.2, P.2.2⟩, rfl⟩⟩⟩
  invFun y := ⟨chartInv i y.1, ⟨⟨
    (chartMap_image_eq_chartInv_preimage i Y).subset y.2.1,
    (chartMap_image_eq_chartInv_preimage i Z).subset y.2.2⟩,
    chartInv_mem_standardChart i y.1⟩⟩
  left_inv P := Subtype.ext (chartInv_chartMap P.2.2)
  right_inv y := Subtype.ext (chartMap_chartInv i y.1)
  continuous_toFun :=
    ((continuous_chartMap_restrict i).comp
      (continuous_inclusion (Set.inter_subset_right))).subtype_mk _
  continuous_invFun := ((continuous_chartInv i).comp continuous_subtype_val).subtype_mk _

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] in
/-- A relative irreducible component is a projective variety in the ambient
projective space when the containing subspace is closed. -/
theorem isProjVariety_projectiveComponentCarrier
    {S : Set (ProjectiveSpace k σ)} (hS : IsClosed S)
    (W : irreducibleComponents S) :
    IsProjVariety (projectiveComponentCarrier W.1) := by
  refine ⟨?_, ?_⟩
  · exact W.2.1.image Subtype.val continuous_subtype_val.continuousOn
  · exact hS.isClosedMap_subtype_val W.1
      (isClosed_of_mem_irreducibleComponents W.1 W.2)

/-- **Hartshorne I.7, affine-chart reduction.** If `W` is an irreducible
component of `Y ∩ Z` and the chart `Uᵢ` meets `W`, then its chart image is
the carrier of an irreducible component of `Yᵢ ∩ Zᵢ`.  The chart pieces of
`Y`, `Z`, and `W` have the same dimensions as their projective counterparts. -/
theorem projectiveIntersectionComponent_chart
    {Y Z : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) (hZ : IsProjVariety Z)
    (W : irreducibleComponents ↥(Y ∩ Z)) (i : σ)
    (hi : (projectiveComponentCarrier W.1 ∩ standardChart i).Nonempty) :
    ∃ C : irreducibleComponents
        ↥((chartMap i '' (Y ∩ standardChart i)) ∩
          (chartMap i '' (Z ∩ standardChart i))),
      Subtype.val '' C.1 =
          chartMap i '' (projectiveComponentCarrier W.1 ∩ standardChart i) ∧
      projDim Y = dim (chartMap i '' (Y ∩ standardChart i)) ∧
      projDim Z = dim (chartMap i '' (Z ∩ standardChart i)) ∧
      projDim (projectiveComponentCarrier W.1) =
        dim (chartMap i ''
          (projectiveComponentCarrier W.1 ∩ standardChart i)) := by
  let inclusion : ↥((Y ∩ Z) ∩ standardChart i) → ↥(Y ∩ Z) :=
    Set.inclusion Set.inter_subset_left
  have hopen : IsOpenEmbedding inclusion :=
    isOpenEmbedding_chartInclusion i (Y ∩ Z)
  obtain ⟨P, hPW, hPi⟩ := hi
  obtain ⟨w, hwW, rfl⟩ := hPW
  have hmeet : (W.1 ∩ Set.range inclusion).Nonempty := by
    refine ⟨w, hwW, ?_⟩
    refine ⟨⟨w.1, w.2, hPi⟩, ?_⟩
    exact Subtype.ext rfl
  have hrestricted : inclusion ⁻¹' W.1 ∈
      irreducibleComponents ↥((Y ∩ Z) ∩ standardChart i) :=
    preimage_mem_irreducibleComponents W.2 hopen hmeet
  let e := projectiveIntersectionChartHomeomorph i Y Z
  have himage : e '' (inclusion ⁻¹' W.1) ∈
      irreducibleComponents
        ↥((chartMap i '' (Y ∩ standardChart i)) ∩
          (chartMap i '' (Z ∩ standardChart i))) :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber
      e e.continuous e.isOpenMap
        (fun _ ↦ (subsingleton_singleton.preimage e.injective).isPreirreducible)
        e.surjective hrestricted
  refine ⟨⟨e '' (inclusion ⁻¹' W.1), himage⟩, ?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, ⟨x, hxW, rfl⟩, rfl⟩
      refine ⟨x.1, ⟨?_, x.2.2⟩, rfl⟩
      exact ⟨inclusion x, hxW, rfl⟩
    · rintro ⟨P, ⟨⟨w, hwW, rfl⟩, hwi⟩, rfl⟩
      let x : ↥((Y ∩ Z) ∩ standardChart i) := ⟨w.1, w.2, hwi⟩
      have hxW : x ∈ inclusion ⁻¹' W.1 := by
        change inclusion x ∈ W.1
        simpa only [inclusion, Set.inclusion_mk] using hwW
      exact ⟨e x, ⟨x, hxW, rfl⟩, rfl⟩
  · have hYne : (Y ∩ standardChart i).Nonempty := by
      exact ⟨w.1, w.2.1, hPi⟩
    exact projDim_eq_dim_chart hY i hYne
  · have hZne : (Z ∩ standardChart i).Nonempty := by
      exact ⟨w.1, w.2.2, hPi⟩
    exact projDim_eq_dim_chart hZ i hZne
  · have hYZclosed : IsClosed (Y ∩ Z) := hY.2.inter hZ.2
    have hWvariety := isProjVariety_projectiveComponentCarrier hYZclosed W
    exact projDim_eq_dim_chart hWvariety i
      ⟨w.1, ⟨w, hwW, rfl⟩, hPi⟩

end

end Hartshorne
