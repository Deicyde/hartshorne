/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.AffineDiagonalSection
import Hartshorne.Intersection.AffineProductDimension
import Hartshorne.Intersection.FiniteCutDimension

/-!
# The affine dimension theorem

Hartshorne, *Algebraic Geometry*, I.7, Proposition 7.1 (p. 48).

The subtraction-free form says that for every irreducible component `W` of
`Y ∩ Z ⊆ ᴸⁿ`,

`dim Y + dim Z ≤ dim W + n`.

## Main result

* `Hartshorne.affine_dimension_theorem`
-/

namespace Hartshorne

open MvPolynomial Set TopologicalSpace Topology

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {σ : Type} [Finite σ]

/-- The ambient carrier of a subset of an affine subspace. -/
def affineComponentCarrier {S : Set (σ → k)} (W : Set S) : Set (σ → k) :=
  Subtype.val '' W

omit [IsAlgClosed k] [Finite σ] in
/-- A relative irreducible component of a closed affine set is an affine
variety in the ambient affine space. -/
theorem isAffineVariety_affineComponentCarrier
    {S : Set (σ → k)} (hS : IsClosed S)
    (W : irreducibleComponents S) :
    IsAffineVariety (affineComponentCarrier W.1) := by
  refine ⟨?_, ?_⟩
  · exact W.2.1.image Subtype.val continuous_subtype_val.continuousOn
  · exact hS.isClosedMap_subtype_val W.1
      (isClosed_of_mem_irreducibleComponents W.1 W.2)

omit [IsAlgClosed k] [Finite σ] in
/-- The ambient carrier of a relative component is maximal among affine
varieties contained in the closed set. -/
theorem affineComponentCarrier_maximal
    {S : Set (σ → k)} (hS : IsClosed S)
    (W : irreducibleComponents S) :
    Maximal (fun V : Set (σ → k) ↦
      IsAffineVariety V ∧ V ⊆ S) (affineComponentCarrier W.1) := by
  refine ⟨⟨isAffineVariety_affineComponentCarrier hS W, ?_⟩, ?_⟩
  · rintro x ⟨w, _, rfl⟩
    exact w.2
  · intro V hV hWV
    let Vsub : Set S := Subtype.val ⁻¹' V
    have hVrange : V ⊆ Set.range (Subtype.val : S → (σ → k)) := by
      intro x hx
      exact ⟨⟨x, hV.2 hx⟩, rfl⟩
    let eV := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hVrange
    let _ : IrreducibleSpace V := Subtype.irreducibleSpace hV.1.1
    let _ : IrreducibleSpace Vsub := eV.irreducibleSpace_iff.mpr inferInstance
    have hVsub : IsIrreducible Vsub := IsIrreducible.of_subtype
    have hWVsub : W.1 ⊆ Vsub := by
      intro w hw
      exact hWV ⟨w, hw, rfl⟩
    have hVsubW : Vsub ⊆ W.1 := W.2.2 hVsub hWVsub
    intro x hx
    let s : S := ⟨x, hV.2 hx⟩
    have hsV : s ∈ Vsub := hx
    exact ⟨s, hVsubW hsV, rfl⟩

omit [IsAlgClosed k] [Finite σ] in
/-- Passing between a component inside a subspace and its ambient carrier
does not change dimension. -/
theorem dim_affineComponentCarrier
    {S : Set (σ → k)} (W : Set S) :
    dim (affineComponentCarrier W) = topologicalKrullDim W := by
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (Topology.IsEmbedding.subtypeVal.homeomorphImage W).isHomeomorph).symm

/-- **Proposition I.7.1.** Every irreducible component of the intersection of
two affine varieties has the expected lower dimension bound, written without
subtraction in `WithBot ℕ∞`. -/
theorem affine_dimension_theorem
    {Y Z : Set (σ → k)} (hY : IsAffineVariety Y) (hZ : IsAffineVariety Z)
    (W : irreducibleComponents ↥(Y ∩ Z)) :
    dim Y + dim Z ≤ dim (affineComponentCarrier W.1) + Nat.card σ := by
  let e := affineDiagonalSectionHomeomorph Y Z
  let D := affineDiagonalSectionIrreducibleComponentsEquiv Y Z W
  have hProduct : IsAffineVariety (affineProduct Y Z) :=
    isAffineVariety_affineProduct hY hZ
  have hSectionClosed : IsClosed (affineDiagonalSection Y Z) := by
    exact hProduct.2.inter (isClosed_zeroSet affineDiagonalPolynomials)
  have hDmax : Maximal
      (fun V : Set (Sum σ σ → k) ↦
        IsAffineVariety V ∧
          V ⊆ affineProduct Y Z ∩ zeroSet affineDiagonalPolynomials)
      (affineComponentCarrier D.1) := by
    simpa only [affineDiagonalSection, affineDiagonalZeroSet] using
      affineComponentCarrier_maximal hSectionClosed D
  have hcut := dim_component_inter_zeroLocus_add_ncard hProduct
    affineDiagonalPolynomials affineDiagonalPolynomials_finite hDmax
  have hWDtop : topologicalKrullDim W.1 = topologicalKrullDim D.1 := by
    change topologicalKrullDim W.1 =
      topologicalKrullDim (e '' W.1)
    exact IsHomeomorph.topologicalKrullDim_eq _
      (e.isEmbedding.homeomorphImage W.1).isHomeomorph
  have hWDdim : dim (affineComponentCarrier D.1) =
      dim (affineComponentCarrier W.1) := by
    rw [dim_affineComponentCarrier, dim_affineComponentCarrier]
    exact hWDtop.symm
  have hcard : (affineDiagonalPolynomials :
      Set (MvPolynomial (Sum σ σ) k)).ncard ≤ Nat.card σ := by
    simpa only [← Nat.card_coe_set_eq] using
      (natCard_affineDiagonalPolynomials_le (k := k) (σ := σ))
  have hcard' : ((affineDiagonalPolynomials :
      Set (MvPolynomial (Sum σ σ) k)).ncard : WithBot ℕ∞) ≤
      (Nat.card σ : WithBot ℕ∞) := by
    exact_mod_cast hcard
  calc
    dim Y + dim Z = dim (affineProduct Y Z) :=
      (dim_affineProduct hY hZ).symm
    _ ≤ dim (affineComponentCarrier D.1) +
        (affineDiagonalPolynomials :
          Set (MvPolynomial (Sum σ σ) k)).ncard := hcut
    _ = dim (affineComponentCarrier W.1) +
        (affineDiagonalPolynomials :
          Set (MvPolynomial (Sum σ σ) k)).ncard := by
      rw [hWDdim]
    _ ≤ dim (affineComponentCarrier W.1) + Nat.card σ := by
      exact add_le_add_right hcard' _

end

end Hartshorne
