/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.GradedMultiplicity
import Hartshorne.Intersection.ProjectiveIntersectionChart
import Hartshorne.Projective.Correspondence

/-!
# Intersection multiplicity with a projective hypersurface

Hartshorne, *Algebraic Geometry*, definition before Theorem I.7.7 (p. 53).
-/

namespace Hartshorne

open MvPolynomial Set TopologicalSpace

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {σ : Type} [Finite σ]

/-- The homogeneous ideal defining the scheme-theoretic intersection used in
Hartshorne's intersection multiplicity. -/
noncomputable def projectiveIntersectionIdeal
    (Y H : Set (ProjectiveSpace k σ)) : Ideal (MvPolynomial σ k) :=
  homogeneousVanishingIdeal Y ⊔ homogeneousVanishingIdeal H

/-- The homogeneous prime attached to an irreducible component of a
projective intersection. -/
noncomputable def projectiveIntersectionComponentPrime
    {Y H : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) (hH : IsProjAlgebraicSet H)
    (Z : irreducibleComponents ↥(Y ∩ H)) :
    PrimeSpectrum (MvPolynomial σ k) :=
  ⟨homogeneousVanishingIdeal (projectiveComponentCarrier Z.1),
    (isIrreducible_iff_isPrime_homogeneousVanishingIdeal
      (isProjVariety_projectiveComponentCarrier
        (hY.2.inter (isClosed_iff_isProjAlgebraicSet.2 hH)) Z).isProjAlgebraicSet).1
      (isProjVariety_projectiveComponentCarrier
        (hY.2.inter (isClosed_iff_isProjAlgebraicSet.2 hH)) Z).1⟩

/-- The component prime is minimal over the ideal defining the intersection. -/
theorem projectiveIntersectionComponentPrime_isMinimalPrime
    {Y H : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) (hH : IsProjAlgebraicSet H)
    (Z : irreducibleComponents ↥(Y ∩ H)) :
    (projectiveIntersectionIdeal Y H).IsMinimalPrime
      (projectiveIntersectionComponentPrime hY hH Z).1 := by
  let S := MvPolynomial σ k
  let 𝓢 : ℤ → Submodule k S := integerHomogeneousSubmodule k σ
  let C : Set (ProjectiveSpace k σ) := projectiveComponentCarrier Z.1
  let I : Ideal S := projectiveIntersectionIdeal Y H
  let P : PrimeSpectrum S := projectiveIntersectionComponentPrime hY hH Z
  have hC : IsProjVariety C :=
    isProjVariety_projectiveComponentCarrier
      (hY.2.inter (isClosed_iff_isProjAlgebraicSet.2 hH)) Z
  have hCY : C ⊆ Y := by
    rintro x ⟨z, hz, rfl⟩
    exact z.2.1
  have hCH : C ⊆ H := by
    rintro x ⟨z, hz, rfl⟩
    exact z.2.2
  have hIP : I ≤ P.1 := by
    apply sup_le
    · exact homogeneousVanishingIdeal_anti_mono hCY
    · exact homogeneousVanishingIdeal_anti_mono hCH
  have hIhomNat : IsHomogeneousIdeal I :=
    (isHomogeneousIdeal_homogeneousVanishingIdeal Y).sup
      (isHomogeneousIdeal_homogeneousVanishingIdeal H)
  have hIhom : I.IsHomogeneous 𝓢 :=
    (ideal_isHomogeneous_integer_iff k σ I).2 hIhomNat
  refine ⟨⟨P.2, hIP⟩, ?_⟩
  intro Q hQ hQP
  let Qh : Ideal S := (Q.homogeneousCore 𝓢).toIdeal
  have hQhprime : Qh.IsPrime := hQ.1.homogeneousCore
  have hQhhom : Qh.IsHomogeneous 𝓢 :=
    HomogeneousIdeal.isHomogeneous (Q.homogeneousCore 𝓢)
  have hIQh : I ≤ Qh :=
    hIhom.toIdeal_homogeneousCore_eq_self.symm.trans_le
      (Ideal.homogeneousCore_mono 𝓢 hQ.2)
  have hQhQ : Qh ≤ Q := Ideal.toIdeal_homogeneousCore_le 𝓢 Q
  have hQhP : Qh ≤ P.1 := hQhQ.trans hQP
  let V : Set (ProjectiveSpace k σ) := projZeroSet (Qh : Set S)
  have hCzero : projZeroSet (P.1 : Set S) = C :=
    hC.isProjAlgebraicSet.projZeroSet_homogeneousVanishingIdeal_eq
  have hCV : C ⊆ V := by
    rw [← hCzero]
    exact projZeroSet_anti_mono hQhP
  have hVY : V ⊆ Y := by
    have h := projZeroSet_anti_mono
      (show (homogeneousVanishingIdeal Y : Set S) ⊆ Qh from
        (le_sup_left : homogeneousVanishingIdeal Y ≤ I).trans hIQh)
    rwa [hY.isProjAlgebraicSet.projZeroSet_homogeneousVanishingIdeal_eq] at h
  have hVH : V ⊆ H := by
    have h := projZeroSet_anti_mono
      (show (homogeneousVanishingIdeal H : Set S) ⊆ Qh from
        (le_sup_right : homogeneousVanishingIdeal H ≤ I).trans hIQh)
    rwa [hH.projZeroSet_homogeneousVanishingIdeal_eq] at h
  have hVS : V ⊆ Y ∩ H := fun x hx ↦ ⟨hVY hx, hVH hx⟩
  have hVne : V.Nonempty := by
    obtain ⟨z, hz⟩ := Z.2.1.nonempty
    exact ⟨z.1, hCV ⟨z, hz, rfl⟩⟩
  have hQhhomNat : IsHomogeneousIdeal Qh :=
    (ideal_isHomogeneous_integer_iff k σ Qh).1 hQhhom
  obtain ⟨T, hTspan⟩ :=
    (Ideal.IsHomogeneous.iff_exists
      (𝒜 := MvPolynomial.homogeneousSubmodule σ k) (I := Qh)).1 hQhhomNat
  let U : Set S := ((↑) :
    SetLike.homogeneousSubmonoid (MvPolynomial.homogeneousSubmodule σ k) → S) '' T
  have hUhom : IsHomogeneousSet U := by
    rintro f ⟨g, hg, rfl⟩
    exact isHomogeneousElem_iff.mp g.property
  have hVU : V = projZeroSet U := by
    change projZeroSet (Qh : Set S) = projZeroSet U
    rw [hTspan, projZeroSet_span]
  have hValg : IsProjAlgebraicSet V := ⟨U, hUhom, hVU⟩
  have hJV : homogeneousVanishingIdeal V = Qh := by
    change homogeneousVanishingIdeal (projZeroSet (Qh : Set S)) = Qh
    rw [homogeneousVanishingIdeal_projZeroSet hQhhomNat hVne,
      hQhprime.radical]
  have hVirr : IsIrreducible V :=
    (isIrreducible_iff_isPrime_homogeneousVanishingIdeal hValg).2
      (hJV.symm ▸ hQhprime)
  let f : V → ↥(Y ∩ H) := fun x ↦ ⟨x.1, hVS x.2⟩
  let W' : Set ↥(Y ∩ H) := Set.range f
  have hfcont : Continuous f :=
    continuous_subtype_val.subtype_mk fun x ↦ hVS x.2
  have hW'irr : IsIrreducible W' := by
    let _ : IrreducibleSpace V := Subtype.irreducibleSpace hVirr
    simpa [W', Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ V).image f hfcont.continuousOn
  have hZW' : Z.1 ⊆ W' := by
    intro z hz
    let x : V := ⟨z.1, hCV ⟨z, hz, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rfl
  have hW'Z : W' ⊆ Z.1 := Z.2.2 hW'irr hZW'
  have hZW'eq : Z.1 = W' := Set.Subset.antisymm hZW' hW'Z
  have hcarrierW' : Subtype.val '' W' = V := by
    ext x
    constructor
    · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
      exact v.2
    · intro hx
      let v : V := ⟨x, hx⟩
      exact ⟨f v, ⟨v, rfl⟩, rfl⟩
  have hCVeq : C = V := by
    change Subtype.val '' Z.1 = V
    rw [hZW'eq, hcarrierW']
  have hPQh : P.1 = Qh := by
    change homogeneousVanishingIdeal C = Qh
    rw [hCVeq, hJV]
  rw [hPQh]
  exact hQhQ

/-- Equivalently, the component prime is minimal over the annihilator of the
homogeneous coordinate module of the intersection. -/
theorem projectiveIntersectionComponentPrime_isMinimalPrime_annihilator
    {Y H : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) (hH : IsProjAlgebraicSet H)
    (Z : irreducibleComponents ↥(Y ∩ H)) :
    (Module.annihilator (MvPolynomial σ k)
      (MvPolynomial σ k ⧸ projectiveIntersectionIdeal Y H)).IsMinimalPrime
        (projectiveIntersectionComponentPrime hY hH Z).1 := by
  rw [Ideal.annihilator_quotient]
  exact projectiveIntersectionComponentPrime_isMinimalPrime hY hH Z

/-- The underlying localized module length attached to a projective
intersection component is finite. -/
theorem projectiveIntersectionMultiplicity_length_ne_top
    {Y H : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) (hH : IsProjAlgebraicSet H)
    (Z : irreducibleComponents ↥(Y ∩ H)) :
    gradedMultiplicity (MvPolynomial σ k)
        (MvPolynomial σ k ⧸ projectiveIntersectionIdeal Y H)
        (projectiveIntersectionComponentPrime hY hH Z) ≠ ⊤ := by
  let S := MvPolynomial σ k
  let I : Ideal S := projectiveIntersectionIdeal Y H
  let 𝓢 : ℤ → Submodule k S := integerHomogeneousSubmodule k σ
  have hIhomNat : IsHomogeneousIdeal I :=
    (isHomogeneousIdeal_homogeneousVanishingIdeal Y).sup
      (isHomogeneousIdeal_homogeneousVanishingIdeal H)
  have hIhom : I.IsHomogeneous 𝓢 :=
    (ideal_isHomogeneous_integer_iff k σ I).2 hIhomNat
  let Psub : HomogeneousSubmodule 𝓢 𝓢 :=
    homogeneousIdealSubmodule 𝓢 I hIhom
  let ℳ := gradedQuotientPiece 𝓢 𝓢 Psub
  obtain ⟨s, hshead, hslast⟩ := exists_gradedPrimeFiltration 𝓢 ℳ
  exact gradedPrimeFiltration_multiplicity_ne_top 𝓢 ℳ
    s hshead hslast (projectiveIntersectionComponentPrime hY hH Z)
      (projectiveIntersectionComponentPrime_isMinimalPrime_annihilator hY hH Z)

/-- Hartshorne's natural-valued intersection multiplicity.  The construction
works for a projective variety and a projective algebraic set, including a
reducible hypersurface; the source applies it when the hypersurface does not
contain the variety. -/
noncomputable def projectiveIntersectionMultiplicity
    {Y H : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) (hH : IsProjAlgebraicSet H)
    (Z : irreducibleComponents ↥(Y ∩ H)) : ℕ :=
  ENat.toNat <| gradedMultiplicity (MvPolynomial σ k)
    (MvPolynomial σ k ⧸ projectiveIntersectionIdeal Y H)
    (projectiveIntersectionComponentPrime hY hH Z)

/-- Casting the natural-valued intersection multiplicity back to `ℕ∞`
recovers its defining localized module length. -/
@[simp]
theorem natCast_projectiveIntersectionMultiplicity
    {Y H : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) (hH : IsProjAlgebraicSet H)
    (Z : irreducibleComponents ↥(Y ∩ H)) :
    (projectiveIntersectionMultiplicity hY hH Z : ℕ∞) =
      gradedMultiplicity (MvPolynomial σ k)
        (MvPolynomial σ k ⧸ projectiveIntersectionIdeal Y H)
        (projectiveIntersectionComponentPrime hY hH Z) := by
  apply ENat.natCast_toNat
  exact projectiveIntersectionMultiplicity_length_ne_top hY hH Z

end

end Hartshorne
