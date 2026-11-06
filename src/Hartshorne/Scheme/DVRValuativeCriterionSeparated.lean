/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.DominatingDVR
import Hartshorne.Scheme.FiniteType
import Hartshorne.Scheme.QuasiCompactImageClosed
import Hartshorne.Scheme.ValuationSpectrumMaps
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# The DVR-valuative criterion for separatedness

Hartshorne, *Algebraic Geometry*, II.4, Exercise 4.11(b), separatedness clause (pp. 107–108):
a finite-type morphism `f : X ⟶ Y` of Noetherian schemes is separated if and only if every
valuative commutative square over `f` (`AlgebraicGeometry.ValuativeCommSq`) whose valuation
ring is a discrete valuation ring has at most one lift.

The forward implication is the uniqueness part of the valuative criterion
(`AlgebraicGeometry.IsSeparated.valuativeCriterion`). For the converse, the diagonal is an
immersion and quasi-compact (the source is Noetherian), so by Hartshorne II, Lemma 4.5 it
suffices that its range is stable under specialization. Given `Δ(x) ⤳ q` with `q ≠ Δ(x)`,
the image `A` of the local ring `𝒪_q` of `X ×_Y X` in `κ(Δ(x))` is a Noetherian local domain
(the fibre product is locally Noetherian because `f` is locally of finite type), with fraction
field `κ(Δ(x))` and nonzero maximal ideal. A DVR `R` of `κ(Δ(x))` dominating `A`
(`Hartshorne.exists_dominating_dvr_of_fg`) gives a morphism `Spec R ⟶ X ×_Y X` sending the
closed point to `q`; its two projections lift the same valuative square, hence agree, and the
morphism factors through the diagonal.
-/

open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace

namespace Hartshorne

universe u

variable {P : Scheme.{u}}

/-- For a specialization `x₁ ⤳ x₀`, the canonical map `𝒪_{P, x₀} ⟶ κ(x₁)`. -/
noncomputable abbrev stalkToResidueFieldOfSpecializes {x₁ x₀ : P} (h : x₁ ⤳ x₀) :
    P.presheaf.stalk x₀ ⟶ P.residueField x₁ :=
  P.presheaf.stalkSpecializes h ≫ P.residue x₁

/-- The image of `𝒪_{P, x₀}` in `κ(x₁)` is a local ring. -/
instance isLocalRing_range_stalkToResidueFieldOfSpecializes {x₁ x₀ : P} (h : x₁ ⤳ x₀) :
    IsLocalRing (stalkToResidueFieldOfSpecializes h).hom.range :=
  IsLocalRing.of_surjective' _ (stalkToResidueFieldOfSpecializes h).hom.rangeRestrict_surjective

/-- The map `𝒪_{P, x₀} ⟶ κ(x₁)` sends the germ at `x₀` of a section to the value at `x₁`. -/
lemma stalkToResidueFieldOfSpecializes_germ {x₁ x₀ : P} (h : x₁ ⤳ x₀) {V : P.Opens}
    (hx₀ : x₀ ∈ V) (c : Γ(P, V)) :
    stalkToResidueFieldOfSpecializes h (P.presheaf.germ V x₀ hx₀ c) =
      P.residue x₁ (P.presheaf.germ V x₁ (h.mem_open V.isOpen hx₀) c) := by
  change (P.presheaf.germ V x₀ hx₀ ≫ P.presheaf.stalkSpecializes h ≫ P.residue x₁) c = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  rfl

/-- The residue field `κ(x₁)` is the fraction field of the image of `𝒪_{P, x₀}`. -/
lemma isFractionRing_range_stalkToResidueFieldOfSpecializes {x₁ x₀ : P} (h : x₁ ⤳ x₀) :
    IsFractionRing (stalkToResidueFieldOfSpecializes h).hom.range (P.residueField x₁) := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨V, hV, hx₀, -⟩ := (Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens)
    (show x₀ ∈ (⊤ : P.Opens) from trivial)
  have hx₁ : x₁ ∈ V := h.mem_open V.isOpen hx₀
  obtain ⟨s, rfl⟩ := P.residue_surjective x₁ z
  let := P.presheaf.algebra_section_stalk ⟨x₁, hx₁⟩
  have := hV.isLocalization_stalk ⟨x₁, hx₁⟩
  obtain ⟨⟨a, b, hb⟩, hab⟩ :=
    IsLocalization.surj (hV.primeIdealOf ⟨x₁, hx₁⟩).asIdeal.primeCompl s
  have hbu : IsUnit (algebraMap Γ(P, V) (P.presheaf.stalk x₁) b) :=
    IsLocalization.map_units _ (⟨b, hb⟩ : (hV.primeIdealOf ⟨x₁, hx₁⟩).asIdeal.primeCompl)
  have hb0 : P.residue x₁ (algebraMap Γ(P, V) (P.presheaf.stalk x₁) b) ≠ 0 :=
    (hbu.map (P.residue x₁).hom).ne_zero
  refine ⟨⟨_, P.presheaf.germ V x₀ hx₀ a, rfl⟩, ⟨_, P.presheaf.germ V x₀ hx₀ b, rfl⟩, ?_⟩
  change _ = stalkToResidueFieldOfSpecializes h _ / stalkToResidueFieldOfSpecializes h _
  change P.residue x₁ (P.presheaf.germ V x₁ hx₁ b) ≠ 0 at hb0
  change s * P.presheaf.germ V x₁ hx₁ b = P.presheaf.germ V x₁ hx₁ a at hab
  rw [stalkToResidueFieldOfSpecializes_germ, stalkToResidueFieldOfSpecializes_germ,
    eq_div_iff hb0, ← map_mul, hab]

/-- For a strict specialization `x₁ ⤳ x₀`, the image of `𝒪_{P, x₀}` in `κ(x₁)` is not a
field: a section on an affine neighbourhood of `x₀` vanishing at `x₀` but not at `x₁` gives a
nonzero element of its maximal ideal. -/
lemma maximalIdeal_range_stalkToResidueFieldOfSpecializes_ne_bot {x₁ x₀ : P} (h : x₁ ⤳ x₀)
    (hne : x₁ ≠ x₀) :
    maximalIdeal (stalkToResidueFieldOfSpecializes h).hom.range ≠ ⊥ := by
  obtain ⟨V, hV, hx₀, -⟩ := (Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens)
    (show x₀ ∈ (⊤ : P.Opens) from trivial)
  have hx₁ : x₁ ∈ V := h.mem_open V.isOpen hx₀
  have hns : ¬ x₀ ⤳ x₁ := fun h' => hne (h.antisymm h').eq
  obtain ⟨W, hW, hx₁W, hx₀W⟩ : ∃ W : Set P, IsOpen W ∧ x₁ ∈ W ∧ x₀ ∉ W := by
    simpa [specializes_iff_forall_open] using hns
  obtain ⟨b, hbW, hx₁b⟩ := hV.exists_basicOpen_le (V := ⟨W, hW⟩) ⟨x₁, hx₁W⟩ hx₁
  have hx₀b : x₀ ∉ P.basicOpen b := fun hb => hx₀W (hbW hb)
  rw [Scheme.mem_basicOpen _ _ _ hx₁] at hx₁b
  rw [Scheme.mem_basicOpen _ _ _ hx₀] at hx₀b
  let g := stalkToResidueFieldOfSpecializes h
  have : IsLocalHom g.hom.rangeRestrict :=
    IsLocalHom.of_surjective _ g.hom.rangeRestrict_surjective
  intro hbot
  have hmem : g.hom.rangeRestrict (P.presheaf.germ V x₀ hx₀ b) ∈ maximalIdeal g.hom.range :=
    (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu => hx₀b (isUnit_of_map_unit _ _ hu))
  rw [hbot, Ideal.mem_bot] at hmem
  apply (hx₁b.map (P.residue x₁).hom).ne_zero
  rw [← stalkToResidueFieldOfSpecializes_germ h hx₀]
  exact congrArg Subtype.val hmem

/-- If every valuative square over `f` with a discrete valuation ring has at most one lift and
the source is locally Noetherian, then the range of the diagonal of a locally finite type `f`
is stable under specialization. For a strict specialization `Δ(x) ⤳ q`, a DVR of `κ(Δ(x))`
dominating the image of `𝒪_{q}` gives a morphism `Spec R ⟶ X ×_Y X` whose two projections
are lifts of the same valuative square; they agree, so `q` lies on the diagonal. -/
theorem mem_range_diagonal_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X]
    (H : ∀ S : ValuativeCommSq f, IsDiscreteValuationRing S.R →
      Subsingleton S.commSq.LiftStruct)
    (x : X) {q : ↥(pullback f f)} (h : pullback.diagonal f x ⤳ q) :
    q ∈ Set.range (pullback.diagonal f) := by
  by_cases hne : pullback.diagonal f x = q
  · exact ⟨x, hne⟩
  let P := pullback.diagonalObj f
  let g := stalkToResidueFieldOfSpecializes h
  let A := g.hom.range
  let L := P.residueField (pullback.diagonal f x)
  have : IsNoetherianRing A := isNoetherianRing_range g.hom
  have : IsFractionRing A L := isFractionRing_range_stalkToResidueFieldOfSpecializes h
  obtain ⟨R, hR, hRL, -, hmem, hloc⟩ := exists_dominating_dvr_of_fg A L (L := L)
    (maximalIdeal_range_stalkToResidueFieldOfSpecializes_ne_bot h hne)
    (IntermediateField.fg_top L L)
  have : IsLocalHom g.hom.rangeRestrict :=
    IsLocalHom.of_surjective _ g.hom.rangeRestrict_surjective
  let φ : P.presheaf.stalk q ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (((algebraMap A L).codRestrict R hmem).comp g.hom.rangeRestrict)
  have : IsLocalHom φ.hom := RingHom.isLocalHom_comp _ _
  have hφ : φ ≫ CommRingCat.ofHom (algebraMap R L) = g := rfl
  let ψ : Spec (CommRingCat.of R) ⟶ P := Spec.map φ ≫ P.fromSpecStalk q
  have hψ : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ ψ =
      P.fromSpecResidueField (pullback.diagonal f x) := by
    rw [← Spec.map_comp_assoc, hφ, Scheme.fromSpecResidueField,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h, Spec.map_comp_assoc]
  have hdiag : P.fromSpecResidueField (pullback.diagonal f x) ≫ pullback.fst f f =
      P.fromSpecResidueField (pullback.diagonal f x) ≫ pullback.snd f f := by
    rw [← cancel_epi (Spec.map ((pullback.diagonal f).residueFieldMap x)),
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
    simp
  let S : ValuativeCommSq f :=
    { R := R, K := L
      i₁ := P.fromSpecResidueField (pullback.diagonal f x) ≫ pullback.fst f f
      i₂ := ψ ≫ pullback.fst f f ≫ f
      commSq := ⟨by rw [reassoc_of% hψ, Category.assoc]⟩ }
  let l₁ : S.commSq.LiftStruct :=
    ⟨ψ ≫ pullback.fst f f, by simp [S, reassoc_of% hψ], rfl⟩
  let l₂ : S.commSq.LiftStruct :=
    ⟨ψ ≫ pullback.snd f f, by simp [S, reassoc_of% hψ, hdiag],
      by simp [S, pullback.condition]⟩
  have h₁₂ : ψ ≫ pullback.fst f f = ψ ≫ pullback.snd f f :=
    congrArg CommSq.LiftStruct.l ((H S hR).elim l₁ l₂)
  have hψΔ : ψ = (ψ ≫ pullback.fst f f) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp
    · simp [h₁₂]
  have hq : ψ (closedPoint R) = q := by
    change P.fromSpecStalk q (Spec.map φ (closedPoint R)) = q
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  refine ⟨(ψ ≫ pullback.fst f f) (closedPoint R), ?_⟩
  calc _ = ((ψ ≫ pullback.fst f f) ≫ pullback.diagonal f) (closedPoint R) := rfl
    _ = ψ (closedPoint R) := by rw [← hψΔ]
    _ = q := hq

/-- **Hartshorne II, Exercise 4.11(b)** (separatedness clause). A finite-type morphism
`f : X ⟶ Y` of Noetherian schemes is separated if and only if every valuative commutative
square over `f` whose valuation ring is a discrete valuation ring has at most one lift.

The Noetherian hypothesis on `Y` is the source's; the proof does not use it. -/
theorem isSeparated_iff_dvr_valuativeCriterion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] (hf : FiniteType f) :
    IsSeparated f ↔ ∀ S : ValuativeCommSq f, IsDiscreteValuationRing S.R →
      Subsingleton S.commSq.LiftStruct := by
  refine ⟨fun _ S _ => IsSeparated.valuativeCriterion f S, fun H => ?_⟩
  have : LocallyOfFiniteType f := hf.1
  refine ⟨.of_isPreimmersion _ ?_⟩
  rw [isClosed_range_iff_stableUnderSpecialization]
  rintro _ q h ⟨x, rfl⟩
  exact mem_range_diagonal_of_specializes f H x h

end Hartshorne
