/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Hartshorne.Scheme.AbsoluteNormalizationDominant
import Hartshorne.Scheme.AbsoluteNormalizationNormal
import Hartshorne.Scheme.AbsoluteNormalizationUniversal
import Hartshorne.Scheme.AffineUFDClassGroup

/-!
# The normalization of an affine integral scheme

Let `D` be a domain and `j : D → O` an injective integral ring map to an integrally closed domain
`O` such that every element of `O` is a quotient of elements of `j(D)`. Then `Spec O ⟶ Spec D` is
the normalization of `Spec D` (`exists_isIso_absoluteNormalization_spec`): the lift of
`Spec O ⟶ Spec D` through the normalization (`Spec O` being normal) and the map out of the
normalization given by the universal property of the relative normalization (`Spec O ⟶ Spec D`
being integral) are mutually inverse.

We also compute residue degrees of `Spec O ⟶ Spec D`: at a prime `𝔮` of `O`, the degree
`[κ(𝔮) : κ(𝔮 ∩ D)]` is `1` when every element of `O` becomes, modulo `𝔮`, a quotient of elements
of `j(D)` with denominator outside `𝔮` (`residueDegree_SpecMap_eq_one`).
-/

namespace Hartshorne

open AlgebraicGeometry CategoryTheory

universe u

section Normalization

variable {D O : Type u} [CommRing D] [IsDomain D] [CommRing O] [IsDomain O]

omit [IsDomain D] in
/-- If every element of `O` is a quotient of elements of `j(D)`, the fraction field of `D` maps
isomorphically onto that of `O`; the resulting map `O → K(D)` restricts to the given map on
`D`. -/
theorem exists_ringHom_comp_eq_algebraMap (K : Type u) [Field K] [Algebra D K] [IsFractionRing D K]
    (j : D →+* O) (hj : Function.Injective j)
    (hbir : ∀ a : O, ∃ d₁ d₂ : D, d₂ ≠ 0 ∧ j d₂ * a = j d₁) :
    ∃ θ : O →+* K, θ.comp j = algebraMap D K := by
  let L := FractionRing O
  have hg : Function.Injective ((algebraMap O L).comp j) :=
    (IsFractionRing.injective O L).comp hj
  let ψ : K →+* L := IsFractionRing.lift hg
  have hψ : ∀ d : D, ψ (algebraMap D K d) = algebraMap O L (j d) := fun d =>
    IsFractionRing.lift_algebraMap hg d
  have hrange : ∀ a : O, algebraMap O L a ∈ Set.range ψ := by
    intro a
    obtain ⟨d₁, d₂, hd₂, h⟩ := hbir a
    have hd₂' : algebraMap O L (j d₂) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap O L), (IsFractionRing.injective O L).eq_iff, ← map_zero j,
        hj.eq_iff]
      exact hd₂
    refine ⟨algebraMap D K d₁ / algebraMap D K d₂, ?_⟩
    rw [map_div₀, hψ, hψ, div_eq_iff hd₂', ← h, map_mul, mul_comm]
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    obtain ⟨u, hu⟩ := hrange a
    obtain ⟨v, hv⟩ := hrange b
    exact ⟨u / v, by rw [map_div₀, hu, hv]⟩
  let e : K ≃+* L := RingEquiv.ofBijective ψ ⟨ψ.injective, hsurj⟩
  refine ⟨e.symm.toRingHom.comp (algebraMap O L), RingHom.ext fun d => ?_⟩
  change e.symm (algebraMap O L (j d)) = algebraMap D K d
  rw [RingEquiv.symm_apply_eq]
  exact (hψ d).symm

/-- `Spec O ⟶ Spec D` is dominant for an injective map `D → O` of domains. -/
theorem isDominant_SpecMap_of_injective (j : D →+* O) (hj : Function.Injective j) :
    IsDominant (Spec.map (CommRingCat.ofHom j)) := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  have hgen : Spec.map (CommRingCat.ofHom j) (genericPoint (Spec (.of O))) =
      genericPoint (Spec (.of D)) := by
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    change Ideal.comap j ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot j).mp hj
  have hx : x ∈ closure {genericPoint (Spec (.of D))} := by
    rw [(genericPoint_spec (Spec (.of D))).def]
    trivial
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range.mpr ⟨_, hgen⟩)) hx

variable [IsIntegrallyClosed O]

/-- **The normalization of `Spec D`.** Let `j : D → O` be an injective integral map of domains,
`O` integrally closed, with every element of `O` a quotient of elements of `j(D)`. Then
`Spec O ⟶ Spec D` is the normalization of `Spec D`: there is an isomorphism from `Spec O` to the
normalization of `Spec D` over `Spec D`. -/
theorem exists_isIso_absoluteNormalization_spec (j : D →+* O) (hj : Function.Injective j)
    (hint : j.IsIntegral) (hbir : ∀ a : O, ∃ d₁ d₂ : D, d₂ ≠ 0 ∧ j d₂ * a = j d₁) :
    ∃ e : Spec (.of O) ⟶ absoluteNormalization (Spec (.of D)), IsIso e ∧
      e ≫ absoluteNormalizationMap (Spec (.of D)) = Spec.map (CommRingCat.ofHom j) := by
  let V := Spec (.of D)
  let Z := Spec (.of O)
  let f₂ : Z ⟶ V := Spec.map (CommRingCat.ofHom j)
  have : IsNormal Z := isNormal_spec_of_isIntegrallyClosed (.of O)
  have : IsIntegralHom f₂ := IsIntegralHom.SpecMap_iff.mpr hint
  have : IsDominant f₂ := isDominant_SpecMap_of_injective j hj
  have := (absoluteNormalization_isNormal_and_isIntegral V).1
  have := (absoluteNormalization_isNormal_and_isIntegral V).2
  have := absoluteNormalizationMap_isDominant V
  obtain ⟨φ, hφ, -⟩ := absoluteNormalization_existsUnique_lift f₂
  have : IsDomain (CommRingCat.of D) := inferInstanceAs (IsDomain D)
  let _ : Algebra D V.functionField :=
    RingHom.toAlgebra (StructureSheaf.toStalk D (genericPoint V)).hom
  have : IsFractionRing D V.functionField :=
    @functionField_isFractionRing_of_affine (CommRingCat.of D) (inferInstanceAs (IsDomain D))
  obtain ⟨θ, hθ⟩ := exists_ringHom_comp_eq_algebraMap V.functionField j hj hbir
  let f₁ : Spec V.functionField ⟶ Z := Spec.map (CommRingCat.ofHom θ)
  have H : absoluteNormalizationGenericMap V = f₁ ≫ f₂ := by
    rw [absoluteNormalizationGenericMap, Spec.fromSpecStalk_eq']
    change _ = Spec.map (CommRingCat.ofHom θ) ≫ Spec.map (CommRingCat.ofHom j)
    rw [← Spec.map_comp]
    congr 1
    ext d
    exact (RingHom.congr_fun hθ d).symm
  let ψ : absoluteNormalization V ⟶ Z :=
    (absoluteNormalizationGenericMap V).normalizationDesc f₁ f₂ H
  have hψ : ψ ≫ f₂ = absoluteNormalizationMap V :=
    (absoluteNormalizationGenericMap V).normalizationDesc_comp f₁ f₂ H
  have h1 : ψ ≫ φ = 𝟙 _ := by
    obtain ⟨_, -, hu⟩ := absoluteNormalization_existsUnique_lift (absoluteNormalizationMap V)
    have ha : (ψ ≫ φ) ≫ absoluteNormalizationMap V = absoluteNormalizationMap V := by
      rw [Category.assoc, hφ, hψ]
    exact (hu _ ha).trans (hu _ (Category.id_comp _)).symm
  have h2 : φ ≫ ψ = 𝟙 _ := by
    obtain ⟨h, hh⟩ : ∃ h : CommRingCat.of O ⟶ CommRingCat.of O, Spec.map h = φ ≫ ψ :=
      ⟨Spec.preimage _, Spec.map_preimage _⟩
    have hcomp : Spec.map h ≫ f₂ = f₂ := by rw [hh, Category.assoc, hψ, hφ]
    rw [← Spec.map_comp] at hcomp
    have hjh := Spec.map_injective hcomp
    rw [← hh, Spec.map_eq_id]
    ext a
    obtain ⟨d₁, d₂, hd₂, had⟩ := hbir a
    have hjd : ∀ d, h.hom (j d) = j d := fun d => by
      simpa using congrArg (fun g : CommRingCat.of D ⟶ CommRingCat.of O => g.hom d) hjh
    have hne : j d₂ ≠ 0 := by
      rw [Ne, ← map_zero j, hj.eq_iff]
      exact hd₂
    refine mul_left_cancel₀ hne ?_
    have := congrArg h.hom had
    rw [map_mul, hjd, hjd] at this
    rw [this, ← had]
    rfl
  exact ⟨φ, ⟨⟨ψ, h2, h1⟩⟩, hφ⟩

end Normalization

section ResidueDegree


variable {D O : Type u} [CommRing D] [CommRing O]

/-- The residue field map of `Spec O ⟶ Spec D` at `𝔮` is surjective, so the residue degree is
`1`, when every element of `O` is, up to `𝔮`, a quotient of elements of `j(D)` whose denominator
lies outside `𝔮`. -/
theorem residueDegree_SpecMap_eq_one (j : D →+* O) (z : Spec (.of O))
    (happrox : ∀ a : O, ∃ d₁ d₂ : D, j d₂ ∉ z.asIdeal ∧ j d₂ * a - j d₁ ∈ z.asIdeal) :
    (Spec.map (CommRingCat.ofHom j)).residueDegree z = 1 := by
  let f := Spec.map (CommRingCat.ofHom j)
  have : z.asIdeal.IsPrime := z.isPrime
  let _ : Algebra (CommRingCat.of O) ((Spec (.of O)).presheaf.stalk z) :=
    FreeLocusAux.freeLocusStalkAlgebra z
  have : IsLocalization.AtPrime ((Spec (.of O)).presheaf.stalk z) z.asIdeal :=
    FreeLocusAux.freeLocus_stalk_isLocalization z
  -- residues of global functions
  let resO : O →+* (Spec (.of O)).residueField z :=
    ((Spec (.of O)).residue z).hom.comp
      (((Spec (.of O)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (.of O)).inv.hom)
  let resD : D →+* (Spec (.of D)).residueField (f z) :=
    ((Spec (.of D)).residue (f z)).hom.comp
      (((Spec (.of D)).presheaf.germ ⊤ (f z) trivial).hom.comp (Scheme.ΓSpecIso (.of D)).inv.hom)
  have hcompat : ∀ d : D, (f.residueFieldMap z).hom (resD d) = resO (j d) := by
    intro d
    have h1 := congrArg (fun g => g.hom (((Spec (.of D)).presheaf.germ ⊤ (f z) trivial).hom
      ((Scheme.ΓSpecIso (.of D)).inv.hom d))) (Scheme.residue_residueFieldMap f z)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
    refine h1.trans ?_
    have h3 := Scheme.Hom.germ_stalkMap_apply f ⊤ z (by trivial)
      ((Scheme.ΓSpecIso (.of D)).inv.hom d)
    refine (congrArg _ h3).trans ?_
    have h2 := congrArg (fun g => g.hom d) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    change _ = (Spec (.of O)).residue z ((Spec (.of O)).presheaf.germ ⊤ z trivial
      ((Scheme.ΓSpecIso (.of O)).inv.hom ((CommRingCat.ofHom j).hom d)))
    rw [h2]
    rfl
  have hres0 : ∀ a : O, resO a = 0 ↔ a ∈ z.asIdeal := by
    intro a
    change IsLocalRing.residue _ _ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      ((Spec (.of O)).presheaf.stalk z) z.asIdeal a)
  have hrangeO : ∀ a : O, resO a ∈ Set.range (f.residueFieldMap z).hom := by
    intro a
    obtain ⟨d₁, d₂, hd₂, h⟩ := happrox a
    have hne : resO (j d₂) ≠ 0 := fun h0 => hd₂ ((hres0 _).mp h0)
    refine ⟨resD d₁ / resD d₂, ?_⟩
    rw [map_div₀, hcompat, hcompat, div_eq_iff hne]
    have h' := (hres0 _).mpr h
    rw [map_sub, sub_eq_zero, map_mul] at h'
    rw [← h', mul_comm]
  have hsurj : Function.Surjective (f.residueFieldMap z).hom := by
    intro w
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective w
    obtain ⟨⟨a, c⟩, rfl⟩ := IsLocalization.mk'_surjective z.asIdeal.primeCompl s
    have hc : resO c ≠ 0 := fun h0 => c.2 ((hres0 _).mp h0)
    obtain ⟨u, hu⟩ := hrangeO a
    obtain ⟨v, hv⟩ := hrangeO c
    refine ⟨u / v, ?_⟩
    rw [map_div₀, hu, hv]
    symm
    refine (eq_div_iff hc).mpr ?_
    change IsLocalRing.residue _ (IsLocalization.mk' _ a c) * IsLocalRing.residue _
      (algebraMap (CommRingCat.of O) _ (c : O)) = IsLocalRing.residue _ (algebraMap _ _ a)
    exact (map_mul (IsLocalRing.residue _) _ _).symm.trans
      (congrArg _ (IsLocalization.mk'_spec _ a c))
  let _ := (f.residueFieldMap z).hom.toAlgebra
  rw [Scheme.Hom.residueDegree,
    Module.finrank_of_bijective_algebraMap ⟨(f.residueFieldMap z).hom.injective, hsurj⟩]

end ResidueDegree

end Hartshorne
