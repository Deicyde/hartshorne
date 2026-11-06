/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.DVRValuativeCriterionSeparated

/-!
# The DVR-valuative criterion for properness

Hartshorne, *Algebraic Geometry*, II.4, Exercise 4.11(b), properness clause (pp. 107–108):
a finite-type morphism `f : X ⟶ Y` of Noetherian schemes is proper if and only if every
valuative commutative square over `f` (`AlgebraicGeometry.ValuativeCommSq`) whose valuation
ring is a discrete valuation ring has a unique lift.

The forward implication is Mathlib's valuative criterion `IsProper.eq_valuativeCriterion`.
Conversely, separatedness is the companion criterion
`Hartshorne.isSeparated_iff_dvr_valuativeCriterion`, and universal closedness follows from
`UniversallyClosed.of_valuativeCriterion` once every valuative square, with an arbitrary
valuation ring `R` of a field `K`, has a lift (`Hartshorne.valuativeCriterion_existence_of_dvr`).
This reduction to discrete valuation rings avoids base change, so everything stays Noetherian:

* let `x` be the image of `Spec K`, `V` an affine open of `Y` containing the image of the closed
  point of `Spec R`, and `U₁, …, Uₙ` finitely many affine opens covering `f ⁻¹ V`;
* if for some `Uⱼ ∋ x` the evaluation `Γ(Uⱼ) ⟶ κ(x) ⟶ K` lands in `R`, it gives a lift
  `Spec R ⟶ Spec Γ(Uⱼ) ⟶ X` (`Hartshorne.hasLift_of_evaluation_mem`);
* otherwise pick `bⱼ ∈ Γ(Uⱼ)` with value `βⱼ ∉ R`, so `βⱼ⁻¹` lies in the maximal ideal of `R`;
  the subring `D = Γ(V)[βⱼ⁻¹] ⊆ κ(x)` is Noetherian, and its localization `A` at the contraction
  of `𝔪_R` is a Noetherian local domain with nonzero maximal ideal containing the `βⱼ⁻¹`, over
  whose fraction field `κ(x)` is finitely generated (`f` is locally of finite type);
* a DVR `R'` of `κ(x)` dominating `A` (`Hartshorne.hasDominatingDVR_of_closure_eq_top`) gives
  a valuative square `Spec κ(x) ⟶ X`, `Spec R' ⟶ Spec Γ(V) ⟶ Y`; its lift sends the closed point
  into some `Uⱼ ∋ x`, so `βⱼ ∈ R'` (`Hartshorne.evaluation_mem_range_of_comp_eq`), while `βⱼ⁻¹`
  lies in the maximal ideal of `R'`, a contradiction.
-/

open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace

namespace Hartshorne

universe u

section

variable {R : Type u} [CommRing R]

/-- A morphism from the spectrum of a local ring sending the closed point into an open set
`V` maps every point into `V`. -/
lemma mem_of_closedPoint_mem [IsLocalRing R] {Y : Scheme.{u}} (g : Spec (CommRingCat.of R) ⟶ Y)
    {V : Y.Opens} (hV : g (closedPoint R) ∈ V) (p : Spec (CommRingCat.of R)) : g p ∈ V :=
  ((specializes_closedPoint p).map g.continuous).mem_open V.isOpen hV

/-- A morphism from an affine spectrum whose image lies in an affine open `V` factors through
`Spec Γ(V) ⟶ Y`. -/
lemma exists_eq_specMap_comp_fromSpec {Y : Scheme.{u}} (g : Spec (CommRingCat.of R) ⟶ Y)
    {V : Y.Opens} (hV : IsAffineOpen V) (hg : ∀ p, g p ∈ V) :
    ∃ ρ : Γ(Y, V) ⟶ CommRingCat.of R, g = Spec.map ρ ≫ hV.fromSpec := by
  have hrange : Set.range g ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact hg p
  refine ⟨Spec.preimage (IsOpenImmersion.lift hV.fromSpec g hrange), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

/-- The canonical morphism `Spec κ(x) ⟶ X` factors through an affine open `U ∋ x` as the
spectrum of the evaluation map `Γ(U) ⟶ κ(x)`. -/
lemma specMap_evaluation_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) :
    Spec.map (X.evaluation U x hx) ≫ hU.fromSpec = X.fromSpecResidueField x := by
  rw [← Scheme.germ_residue, Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk,
    hU.fromSpecStalk_eq_fromSpecStalk, Scheme.fromSpecResidueField]

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R] {K : Type u} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- Two morphisms `Spec R ⟶ Y` from the spectrum of a local domain `R` with fraction field `K`
that send the closed point into a common affine open and agree on `Spec K` are equal. -/
lemma eq_of_specMap_algebraMap_comp_eq {Y : Scheme.{u}} (g₁ g₂ : Spec (CommRingCat.of R) ⟶ Y)
    {V : Y.Opens} (hV : IsAffineOpen V) (h₁ : g₁ (closedPoint R) ∈ V)
    (h₂ : g₂ (closedPoint R) ∈ V)
    (h : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g₁ =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g₂) : g₁ = g₂ := by
  obtain ⟨ρ₁, rfl⟩ := exists_eq_specMap_comp_fromSpec g₁ hV (mem_of_closedPoint_mem g₁ h₁)
  obtain ⟨ρ₂, rfl⟩ := exists_eq_specMap_comp_fromSpec g₂ hV (mem_of_closedPoint_mem g₂ h₂)
  have hmono : Mono (CommRingCat.ofHom (algebraMap R K)) :=
    ConcreteCategory.mono_of_injective _ (IsFractionRing.injective R K)
  have hρ : ρ₁ ≫ CommRingCat.ofHom (algebraMap R K) = ρ₂ ≫ CommRingCat.ofHom (algebraMap R K) := by
    rw [← Spec.map_inj, ← cancel_mono hV.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc,
      Category.assoc, h]
  rw [cancel_mono] at hρ
  rw [hρ]

omit [IsFractionRing R K] in
/-- If a morphism `l : Spec R ⟶ X` restricts on `Spec K` to the point `x` with the embedding
`ι : κ(x) ⟶ K`, and sends the closed point into an affine open `U`, then the evaluation map
`Γ(U) ⟶ κ(x) ⟶ K` takes values in `R`. -/
lemma evaluation_mem_range_of_comp_eq {X : Scheme.{u}} (l : Spec (CommRingCat.of R) ⟶ X)
    {x : X} (ι : X.residueField x ⟶ CommRingCat.of K)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = Spec.map ι ≫ X.fromSpecResidueField x)
    {U : X.Opens} (hU : IsAffineOpen U) (hlU : l (closedPoint R) ∈ U) (hx : x ∈ U)
    (a : Γ(X, U)) : ι (X.evaluation U x hx a) ∈ (algebraMap R K).range := by
  obtain ⟨ψ, rfl⟩ := exists_eq_specMap_comp_fromSpec l hU (mem_of_closedPoint_mem l hlU)
  have hψ : ψ ≫ CommRingCat.ofHom (algebraMap R K) = X.evaluation U x hx ≫ ι := by
    rw [← Spec.map_inj, ← cancel_mono hU.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc,
      Category.assoc, specMap_evaluation_fromSpec, ← hl]
  exact ⟨ψ a, congr($hψ a)⟩

end

section

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- If the evaluation map `Γ(U) ⟶ κ(x) ⟶ K` of an affine open `U ∋ x` lying over an affine
open `V` of `Y` containing the image of the closed point takes values in the valuation ring,
then the valuative square has a lift. -/
lemma hasLift_of_evaluation_mem (S : ValuativeCommSq f) {x : X}
    (ι : X.residueField x ⟶ CommRingCat.of S.K)
    (hi : S.i₁ = Spec.map ι ≫ X.fromSpecResidueField x) {V : Y.Opens} (hV : IsAffineOpen V)
    (hy : S.i₂ (closedPoint S.R) ∈ V) {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
    (hx : x ∈ U) (hmem : ∀ a, ι (X.evaluation U x hx a) ∈ (algebraMap S.R S.K).range) :
    S.commSq.HasLift := by
  let e : S.R ≃+* (algebraMap S.R S.K).range := RingEquiv.ofBijective
    (algebraMap S.R S.K).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective S.R S.K (congrArg Subtype.val hab),
      (algebraMap S.R S.K).rangeRestrict_surjective⟩
  let ψ : Γ(X, U) ⟶ CommRingCat.of S.R := CommRingCat.ofHom
    (e.symm.toRingHom.comp ((X.evaluation U x hx ≫ ι).hom.codRestrict _ hmem))
  have hψ : ψ ≫ CommRingCat.ofHom (algebraMap S.R S.K) = X.evaluation U x hx ≫ ι := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply _)
  let l : Spec (CommRingCat.of S.R) ⟶ X := Spec.map ψ ≫ hU.fromSpec
  have hl₁ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l = S.i₁ := by
    rw [hi, ← specMap_evaluation_fromSpec hU hx, ← Spec.map_comp_assoc, hψ, Spec.map_comp,
      Category.assoc]
  have hlU : l (closedPoint S.R) ∈ U := by
    have := Set.mem_range_self (f := hU.fromSpec) (Spec.map ψ (closedPoint S.R))
    rwa [hU.range_fromSpec] at this
  have hl₂ : l ≫ f = S.i₂ :=
    eq_of_specMap_algebraMap_comp_eq (K := S.K) _ _ hV (hUV hlU) hy
      (by rw [← Category.assoc, hl₁, S.commSq.w])
  exact ⟨⟨⟨l, hl₁, hl₂⟩⟩⟩

end

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Every element of `κ(x)` is a quotient of values at `x` of sections over an affine open
neighbourhood `U` of `x`. -/
lemma exists_evaluation_div {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (c : X.residueField x) :
    ∃ a b : Γ(X, U), X.evaluation U x hx b ≠ 0 ∧
      c = X.evaluation U x hx a / X.evaluation U x hx b := by
  obtain ⟨s, rfl⟩ := X.residue_surjective x c
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨a, b, hb⟩, hab⟩ :=
    IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
  have hbu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) b) :=
    IsLocalization.map_units _ (⟨b, hb⟩ : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
  have hb0 : X.residue x (algebraMap Γ(X, U) (X.presheaf.stalk x) b) ≠ 0 :=
    (hbu.map (X.residue x).hom).ne_zero
  change X.residue x (X.presheaf.germ U x hx b) ≠ 0 at hb0
  change s * X.presheaf.germ U x hx b = X.presheaf.germ U x hx a at hab
  refine ⟨a, b, hb0, ?_⟩
  change _ = X.residue x (X.presheaf.germ U x hx a) / X.residue x (X.presheaf.germ U x hx b)
  rw [eq_div_iff hb0, ← map_mul, hab]

/-- The evaluation of an affine open `V ∋ f x` of `Y`, followed by `κ(f x) ⟶ κ(x)`, factors
`Spec κ(x) ⟶ X ⟶ Y` through `Spec Γ(V) ⟶ Y`. -/
lemma specMap_evaluation_residueFieldMap_fromSpec {V : Y.Opens} (hV : IsAffineOpen V) {x : X}
    (hx : f x ∈ V) :
    Spec.map (Y.evaluation V (f x) hx ≫ f.residueFieldMap x) ≫ hV.fromSpec =
      X.fromSpecResidueField x ≫ f := by
  rw [Spec.map_comp, Category.assoc, specMap_evaluation_fromSpec,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- Restricting along `f.appLE` and then evaluating at `x` is evaluating at `f x` followed by
`κ(f x) ⟶ κ(x)`. -/
lemma appLE_evaluation {V : Y.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ V) {x : X} (hx : x ∈ W) :
    f.appLE V W e ≫ X.evaluation W x hx =
      Y.evaluation V (f x) (show f x ∈ V from e hx) ≫ f.residueFieldMap x := by
  rw [Scheme.evaluation_naturality f x (show f x ∈ V from e hx), Scheme.Hom.appLE,
    Category.assoc, ← Scheme.germ_residue, ← Scheme.germ_residue, X.presheaf.germ_res_assoc]

end

/-- If every valuative square over a quasi-compact, locally of finite type morphism `f` with
locally Noetherian target whose valuation ring is a discrete valuation ring has a lift, then every
valuative square over `f` has a lift. -/
theorem valuativeCriterion_existence_of_dvr {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (H : ∀ S : ValuativeCommSq f, IsDiscreteValuationRing S.R → S.commSq.HasLift) :
    ValuativeCriterion.Existence f := by
  intro S
  classical
  obtain ⟨⟨x, ι⟩, hi⟩ : ∃ p : Σ x : X, X.residueField x ⟶ CommRingCat.of S.K,
      S.i₁ = Spec.map p.2 ≫ X.fromSpecResidueField p.1 :=
    ⟨_, ((Scheme.SpecToEquivOfField S.K X).symm_apply_apply S.i₁).symm⟩
  dsimp only at hi
  obtain ⟨V, hV, hyV, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show S.i₂ (closedPoint S.R) ∈ (⊤ : Y.Opens) from trivial)
  have hV : IsAffineOpen V := hV
  -- `x` lies over `V`
  have hxV : f x ∈ V := by
    obtain ⟨p₀⟩ : Nonempty (Spec (CommRingCat.of S.K)) := inferInstance
    have h₁ : S.i₁ p₀ = x := by rw [hi]; simp
    rw [← h₁, ← Scheme.Hom.comp_apply, S.commSq.w, Scheme.Hom.comp_apply]
    exact mem_of_closedPoint_mem S.i₂ hyV _
  -- the comparison map `Γ(V) ⟶ κ(x)`
  let γV : Γ(Y, V) ⟶ X.residueField x := Y.evaluation V (f x) hxV ≫ f.residueFieldMap x
  have hγV : Spec.map γV ≫ hV.fromSpec = X.fromSpecResidueField x ≫ f :=
    specMap_evaluation_residueFieldMap_fromSpec f hV hxV
  have hγVR : ∀ r, ι (γV r) ∈ (algebraMap S.R S.K).range := by
    obtain ⟨ρ, hρ⟩ := exists_eq_specMap_comp_fromSpec S.i₂ hV (mem_of_closedPoint_mem S.i₂ hyV)
    have : ρ ≫ CommRingCat.ofHom (algebraMap S.R S.K) = γV ≫ ι := by
      rw [← Spec.map_inj, ← cancel_mono hV.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc,
        Category.assoc, ← hρ, hγV, ← S.commSq.w, hi, Category.assoc]
    exact fun r => ⟨ρ r, congr($this r)⟩
  -- a finite affine cover of `f ⁻¹ V`
  have hloc : ∀ z ∈ (f ⁻¹ᵁ V : Set X), ∃ W : X.Opens, IsAffineOpen W ∧ z ∈ W ∧ W ≤ f ⁻¹ᵁ V :=
    fun z hz => by
      obtain ⟨W, hW, hzW, hWV⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hz
      exact ⟨W, hW, hzW, hWV⟩
  choose! W hW hzW hWV using hloc
  obtain ⟨t, htV, htcover⟩ := (f.isCompact_preimage hV.isCompact).elim_nhds_subcover
    (fun z => (W z : Set X)) fun z hz => (W z).isOpen.mem_nhds (hzW z hz)
  by_contra hno
  have hb : ∀ z ∈ t, ∀ hx : x ∈ W z, ∃ a : Γ(X, W z),
      ι (X.evaluation (W z) x hx a) ∉ (algebraMap S.R S.K).range := by
    intro z hz hx
    by_contra hall
    push Not at hall
    exact hno (hasLift_of_evaluation_mem S ι hi hV hyV (hW z (htV z hz)) (hWV z (htV z hz)) hx
      hall)
  choose b hb using hb
  let s : Set (X.residueField x) :=
    ⋃ z ∈ (t : Set X), ⋃ hx : x ∈ W z, {(X.evaluation (W z) x hx (b z ‹_› hx))⁻¹}
  have hs : s.Finite := by
    simp only [s]
    refine Set.Finite.biUnion' t.finite_toSet fun z _ => ?_
    exact Set.finite_iUnion fun _ => Set.finite_singleton _
  have hsR : ∀ c ∈ s, ∃ r : S.R, r ∈ maximalIdeal S.R ∧ ι c = algebraMap S.R S.K r := by
    intro c hc
    simp only [s, Set.mem_iUnion, Set.mem_singleton_iff] at hc
    obtain ⟨z, hz, hx, rfl⟩ := hc
    have hβ := hb z hz hx
    rw [map_inv₀]
    rcases ValuationRing.isInteger_or_isInteger S.R (ι (X.evaluation (W z) x hx (b z hz hx)))
      with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact absurd ⟨r, hr⟩ hβ
    refine ⟨r, (mem_maximalIdeal _).mpr fun hu => hβ ?_, hr.symm⟩
    refine ⟨↑(hu.unit⁻¹), ?_⟩
    have h1 : algebraMap S.R S.K ↑(hu.unit⁻¹) * algebraMap S.R S.K r = 1 := by
      rw [← map_mul, hu.val_inv_mul, map_one]
    rw [eq_inv_of_mul_eq_one_left h1, hr, inv_inv]
  -- the subring `D = Γ(V)[1 / b_z]` of `κ(x)`, which maps to `R`
  let : Algebra Γ(Y, V) (X.residueField x) := γV.hom.toAlgebra
  let D : Subalgebra Γ(Y, V) (X.residueField x) := Algebra.adjoin Γ(Y, V) s
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Algebra.FiniteType Γ(Y, V) D := by
    rw [← Subalgebra.fg_iff_finiteType]
    have := Subalgebra.fg_adjoin_finset (R := Γ(Y, V)) hs.toFinset
    rwa [hs.coe_toFinset] at this
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing Γ(Y, V) D
  have hDR : ∀ d ∈ D, ι d ∈ (algebraMap S.R S.K).range := by
    intro d hd
    induction hd using Algebra.adjoin_induction with
    | mem c hc =>
      obtain ⟨r, -, hr⟩ := hsR c hc
      exact ⟨r, hr.symm⟩
    | algebraMap r => exact hγVR r
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  let e : S.R ≃+* (algebraMap S.R S.K).range := RingEquiv.ofBijective
    (algebraMap S.R S.K).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective S.R S.K (congrArg Subtype.val hab),
      (algebraMap S.R S.K).rangeRestrict_surjective⟩
  let ρD : D →+* S.R := e.symm.toRingHom.comp
    ((ι.hom.comp (algebraMap D (X.residueField x))).codRestrict _ fun d => hDR d d.2)
  have hρD : ∀ d : D, algebraMap S.R S.K (ρD d) = ι d :=
    fun d => congrArg Subtype.val (e.apply_symm_apply _)
  let P : Ideal D := (maximalIdeal S.R).comap ρD
  have hsP : ∀ c (hc : c ∈ s), (⟨c, Algebra.subset_adjoin hc⟩ : D) ∈ P := by
    intro c hc
    obtain ⟨r, hr, hcr⟩ := hsR c hc
    have : ρD ⟨c, Algebra.subset_adjoin hc⟩ = r :=
      IsFractionRing.injective S.R S.K (by rw [hρD]; exact hcr)
    change ρD _ ∈ maximalIdeal S.R
    rwa [this]
  -- the Noetherian local subring `A = D_P` of `κ(x)`
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap D (X.residueField x) y) := by
    intro y
    apply IsUnit.mk0
    intro h0
    apply y.2
    have : ρD y = 0 := IsFractionRing.injective S.R S.K (by
      rw [hρD, map_zero]
      exact (congrArg ι h0).trans (map_zero _))
    change ρD y ∈ maximalIdeal S.R
    rw [this]
    exact zero_mem _
  let φ : Localization.AtPrime P →+* X.residueField x := IsLocalization.lift hunit
  let A : Subring (X.residueField x) := φ.range
  have : IsLocalRing A := IsLocalRing.of_surjective' φ.rangeRestrict φ.rangeRestrict_surjective
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have : IsNoetherianRing A := isNoetherianRing_range φ
  have hDA : ∀ d : D, (d : X.residueField x) ∈ A :=
    fun d => ⟨algebraMap D _ d, IsLocalization.lift_eq hunit d⟩
  have hsA : ∀ c (hc : c ∈ s),
      (⟨c, hDA ⟨c, Algebra.subset_adjoin hc⟩⟩ : A) ∈ maximalIdeal A := by
    intro c hc
    have : IsLocalHom φ.rangeRestrict := IsLocalHom.of_surjective _ φ.rangeRestrict_surjective
    have h1 : algebraMap D (Localization.AtPrime P) ⟨c, Algebra.subset_adjoin hc⟩ ∈
        maximalIdeal (Localization.AtPrime P) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr (hsP c hc)
    have h2 : φ.rangeRestrict (algebraMap D _ ⟨c, Algebra.subset_adjoin hc⟩) =
        ⟨c, hDA ⟨c, Algebra.subset_adjoin hc⟩⟩ :=
      Subtype.ext (IsLocalization.lift_eq hunit _)
    rw [← h2]
    exact map_nonunit φ.rangeRestrict _ h1
  -- some `W z₁` contains `x`, and the elements `1 / b_z` are nonzero elements of `𝔪_A`
  obtain ⟨z₁, hz₁, hxz₁⟩ : ∃ z ∈ t, x ∈ W z := by
    simpa using htcover (show x ∈ (f ⁻¹ᵁ V : Set X) from hxV)
  have hβne : ∀ z (hz : z ∈ t) (hx : x ∈ W z), X.evaluation (W z) x hx (b z hz hx) ≠ 0 := by
    intro z hz hx h0
    apply hb z hz hx
    rw [h0, map_zero]
    exact zero_mem _
  have hmem_s : ∀ z (hz : z ∈ t) (hx : x ∈ W z),
      (X.evaluation (W z) x hx (b z hz hx))⁻¹ ∈ s := by
    intro z hz hx
    simp only [s, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨z, hz, hx, rfl⟩
  have hm : maximalIdeal A ≠ ⊥ := by
    intro hbot
    have := hsA _ (hmem_s z₁ hz₁ hxz₁)
    rw [hbot, Ideal.mem_bot] at this
    exact inv_ne_zero (hβne z₁ hz₁ hxz₁) (congrArg Subtype.val this)
  -- `κ(x)` is generated as a field over `A` by finitely many elements
  have hft := f.finiteType_appLE hV (hW z₁ (htV z₁ hz₁)) (hWV z₁ (htV z₁ hz₁))
  let : Algebra Γ(Y, V) Γ(X, W z₁) := (f.appLE V (W z₁) (hWV z₁ (htV z₁ hz₁))).hom.toAlgebra
  obtain ⟨T, hT⟩ := hft.out
  let S₀ : Finset (X.residueField x) := T.image (X.evaluation (W z₁) x hxz₁)
  have hev : ∀ a : Γ(X, W z₁),
      X.evaluation (W z₁) x hxz₁ a ∈ Subfield.closure ((A : Set (X.residueField x)) ∪ S₀) := by
    intro a
    have ha : a ∈ Algebra.adjoin Γ(Y, V) (T : Set Γ(X, W z₁)) := hT ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem c hc => exact Subfield.subset_closure (Or.inr (Finset.mem_image_of_mem _ hc))
    | algebraMap r =>
      apply Subfield.subset_closure
      left
      have : X.evaluation (W z₁) x hxz₁ (algebraMap Γ(Y, V) Γ(X, W z₁) r) = γV r :=
        congr($(appLE_evaluation f (hWV z₁ (htV z₁ hz₁)) hxz₁) r)
      rw [this]
      exact hDA ⟨_, Subalgebra.algebraMap_mem D r⟩
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  have hclosure : Subfield.closure ((A : Set (X.residueField x)) ∪ S₀) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨a, a', -, rfl⟩ := exists_evaluation_div (hW z₁ (htV z₁ hz₁)) hxz₁ c
    exact div_mem (hev a) (hev a')
  obtain ⟨R'', hR, hRf, hle, hloc⟩ :=
    hasDominatingDVR_of_closure_eq_top S₀.card A hm S₀ rfl hclosure
  -- the valuative square with the dominating discrete valuation ring `R''` of `κ(x)`
  let θ : Γ(Y, V) ⟶ CommRingCat.of R'' := CommRingCat.ofHom
    (γV.hom.codRestrict R'' fun r => hle (hDA ⟨_, Subalgebra.algebraMap_mem D r⟩))
  have hw : X.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R'' (X.residueField x))) ≫
        Spec.map θ ≫ hV.fromSpec := by
    rw [← Spec.map_comp_assoc, ← hγV]
    rfl
  let S'' : ValuativeCommSq f :=
    { R := R'', K := X.residueField x, i₁ := X.fromSpecResidueField x,
      i₂ := Spec.map θ ≫ hV.fromSpec, commSq := ⟨hw⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (H S'' hR).exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap R'' (X.residueField x))) ≫ l =
    X.fromSpecResidueField x at hl₁
  change l ≫ f = Spec.map θ ≫ hV.fromSpec at hl₂
  -- the closed point of `Spec R''` maps into some `W z`, hence so does `x`
  have hlV : f (l (closedPoint R'')) ∈ V := by
    have h := Set.mem_range_self (f := hV.fromSpec) (Spec.map θ (closedPoint R''))
    rw [hV.range_fromSpec] at h
    change (Spec.map θ ≫ hV.fromSpec) (closedPoint R'') ∈ V at h
    rw [← hl₂] at h
    exact h
  obtain ⟨z, hz, hz₀⟩ : ∃ z ∈ t, l (closedPoint R'') ∈ W z := by
    simpa using htcover hlV
  have hx : x ∈ W z := by
    obtain ⟨p₀⟩ : Nonempty (Spec (CommRingCat.of (X.residueField x))) := inferInstance
    have : l (Spec.map (CommRingCat.ofHom (algebraMap R'' (X.residueField x))) p₀) = x := by
      change (Spec.map (CommRingCat.ofHom (algebraMap R'' (X.residueField x))) ≫ l) p₀ = x
      rw [hl₁]
      exact Scheme.fromSpecResidueField_apply x p₀
    rw [← this]
    exact mem_of_closedPoint_mem l hz₀ _
  -- then `b_z ∈ R''` while `1 / b_z ∈ 𝔪_{R''}`, a contradiction
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R'' (X.residueField x))) ≫ l =
      Spec.map (𝟙 (X.residueField x)) ≫ X.fromSpecResidueField x := by
    rw [Spec.map_id, Category.id_comp]
    exact hl₁
  obtain ⟨r₁, hr₁⟩ := evaluation_mem_range_of_comp_eq (R := R'') (K := X.residueField x) l
    (𝟙 (X.residueField x)) hl₁' (hW z (htV z hz)) hz₀ hx (b z hz hx)
  have hmax := map_nonunit (Subring.inclusion hle) _ (hsA _ (hmem_s z hz hx))
  apply (mem_maximalIdeal _).mp hmax
  refine IsUnit.of_mul_eq_one r₁ (Subtype.ext ?_)
  change _ * algebraMap R'' (X.residueField x) r₁ = 1
  rw [hr₁]
  exact inv_mul_cancel₀ (hβne z hz hx)

/-- **Hartshorne II, Exercise 4.11(b)** (properness clause). A finite-type morphism
`f : X ⟶ Y` of Noetherian schemes is proper if and only if every valuative commutative square
over `f` whose valuation ring is a discrete valuation ring has a unique lift. -/
theorem isProper_iff_dvr_valuativeCriterion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] (hf : FiniteType f) :
    IsProper f ↔ ∀ S : ValuativeCommSq f, IsDiscreteValuationRing S.R →
      Nonempty (Unique S.commSq.LiftStruct) := by
  have : LocallyOfFiniteType f := hf.1
  have : QuasiCompact f := hf.2
  refine ⟨fun hp S _ => ?_, fun H => ?_⟩
  · rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1 S
  · have hsep : IsSeparated f := (isSeparated_iff_dvr_valuativeCriterion f hf).mpr fun S hS => by
      obtain ⟨_⟩ := H S hS
      infer_instance
    have : UniversallyClosed f := UniversallyClosed.of_valuativeCriterion f
      (valuativeCriterion_existence_of_dvr f fun S hS => by
        obtain ⟨_⟩ := H S hS
        exact ⟨⟨default⟩⟩)
    exact
      { toIsSeparated := hsep
        toUniversallyClosed := this
        toLocallyOfFiniteType := ‹_› }

end Hartshorne
