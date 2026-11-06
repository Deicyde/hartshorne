/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ReducedInducedSubscheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Maps from spectra of valuation rings

Hartshorne, *Algebraic Geometry*, II.4, Lemma 4.4 (pp. 97–98).

Let `R` be a valuation ring with fraction field `K` and let `X` be a scheme. A morphism
`Spec R ⟶ X` is the same as the following data:

* a point `x₁ : X` with an embedding of fields `κ(x₁) ⟶ K` (the image of the generic point,
  i.e. the `K`-valued point `Spec K ⟶ Spec R ⟶ X`);
* a point `x₀ : X` with `x₁ ⤳ x₀` (the image of the closed point);
* such that `R` dominates the image in `K` of the local ring of `x₀` on the closed subscheme
  `Z = closure {x₁}` with its reduced induced structure.

Here the local ring `𝒪_{Z, x₀}` maps to `K` through `κ(x₁)`: it maps to the stalk of `Z` at the
point over `x₁` (the generic point of `Z`), then to the residue field there, which the closed
immersion `Z ⟶ X` identifies with `κ(x₁)`.

We record:

* `Hartshorne.reducedPointClosure x`: the reduced induced closed subscheme on `closure {x}`;
* `Hartshorne.reducedPointClosurePoint h`: for `h : x₁ ⤳ x₀`, the point of
  `reducedPointClosure x₁` over `x₀`;
* `Hartshorne.reducedPointClosureStalkToResidueField h`: the map
  `𝒪_{Z, x₀} ⟶ κ(x₁)`;
* `Hartshorne.ValuationSpecData R K X`: Hartshorne's data `(x₁, κ(x₁) ⟶ K, x₁ ⤳ x₀)` with the
  domination condition, stated with the domination order on local subrings of `K`;
* `Hartshorne.valuationSpecEquiv R K X`: the equivalence
  `(Spec R ⟶ X) ≃ ValuationSpecData R K X`;
* `Hartshorne.bijective_toValuationSpecData`: the map from morphisms to this data is bijective.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace Hartshorne

universe u

section

variable {X : Scheme.{u}}

/-- The residue field map of a morphism that is surjective on stalks is an isomorphism. -/
instance isIso_residueFieldMap_of_surjectiveOnStalks {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [SurjectiveOnStalks f] (y : Y) : IsIso (f.residueFieldMap y) := by
  have hsurj : Function.Surjective (f.residueFieldMap y) := by
    intro a
    obtain ⟨b, rfl⟩ := Y.residue_surjective y a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective y b
    exact ⟨Z.residue (f y) c, by
      rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.residueFieldMap y).hom.injective, hsurj⟩

/-- The closed subset `closure {x}` of a scheme. -/
def pointClosure (x : X) : Closeds X :=
  ⟨closure {x}, isClosed_closure⟩

/-- The closed subscheme `closure {x}` with its reduced induced structure. -/
noncomputable abbrev reducedPointClosure (x : X) : Scheme.{u} :=
  reducedInducedSubscheme (pointClosure x)

lemma exists_reducedPointClosure_point {x₁ x₀ : X} (h : x₁ ⤳ x₀) :
    ∃ z, reducedInducedSubschemeι (pointClosure x₁) z = x₀ := by
  have : x₀ ∈ Set.range (reducedInducedSubschemeι (pointClosure x₁)) := by
    rw [range_reducedInducedSubschemeι]
    exact specializes_iff_mem_closure.mp h
  exact this

/-- For `x₁ ⤳ x₀`, the point of the reduced closure of `x₁` lying over `x₀`. -/
noncomputable def reducedPointClosurePoint {x₁ x₀ : X} (h : x₁ ⤳ x₀) :
    reducedPointClosure x₁ :=
  (exists_reducedPointClosure_point h).choose

@[simp]
lemma reducedInducedSubschemeι_reducedPointClosurePoint {x₁ x₀ : X} (h : x₁ ⤳ x₀) :
    reducedInducedSubschemeι (pointClosure x₁) (reducedPointClosurePoint h) = x₀ :=
  (exists_reducedPointClosure_point h).choose_spec

/-- In the reduced closure of `x₁`, the point over `x₁` specializes to the point over `x₀`. -/
lemma reducedPointClosurePoint_specializes {x₁ x₀ : X} (h : x₁ ⤳ x₀) :
    reducedPointClosurePoint (specializes_refl x₁) ⤳ reducedPointClosurePoint h := by
  rw [← (reducedInducedSubschemeι (pointClosure x₁)).isClosedEmbedding.isInducing.specializes_iff,
    reducedInducedSubschemeι_reducedPointClosurePoint,
    reducedInducedSubschemeι_reducedPointClosurePoint]
  exact h

/-- The map from the local ring of `x₀` on the reduced closure `Z` of `x₁` to `κ(x₁)`: the
stalk of `Z` at the point over `x₀` maps to the stalk at the point over `x₁` (the generic
point of `Z`), then to its residue field, which the closed immersion `Z ⟶ X` identifies with
`κ(x₁)`. -/
noncomputable def reducedPointClosureStalkToResidueField {x₁ x₀ : X} (h : x₁ ⤳ x₀) :
    (reducedPointClosure x₁).presheaf.stalk (reducedPointClosurePoint h) ⟶
      X.residueField x₁ :=
  (reducedPointClosure x₁).presheaf.stalkSpecializes (reducedPointClosurePoint_specializes h) ≫
    (reducedPointClosure x₁).residue _ ≫
      inv ((reducedInducedSubschemeι (pointClosure x₁)).residueFieldMap _) ≫
        (X.residueFieldCongr
          (reducedInducedSubschemeι_reducedPointClosurePoint (specializes_refl x₁))).hom

end

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
  (K : Type u) [Field K] [Algebra R K] (X : Scheme.{u})

/-- Hartshorne's data classifying morphisms `Spec R ⟶ X` for a valuation ring `R` of `K`:
a point `x₁` with an embedding `κ(x₁) ⟶ K`, a specialization `x₁ ⤳ x₀`, such that `R`
dominates the image in `K` of the local ring of `x₀` on the reduced closure of `x₁`. -/
@[ext]
structure ValuationSpecData where
  /-- The generic point datum: a point `x₁` and an embedding `κ(x₁) ⟶ K`. -/
  generic : Σ x₁ : X, X.residueField x₁ ⟶ CommRingCat.of K
  /-- The point `x₀`. -/
  closed : X
  /-- The specialization `x₁ ⤳ x₀`. -/
  specializes : generic.1 ⤳ closed
  /-- `R` dominates the image in `K` of the local ring of `x₀` on the reduced closure of
  `x₁`. -/
  dominates : LocalSubring.range (reducedPointClosureStalkToResidueField specializes ≫
    generic.2).hom ≤ LocalSubring.range (algebraMap R K)

variable {R K X}

lemma stalkSpecializes_residue_residueFieldCongr {y x₁ x₀ : X} (e : y = x₁) (h : x₁ ⤳ x₀)
    (h' : y ⤳ x₀) :
    X.presheaf.stalkSpecializes h' ≫ X.residue y ≫ (X.residueFieldCongr e).hom =
      X.presheaf.stalkSpecializes h ≫ X.residue x₁ := by
  subst e
  simp

lemma stalkSpecializes_of_eq_surjective {x y : X} (e : x = y) :
    Function.Surjective (X.presheaf.stalkSpecializes (specializes_of_eq e)) := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.surjective_id

/-- The stalk map of the closed immersion of the reduced closure, followed by the map
`𝒪_{Z, x₀} ⟶ κ(x₁)`, is the canonical map `𝒪_{X, x₀} ⟶ κ(x₁)`. -/
lemma stalkMap_reducedPointClosureStalkToResidueField {x₁ x₀ : X} (h : x₁ ⤳ x₀) :
    X.presheaf.stalkSpecializes
        (specializes_of_eq (reducedInducedSubschemeι_reducedPointClosurePoint h)) ≫
      (reducedInducedSubschemeι (pointClosure x₁)).stalkMap (reducedPointClosurePoint h) ≫
        reducedPointClosureStalkToResidueField h =
      X.presheaf.stalkSpecializes h ≫ X.residue x₁ := by
  rw [reducedPointClosureStalkToResidueField,
    ← Scheme.Hom.stalkSpecializes_stalkMap_assoc, ← Scheme.residue_residueFieldMap_assoc,
    IsIso.hom_inv_id_assoc, TopCat.Presheaf.stalkSpecializes_comp_assoc]
  exact stalkSpecializes_residue_residueFieldCongr _ _ _

/-- The image in `K` of the local ring of `x₀` on the reduced closure of `x₁` is the image of
`𝒪_{X, x₀}` under `𝒪_{X, x₀} ⟶ κ(x₁) ⟶ K`. -/
lemma range_reducedPointClosureStalkToResidueField {x₁ x₀ : X} (h : x₁ ⤳ x₀)
    (ι : X.residueField x₁ ⟶ CommRingCat.of K) :
    LocalSubring.range (reducedPointClosureStalkToResidueField h ≫ ι).hom =
      LocalSubring.range (X.presheaf.stalkSpecializes h ≫ X.residue x₁ ≫ ι).hom := by
  ext a
  change a ∈ Set.range _ ↔ a ∈ Set.range _
  rw [← Category.assoc (X.presheaf.stalkSpecializes h),
    ← stalkMap_reducedPointClosureStalkToResidueField h]
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := (reducedInducedSubschemeι (pointClosure x₁)).stalkMap_surjective _ b
    obtain ⟨d, rfl⟩ := stalkSpecializes_of_eq_surjective
      (reducedInducedSubschemeι_reducedPointClosurePoint h) c
    exact ⟨d, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, rfl⟩

/-- For a local ring `A` and a map `F : A ⟶ K`, the valuation ring `R` dominates the image of
`F` exactly when `F` factors through a local homomorphism `A ⟶ R`. -/
lemma range_le_range_algebraMap_iff [IsFractionRing R K] {A : CommRingCat.{u}} [IsLocalRing A]
    (F : A ⟶ CommRingCat.of K) :
    LocalSubring.range F.hom ≤ LocalSubring.range (algebraMap R K) ↔
      ∃ f : A ⟶ CommRingCat.of R, IsLocalHom f.hom ∧
        f ≫ CommRingCat.ofHom (algebraMap R K) = F := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let e : R ≃+* (LocalSubring.range (algebraMap R K)).toSubring :=
    RingEquiv.ofBijective ((algebraMap R K).codRestrict
      (LocalSubring.range (algebraMap R K)).toSubring (fun r => ⟨r, rfl⟩))
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩⟩
  let s : A →+* (LocalSubring.range F.hom).toSubring := F.hom.codRestrict _ (fun a => ⟨a, rfl⟩)
  have hs : Function.Surjective s := by rintro ⟨_, a, rfl⟩; exact ⟨a, rfl⟩
  have : IsLocalHom s := IsLocalHom.of_surjective s hs
  constructor
  · rintro ⟨hle, hloc⟩
    refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp ((Subring.inclusion hle).comp s)), ?_, ?_⟩
    · have : IsLocalHom e.symm.toRingHom := IsLocalHom.of_surjective _ e.symm.surjective
      exact RingHom.isLocalHom_comp _ _
    · ext a
      exact congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle (s a)))
  · rintro ⟨f, hf, rfl⟩
    have hle : (LocalSubring.range (f ≫ CommRingCat.ofHom (algebraMap R K)).hom).toSubring ≤
        (LocalSubring.range (algebraMap R K)).toSubring := by
      rintro _ ⟨a, rfl⟩
      exact ⟨f a, rfl⟩
    refine ⟨hle, ⟨?_⟩⟩
    rintro ⟨_, a, rfl⟩ hu
    have h1 : Subring.inclusion hle (s a) = e (f.hom a) := Subtype.ext rfl
    change IsUnit (Subring.inclusion hle (s a)) at hu
    rw [h1, isUnit_map_iff e] at hu
    exact (isUnit_of_map_unit f.hom a hu).map s

/-- The canonical maps `Spec K ⟶ X` built from `𝒪_{X, x₀}` and from `κ(x₁)` agree exactly
when the stalk map factors through `κ(x₁)`. -/
lemma specMap_fromSpecStalk_eq_iff {x₁ x₀ : X} (h : x₁ ⤳ x₀)
    (F : X.presheaf.stalk x₀ ⟶ CommRingCat.of K) (ι : X.residueField x₁ ⟶ CommRingCat.of K) :
    Spec.map F ≫ X.fromSpecStalk x₀ = Spec.map ι ≫ X.fromSpecResidueField x₁ ↔
      F = X.presheaf.stalkSpecializes h ≫ X.residue x₁ ≫ ι := by
  rw [Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, cancel_mono, Spec.map_inj]

/-- The domination condition says that `𝒪_{X, x₀} ⟶ κ(x₁) ⟶ K` factors through a local
homomorphism `𝒪_{X, x₀} ⟶ R`. -/
lemma valuationSpec_dominates_iff [IsFractionRing R K] {x₁ x₀ : X} (h : x₁ ⤳ x₀)
    (ι : X.residueField x₁ ⟶ CommRingCat.of K) :
    LocalSubring.range (reducedPointClosureStalkToResidueField h ≫ ι).hom ≤
        LocalSubring.range (algebraMap R K) ↔
      ∃ f : X.presheaf.stalk x₀ ⟶ CommRingCat.of R, IsLocalHom f.hom ∧
        f ≫ CommRingCat.ofHom (algebraMap R K) =
          X.presheaf.stalkSpecializes h ≫ X.residue x₁ ≫ ι := by
  rw [range_reducedPointClosureStalkToResidueField]
  exact range_le_range_algebraMap_iff _

/-- The image of the generic point of `Spec R` specializes to the image of the closed point. -/
lemma valuationSpec_specializes (φ : Spec (CommRingCat.of R) ⟶ X) :
    (Scheme.SpecToEquivOfField K X
        (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ φ)).1 ⤳ φ (closedPoint R) :=
  (specializes_closedPoint _).map φ.continuous

/-- The local homomorphism `𝒪_{X, x₀} ⟶ R` of a morphism `φ : Spec R ⟶ X`, followed by
`R ⟶ K`, factors through the residue field of the image of the generic point. -/
lemma stalkClosedPointTo_comp_algebraMap (φ : Spec (CommRingCat.of R) ⟶ X) :
    Scheme.stalkClosedPointTo φ ≫ CommRingCat.ofHom (algebraMap R K) =
      X.presheaf.stalkSpecializes (valuationSpec_specializes (K := K) φ) ≫ X.residue _ ≫
        (Scheme.SpecToEquivOfField K X
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ φ)).2 := by
  rw [← specMap_fromSpecStalk_eq_iff, Spec.map_comp, Category.assoc,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact ((Scheme.SpecToEquivOfField K X).symm_apply_apply _).symm

/-- Hartshorne's data of a morphism `Spec R ⟶ X`. -/
noncomputable def toValuationSpecData [IsFractionRing R K] (φ : Spec (CommRingCat.of R) ⟶ X) :
    ValuationSpecData R K X where
  generic := Scheme.SpecToEquivOfField K X (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ φ)
  closed := φ (closedPoint R)
  specializes := valuationSpec_specializes φ
  dominates := (valuationSpec_dominates_iff _ _).mpr
    ⟨Scheme.stalkClosedPointTo φ, inferInstance, stalkClosedPointTo_comp_algebraMap φ⟩

/-- The local homomorphism `𝒪_{X, x₀} ⟶ R` determined by Hartshorne's data. -/
noncomputable def ValuationSpecData.stalkHom [IsFractionRing R K] (d : ValuationSpecData R K X) :
    X.presheaf.stalk d.closed ⟶ CommRingCat.of R :=
  ((valuationSpec_dominates_iff d.specializes d.generic.2).mp d.dominates).choose

instance ValuationSpecData.isLocalHom_stalkHom [IsFractionRing R K]
    (d : ValuationSpecData R K X) : IsLocalHom d.stalkHom.hom :=
  ((valuationSpec_dominates_iff d.specializes d.generic.2).mp d.dominates).choose_spec.1

lemma ValuationSpecData.stalkHom_comp [IsFractionRing R K] (d : ValuationSpecData R K X) :
    d.stalkHom ≫ CommRingCat.ofHom (algebraMap R K) =
      X.presheaf.stalkSpecializes d.specializes ≫ X.residue _ ≫ d.generic.2 :=
  ((valuationSpec_dominates_iff d.specializes d.generic.2).mp d.dominates).choose_spec.2

variable (R K X) in
/-- **Hartshorne II, Lemma 4.4.** For a valuation ring `R` with fraction field `K`, morphisms
`Spec R ⟶ X` correspond to the data of a point `x₁ : X` with an embedding `κ(x₁) ⟶ K` and a
specialization `x₁ ⤳ x₀` such that `R` dominates the image in `K` of the local ring of `x₀` on
the reduced closed subscheme `closure {x₁}`. -/
noncomputable def valuationSpecEquiv [IsFractionRing R K] :
    (Spec (CommRingCat.of R) ⟶ X) ≃ ValuationSpecData R K X where
  toFun := toValuationSpecData
  invFun d := Spec.map d.stalkHom ≫ X.fromSpecStalk d.closed
  left_inv φ := by
    have hmono : Mono (CommRingCat.ofHom (algebraMap R K)) :=
      ConcreteCategory.mono_of_injective _ (IsFractionRing.injective R K)
    have : (toValuationSpecData (K := K) φ).stalkHom = Scheme.stalkClosedPointTo φ := by
      apply (cancel_mono (CommRingCat.ofHom (algebraMap R K))).mp
      exact (ValuationSpecData.stalkHom_comp _).trans (stalkClosedPointTo_comp_algebraMap φ).symm
    change Spec.map (toValuationSpecData (K := K) φ).stalkHom ≫
      X.fromSpecStalk (φ (closedPoint R)) = φ
    rw [this]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk φ
  right_inv d := by
    apply ValuationSpecData.ext
    · change Scheme.SpecToEquivOfField K X (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
        Spec.map d.stalkHom ≫ X.fromSpecStalk d.closed) = d.generic
      rw [← Category.assoc, ← Spec.map_comp, ValuationSpecData.stalkHom_comp,
        (specMap_fromSpecStalk_eq_iff d.specializes _ _).mpr rfl]
      exact (Scheme.SpecToEquivOfField K X).apply_symm_apply d.generic
    · show X.fromSpecStalk d.closed (Spec.map d.stalkHom (closedPoint (CommRingCat.of R))) =
        d.closed
      rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

variable (R K X) in
/-- **Hartshorne II, Lemma 4.4**, as a bijection: sending a morphism `Spec R ⟶ X` to the image
`x₁` of the generic point with its embedding `κ(x₁) ⟶ K` and the image `x₀` of the closed point
is a bijection onto the data satisfying the domination condition. -/
theorem bijective_toValuationSpecData [IsFractionRing R K] :
    Function.Bijective (toValuationSpecData : (Spec (CommRingCat.of R) ⟶ X) →
      ValuationSpecData R K X) :=
  (valuationSpecEquiv R K X).bijective

end Hartshorne
