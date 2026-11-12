/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceSectionRing
import Hartshorne.Scheme.ProjClosedSubschemeTruncation
import Hartshorne.Scheme.AbsoluteNormalizationUniversal
import Hartshorne.Scheme.ProjectiveSpaceClassGroup

/-!
# The projective section ring is the integral closure

Hartshorne, *Algebraic Geometry*, II, Exercise 5.14(a) (p. 126).

Work in progress.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open GradedGlobalSections MonoidalCategory ProjGradedModuleSheaf

namespace ProjectiveSectionRing

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

section Fraction

variable [IsDomain A]

omit [IsDomain A] in
variable {𝒜} in
theorem ne_zero_of_mem_primeCompl {x : Proj 𝒜} {s : A}
    (hs : s ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) : s ≠ 0 := by
  rintro rfl
  exact hs (zero_mem _)

omit [IsDomain A] in
variable {𝒜} in
theorem algebraMap_ne_zero_of_mem_primeCompl {x : Proj 𝒜} {s : A}
    (hs : s ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    algebraMap A (FractionRing A) s ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2
    (ne_zero_of_mem_primeCompl hs)

variable {𝒜} in
/-- The image in the fraction field `K` of `A` of an element of the localization `A_x` at a
point `x` of `Proj A`: `a / s ↦ a / s`. -/
def toFraction (x : Proj 𝒜) (m : LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl A) :
    FractionRing A :=
  m.liftOn (fun p => algebraMap A (FractionRing A) p.1 / algebraMap A (FractionRing A) p.2) (by
    rintro ⟨a, s⟩ ⟨b, t⟩ ⟨w, hw⟩
    have hs := algebraMap_ne_zero_of_mem_primeCompl s.2
    have ht := algebraMap_ne_zero_of_mem_primeCompl t.2
    have hw' := algebraMap_ne_zero_of_mem_primeCompl w.2
    simp only [Submonoid.smul_def, smul_eq_mul] at hw
    have h := congrArg (algebraMap A (FractionRing A)) hw
    simp only [map_mul] at h
    change algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) s =
      algebraMap A (FractionRing A) b / algebraMap A (FractionRing A) t
    rw [div_eq_div_iff hs ht]
    have := mul_left_cancel₀ hw' h
    linear_combination this)

variable {𝒜} in
@[simp]
theorem toFraction_mk (x : Proj 𝒜) (a : A) (s : x.asHomogeneousIdeal.toIdeal.primeCompl) :
    toFraction x (LocalizedModule.mk a s) =
      algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) s :=
  LocalizedModule.liftOn_mk _ _ _

variable {𝒜} in
@[simp]
theorem toFraction_zero (x : Proj 𝒜) : toFraction x 0 = 0 := by
  rw [← LocalizedModule.zero_mk 1, toFraction_mk, map_zero, zero_div]

variable {𝒜} in
theorem toFraction_add (x : Proj 𝒜) (m m' : LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl A) :
    toFraction x (m + m') = toFraction x m + toFraction x m' := by
  induction m using LocalizedModule.induction_on with | h a s =>
  induction m' using LocalizedModule.induction_on with | h b t =>
  have hs := algebraMap_ne_zero_of_mem_primeCompl s.2
  have ht := algebraMap_ne_zero_of_mem_primeCompl t.2
  rw [LocalizedModule.mk_add_mk, toFraction_mk, toFraction_mk, toFraction_mk]
  simp only [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul, map_add, map_mul]
  field_simp

variable {𝒜} in
theorem toFraction_injective (x : Proj 𝒜) : Function.Injective (toFraction x) := by
  intro m m' h
  induction m using LocalizedModule.induction_on with | h a s =>
  induction m' using LocalizedModule.induction_on with | h b t =>
  have hs := algebraMap_ne_zero_of_mem_primeCompl s.2
  have ht := algebraMap_ne_zero_of_mem_primeCompl t.2
  rw [toFraction_mk, toFraction_mk, div_eq_div_iff hs ht] at h
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_eq_mul]
  apply IsFractionRing.injective A (FractionRing A)
  simp only [map_mul]
  linear_combination h

variable {𝒜} in
theorem toFraction_eq_zero_iff (x : Proj 𝒜)
    (m : LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl A) :
    toFraction x m = 0 ↔ m = 0 :=
  ⟨fun h => toFraction_injective x (h.trans (toFraction_zero x).symm),
    fun h => h ▸ toFraction_zero x⟩

variable {𝒜} in
theorem toFraction_mk_smul (x : Proj 𝒜) (a : A) (s : x.asHomogeneousIdeal.toIdeal.primeCompl)
    (m : LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl A) :
    toFraction x (Localization.mk a s • m) =
      algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) s * toFraction x m := by
  induction m using LocalizedModule.induction_on with | h b t =>
  rw [LocalizedModule.mk_smul_mk, toFraction_mk, toFraction_mk]
  simp only [smul_eq_mul, Submonoid.coe_mul, map_mul]
  rw [div_mul_div_comm]

/-! ### The generic point -/

variable {𝒜} in
/-- The generic point of `Proj A` for a graded domain `A` with `A₊ ≠ 0`: the homogeneous prime
`(0)`. -/
def genericPoint (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) : Proj 𝒜 :=
  (⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot, h⟩ : ProjectiveSpectrum 𝒜)

variable {𝒜} in
theorem genericPoint_mem {h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥}
    {V : Opens (ProjectiveSpectrum.top 𝒜)} {x : ProjectiveSpectrum 𝒜} (hx : x ∈ V) :
    (show ProjectiveSpectrum 𝒜 from genericPoint h) ∈ V := by
  let η : ProjectiveSpectrum 𝒜 := genericPoint h
  have hcl : x ∈ closure ({η} : Set (ProjectiveSpectrum 𝒜)) :=
    (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := 𝒜) η x).1
      (show (⊥ : HomogeneousIdeal 𝒜) ≤ _ from bot_le)
  obtain ⟨y, hyV, hy⟩ := mem_closure_iff.1 hcl (show Set (ProjectiveSpectrum 𝒜) from V.1) V.2 hx
  rw [Set.mem_singleton_iff.1 hy] at hyV
  exact hyV

/-! ### Values of sections of `𝒪(n)` in the fraction field -/

variable {𝒜} in
/-- The value of a global section of `𝒪_X(n)` at `x`, as an element of the fraction field. -/
def sectionValue (n : ℤ) (g : (projTwistingSheaf 𝒜 n).val.obj (op ⊤)) (x : Proj 𝒜) :
    FractionRing A :=
  toFraction x (globalValue 𝒜 (gradedTwist 𝒜 n) g x).val

variable {𝒜} in
/-- **All values of a global section of `𝒪_X(n)` agree in the fraction field**: near every
point the section is one fraction `a / f`, and that neighbourhood contains the generic point. -/
theorem sectionValue_eq_genericPoint (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) (n : ℤ)
    (g : (projTwistingSheaf 𝒜 n).val.obj (op ⊤)) (x : Proj 𝒜) :
    sectionValue n g x = sectionValue n g (genericPoint h) := by
  let g' : (sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj (op ⊤) := g
  obtain ⟨V, hxV, i, d, m, hm, f, hf, f_nin, w⟩ := g'.2 ⟨x, trivial⟩
  have hηV : genericPoint h ∈ V := genericPoint_mem hxV
  have e1 := congrArg HomogeneousLocalizedModule.val (w ⟨x, hxV⟩)
  have e2 := congrArg HomogeneousLocalizedModule.val (w ⟨genericPoint h, hηV⟩)
  unfold sectionValue
  change toFraction x (g'.1 (i ⟨x, hxV⟩)).val =
    toFraction (genericPoint h) (g'.1 (i ⟨genericPoint h, hηV⟩)).val
  rw [e1, e2]
  simp only [HomogeneousLocalizedModule.val_mk, toFraction_mk]

variable {𝒜} in
theorem sectionValue_add (n : ℤ) (g g' : (projTwistingSheaf 𝒜 n).val.obj (op ⊤))
    (x : Proj 𝒜) : sectionValue n (g + g') x = sectionValue n g x + sectionValue n g' x :=
  toFraction_add x _ _

variable {𝒜} in
theorem sectionValue_zero (n : ℤ) (x : Proj 𝒜) :
    sectionValue n (0 : (projTwistingSheaf 𝒜 n).val.obj (op ⊤)) x = 0 :=
  toFraction_zero x

variable {𝒜} in
theorem eq_zero_of_sectionValue_eq_zero (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) {n : ℤ}
    {g : (projTwistingSheaf 𝒜 n).val.obj (op ⊤)} (hg : sectionValue n g (genericPoint h) = 0) :
    g = 0 := by
  apply globalValue_injective 𝒜 (gradedTwist 𝒜 n)
  funext x
  apply HomogeneousLocalizedModule.ext
  have := (sectionValue_eq_genericPoint h n g x).trans hg
  exact (toFraction_eq_zero_iff x _).1 this

/-! ### The map `S' → K` -/

open Ringed

attribute [local instance] Classical.propDecidable

variable {𝒜} in
/-- The left unitor on global sections, `Γ(X, 𝒪_X ⊗ 𝒪_X(n)) → Γ(X, 𝒪_X(n))`. -/
def unitorGlobal (n : ℤ) (t : twistGlobal (𝟙_ (Proj 𝒜).Modules) n) :
    (projTwistingSheaf 𝒜 n).val.obj (op ⊤) :=
  (λ_ (projTwistingSheaf 𝒜 n)).hom.val.app (op ⊤) t

omit [IsDomain A] in
variable {𝒜} in
theorem unitorGlobal_bijective (n : ℤ) : Function.Bijective (unitorGlobal (𝒜 := 𝒜) n) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun z => (λ_ (projTwistingSheaf 𝒜 n)).inv.val.app (op ⊤) z, fun y => ?_, fun z => ?_⟩
  · change ((λ_ (projTwistingSheaf 𝒜 n)).hom ≫ (λ_ _).inv).val.app (op ⊤) y = y
    rw [Iso.hom_inv_id]
    rfl
  · change ((λ_ (projTwistingSheaf 𝒜 n)).inv ≫ (λ_ _).hom).val.app (op ⊤) z = z
    rw [Iso.inv_hom_id]
    rfl

omit [IsDomain A] in
variable {𝒜} in
theorem unitorGlobal_add (n : ℤ) (y y' : twistGlobal (𝟙_ (Proj 𝒜).Modules) n) :
    unitorGlobal n (y + y') = unitorGlobal n y + unitorGlobal n y' :=
  map_add _ _ _

omit [IsDomain A] in
variable {𝒜} in
theorem unitorGlobal_zero (n : ℤ) :
    unitorGlobal n (0 : twistGlobal (𝟙_ (Proj 𝒜).Modules) n) = 0 :=
  map_zero _

/-- The image of a global section of `𝒪_X(n)` in the fraction field `K` of `S`: its value at the
generic point (zero in the degenerate case `S₊ = 0`, where `Proj S` is empty). -/
def sectionToFraction (n : ℤ) : twistGlobal (𝟙_ (Proj 𝒜).Modules) n →+ FractionRing A where
  toFun t := if h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥ then
    sectionValue n (unitorGlobal n t) (genericPoint h) else 0
  map_zero' := by
    split_ifs
    · rfl
    · rw [unitorGlobal_zero, sectionValue_zero]
  map_add' y y' := by
    split_ifs
    · rw [add_zero]
    · rw [unitorGlobal_add, sectionValue_add]

variable {𝒜} in
theorem sectionToFraction_apply (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) (n : ℤ)
    (t : twistGlobal (𝟙_ (Proj 𝒜).Modules) n) (x : Proj 𝒜) :
    sectionToFraction 𝒜 n t = sectionValue n (unitorGlobal n t) x := by
  change (if h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥ then
    sectionValue n (unitorGlobal n t) (genericPoint h) else 0) = _
  rw [dif_pos h, sectionValue_eq_genericPoint h n _ x]

variable {𝒜} in
theorem sectionToFraction_injective (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) (n : ℤ) :
    Function.Injective (sectionToFraction 𝒜 n) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  rw [sectionToFraction_apply h n t (genericPoint h)] at ht
  apply (unitorGlobal_bijective n).1
  rw [unitorGlobal_zero]
  exact eq_zero_of_sectionValue_eq_zero h ht

/-- **The map `S' = ⨁_{n ≥ 0} Γ(X, 𝒪_X(n)) → K`**, sum of the maps `sectionToFraction`. -/
def sectionRingToFraction :
    (DirectSum ℕ fun n => twistGlobal (𝟙_ (Proj 𝒜).Modules) (n : ℤ)) →+ FractionRing A :=
  DirectSum.toAddMonoid fun n => sectionToFraction 𝒜 n

theorem sectionRingToFraction_of (n : ℕ) (t : twistGlobal (𝟙_ (Proj 𝒜).Modules) (n : ℤ)) :
    sectionRingToFraction 𝒜 (DirectSum.of _ n t) = sectionToFraction 𝒜 n t :=
  DirectSum.toAddMonoid_of _ _ _

/-- **The product on `Γ_*(𝒪_X)`**, degreewise, through the unitors and the multiplication
`𝒪_X(n) ⊗ 𝒪_X(m) → 𝒪_X(n + m)`. -/
def sectionMul (n m : ℤ) (y : twistGlobal (𝟙_ (Proj 𝒜).Modules) n)
    (z : twistGlobal (𝟙_ (Proj 𝒜).Modules) m) : twistGlobal (𝟙_ (Proj 𝒜).Modules) (n + m) :=
  (λ_ (projTwistingSheaf 𝒜 (n + m))).inv.val.app (op ⊤)
    ((twistMulHom 𝒜 n m).val.app (op ⊤) (tmulSection _ _ (unitorGlobal n y) (unitorGlobal m z)))

variable {𝒜} in
theorem toFraction_localization_smul (x : Proj 𝒜)
    (c m : LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl A) :
    toFraction x ((show Localization x.asHomogeneousIdeal.toIdeal.primeCompl from c) • m) =
      toFraction x c * toFraction x m := by
  induction c using LocalizedModule.induction_on with | h a s =>
  rw [toFraction_mk]
  exact toFraction_mk_smul x a s m

variable {𝒜} in
/-- **The map to `K` is multiplicative.** -/
theorem sectionToFraction_sectionMul (n m : ℤ) (y : twistGlobal (𝟙_ (Proj 𝒜).Modules) n)
    (z : twistGlobal (𝟙_ (Proj 𝒜).Modules) m) :
    sectionToFraction 𝒜 (n + m) (sectionMul 𝒜 n m y z) =
      sectionToFraction 𝒜 n y * sectionToFraction 𝒜 m z := by
  by_cases h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥
  · let η := genericPoint h
    rw [sectionToFraction_apply h _ _ η, sectionToFraction_apply h _ _ η,
      sectionToFraction_apply h _ _ η]
    have e : unitorGlobal (n + m) (sectionMul 𝒜 n m y z) =
        (twistMulHom 𝒜 n m).val.app (op ⊤)
          (tmulSection _ _ (unitorGlobal n y) (unitorGlobal m z)) := by
      change ((λ_ (projTwistingSheaf 𝒜 (n + m))).inv ≫ (λ_ _).hom).val.app (op ⊤) _ = _
      rw [Iso.inv_hom_id]
      rfl
    unfold sectionValue
    rw [e]
    change toFraction η (((twistMulHom 𝒜 n m).val.app (op ⊤)
      (tmulSection _ _ (unitorGlobal n y) (unitorGlobal m z)) :
        (sheafInType 𝒜 (gradedTwist 𝒜 (n + m))).1.obj (op ⊤)).1 ⟨η, trivial⟩).val = _
    rw [twistMulHom_tmulSection, toFraction_localization_smul, mul_comm]
    rfl
  · change (if h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥ then _ else 0) =
      (if h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥ then _ else 0) *
        (if h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥ then _ else 0)
    rw [dif_neg h, dif_neg h, dif_neg h, zero_mul]

/-- The global section `1 ⊗ 1` of `𝒪_X ⊗ 𝒪_X(0)`, the unit of `Γ_*(𝒪_X)`. -/
def unitSection : twistGlobal (𝟙_ (Proj 𝒜).Modules) 0 :=
  tmulSection _ _ (oneSec (op ⊤)) (twistSection 0 ⟨1, SetLike.GradedOne.one_mem⟩ (op ⊤))

omit [IsDomain A] in
variable {𝒜} in
/-- `s · 1 = s / 1` on values, for `s ∈ S_d`. -/
theorem globalValue_mulGlobal_unitSection {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (x : Proj 𝒜) :
    (globalValue 𝒜 (gradedTwist 𝒜 (0 + d))
      (unitorGlobal (0 + d) (mulGlobal (𝟙_ (Proj 𝒜).Modules) 0 d ⟨s, hs⟩ (unitSection 𝒜))) x).val =
      LocalizedModule.mk s 1 := by
  let h := (twistMulHom 𝒜 0 d).val.app (op ⊤) (tmulSection _ _
    (twistSection 0 ⟨1, SetLike.GradedOne.one_mem⟩ (op ⊤)) (twistSection d ⟨s, hs⟩ (op ⊤)))
  have e0 : mulGlobal (𝟙_ (Proj 𝒜).Modules) 0 d ⟨s, hs⟩ (unitSection 𝒜) =
      tmulSection _ _ (oneSec (op ⊤)) h :=
    mulMap_tmulSection _ 0 d ⟨s, hs⟩ (oneSec (op ⊤)) _
  have e1 := Ringed.leftUnitor_hom_tmulSection (projTwistingSheaf 𝒜 (0 + d)) (U := op ⊤)
    (1 : (Proj 𝒜).ringCatSheaf.obj.obj (op ⊤)) h
  refine (congrArg (fun t => (globalValue 𝒜 (gradedTwist 𝒜 (0 + d)) (unitorGlobal (0 + d) t) x).val)
    e0).trans ?_
  refine (congrArg (fun g => (globalValue 𝒜 (gradedTwist 𝒜 (0 + d)) g x).val)
    (e1.trans (one_smul ((Proj 𝒜).ringCatSheaf.obj.obj (op ⊤)) h))).trans ?_
  refine (twistMulHom_tmul_twistSection_apply (𝒜 := 𝒜) 0 d ⟨s, hs⟩
    (twistSection 0 ⟨1, SetLike.GradedOne.one_mem⟩ (op ⊤)) ⟨x, trivial⟩).trans ?_
  change s • LocalizedModule.mk (1 : A) 1 = _
  rw [LocalizedModule.smul'_mk, smul_eq_mul, mul_one]

variable {𝒜} in
/-- **The map `S → S' → K` is the inclusion `S ⊆ K`**: the section `s · 1` of `𝒪_X(d)` goes to
`s`. -/
theorem sectionToFraction_mulGlobal_unitSection (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥)
    {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    sectionToFraction 𝒜 (0 + d) (mulGlobal (𝟙_ (Proj 𝒜).Modules) 0 d ⟨s, hs⟩ (unitSection 𝒜)) =
      algebraMap A (FractionRing A) s := by
  rw [sectionToFraction_apply h _ _ (genericPoint h)]
  unfold sectionValue
  rw [globalValue_mulGlobal_unitSection hs, toFraction_mk]
  simp

/-! ### Homogeneous fractions and the directness of degrees -/

variable {𝒜} in
/-- `z ∈ K` is a homogeneous fraction of degree `n`: `z = a / s` with `s ≠ 0` homogeneous of some
degree `e` and `a` homogeneous of degree `e + n`. -/
def IsHomFrac (n : ℕ) (z : FractionRing A) : Prop :=
  ∃ (e : ℕ) (a s : A), a ∈ 𝒜 (e + n) ∧ s ∈ 𝒜 e ∧ s ≠ 0 ∧
    z = algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) s

variable {𝒜} in
/-- **Homogeneous fractions of distinct degrees are independent**: a finite sum of homogeneous
fractions of pairwise distinct degrees vanishes only if every term does. -/
theorem eq_zero_of_sum_isHomFrac_eq_zero (F : Finset ℕ) (z : ℕ → FractionRing A)
    (hz : ∀ n ∈ F, IsHomFrac (𝒜 := 𝒜) n (z n)) (hsum : ∑ n ∈ F, z n = 0) :
    ∀ n ∈ F, z n = 0 := by
  classical
  choose! e a s ha hs hs0 hzas using hz
  set D := ∏ m ∈ F, s m with hD
  set E := ∑ m ∈ F, e m with hE
  have hD0 : algebraMap A (FractionRing A) D ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A)), hD]
    exact Finset.prod_ne_zero_iff.2 hs0
  let b : ℕ → A := fun n => a n * ∏ m ∈ F.erase n, s m
  have hb : ∀ n ∈ F, b n ∈ 𝒜 (E + n) := by
    intro n hn
    have h1 := SetLike.mul_mem_graded (ha n hn)
      (SetLike.prod_mem_graded 𝒜 e s (F := F.erase n) fun m hm => hs m (Finset.mem_of_mem_erase hm))
    have : e n + n + ∑ m ∈ F.erase n, e m = E + n := by
      rw [hE, ← Finset.add_sum_erase F e hn]
      ring
    rwa [this] at h1
  have hzb : ∀ n ∈ F, z n * algebraMap A (FractionRing A) D = algebraMap A (FractionRing A) (b n) := by
    intro n hn
    have hsn := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 (hs0 n hn)
    rw [hzas n hn, hD, ← Finset.mul_prod_erase F s hn]
    simp only [b, map_mul]
    field_simp
  have hbsum : ∑ n ∈ F, b n = 0 := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_sum, map_zero, ← Finset.sum_congr rfl hzb, ← Finset.sum_mul, hsum, zero_mul]
  intro n0 hn0
  have key : (DirectSum.decompose 𝒜 (∑ n ∈ F, b n) (E + n0) : A) = b n0 := by
    rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_eq_single n0]
    · exact DirectSum.decompose_of_mem_same 𝒜 (hb n0 hn0)
    · intro m hm hmn
      exact DirectSum.decompose_of_mem_ne 𝒜 (hb m hm) (by omega)
    · intro h
      exact absurd hn0 h
  rw [hbsum, DirectSum.decompose_zero] at key
  have hb0 : b n0 = 0 := by rw [← key]; rfl
  have := hzb n0 hn0
  rw [hb0, map_zero] at this
  exact (mul_eq_zero.1 this).resolve_right hD0

variable {𝒜} in
theorem isHomFrac_sectionToFraction (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) (n : ℕ)
    (t : twistGlobal (𝟙_ (Proj 𝒜).Modules) (n : ℤ)) :
    IsHomFrac (𝒜 := 𝒜) n (sectionToFraction 𝒜 n t) := by
  rw [sectionToFraction_apply h _ _ (genericPoint h)]
  unfold sectionValue
  obtain ⟨d, m, hm, f, hf, hfx, he⟩ := HomogeneousLocalizedModule.mk_surjective
    (globalValue 𝒜 (gradedTwist 𝒜 n) (unitorGlobal (n : ℤ) t) (genericPoint h))
  rw [he, HomogeneousLocalizedModule.val_mk, toFraction_mk]
  refine ⟨d, m, f, ?_, hf, ?_, rfl⟩
  · have := hm.1
    rwa [show ((n : ℤ) + ((d : ℕ) : ℤ)).toNat = d + n by omega] at this
  · intro h0
    exact hfx (h0 ▸ zero_mem _)

variable {𝒜} in
/-- **`S' → K` is injective.** -/
theorem sectionRingToFraction_injective (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) :
    Function.Injective (sectionRingToFraction 𝒜) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hsum : sectionRingToFraction 𝒜 y =
      ∑ n ∈ y.support, sectionToFraction 𝒜 n (y n) := by
    conv_lhs => rw [← DirectSum.sum_support_of y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ => DirectSum.toAddMonoid_of _ _ _
  rw [hsum] at hy
  have h0 := eq_zero_of_sum_isHomFrac_eq_zero y.support (fun n => sectionToFraction 𝒜 n (y n))
    (fun n _ => isHomFrac_sectionToFraction h n (y n)) hy
  ext n
  by_cases hn : n ∈ y.support
  · exact sectionToFraction_injective h n ((h0 n hn).trans (map_zero _).symm)
  · simpa using hn

omit [IsDomain A] in
variable {𝒜} in
theorem not_irrelevant_le_bot_of_mem_one {f : A} (f_deg : f ∈ 𝒜 1) (hf : f ≠ 0) :
    ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥ := by
  intro h
  have hmem : f ∈ HomogeneousIdeal.irrelevant 𝒜 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne 𝒜 f_deg (by omega)]
  have h0 : f ∈ (⊥ : HomogeneousIdeal 𝒜).toIdeal := h hmem
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h0
  exact hf h0

variable {𝒜} in
/-- **One chart.** On `D₊(f)` with `f ∈ S₁` nonzero, a global section of `𝒪_X(n)` is a single
fraction `a / f^j` with `a ∈ S_{j + n}`; so `f^j` times its image in `K` lies in `S_{j + n}`. -/
theorem exists_mem_eq_pow_mul_sectionToFraction {f : A} (f_deg : f ∈ 𝒜 1) (hf : f ≠ 0) (n : ℕ)
    (t : twistGlobal (𝟙_ (Proj 𝒜).Modules) (n : ℤ)) :
    ∃ (j : ℕ) (a : A), a ∈ 𝒜 (j + n) ∧ algebraMap A (FractionRing A) a =
      algebraMap A (FractionRing A) f ^ j * sectionToFraction 𝒜 n t := by
  have h := not_irrelevant_le_bot_of_mem_one f_deg hf
  obtain ⟨m, hm⟩ := exists_globalValue_eq_mapOfLE 𝒜 (gradedTwist 𝒜 n) f_deg one_pos
    (unitorGlobal (n : ℤ) t)
  have hη : genericPoint h ∈ Proj.basicOpen 𝒜 f := by
    rw [Proj.mem_basicOpen]
    intro hmem
    have h0 : f ∈ (⊥ : HomogeneousIdeal 𝒜).toIdeal := hmem
    rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h0
    exact hf h0
  obtain ⟨d, a, ha, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective m
  obtain ⟨j, rfl⟩ := hsx
  have hfj : f ^ j ≠ 0 := pow_ne_zero j hf
  have hdj : d = j := DirectSum.degree_eq_of_mem_mem 𝒜 hs
    (by simpa using SetLike.pow_mem_graded j f_deg) hfj
  subst hdj
  refine ⟨d, a, ?_, ?_⟩
  · have := ha.1
    rwa [show ((n : ℤ) + ((d : ℕ) : ℤ)).toNat = d + n by omega] at this
  · rw [sectionToFraction_apply h _ _ (genericPoint h)]
    unfold sectionValue
    rw [hm _ hη, HomogeneousLocalizedModule.mapOfLE_mk, HomogeneousLocalizedModule.val_mk,
      toFraction_mk]
    have := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hfj
    simp only [map_pow] at this ⊢
    field_simp

variable {𝒜} in
/-- **Gluing a section of `𝒪_X(n)` from charts.** Let `fᵢ ∈ S₁` be such that the `D₊(fᵢ)` cover
`Proj S`. If `z ∈ K` is, on every chart, a fraction `a / fᵢ^{j}` with `a ∈ S_{j + n}`, then `z` is
the image of a global section of `𝒪_X(n)`. -/
theorem exists_sectionToFraction_eq {ι : Type*} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1)
    (hcover : ∀ x : Proj 𝒜, ∃ i, f i ∉ x.asHomogeneousIdeal)
    (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) (n : ℕ) (z : FractionRing A)
    (hz : ∀ i, f i ≠ 0 → ∃ (j : ℕ) (a : A), a ∈ 𝒜 (j + n) ∧
      algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) (f i) ^ j * z) :
    ∃ t : twistGlobal (𝟙_ (Proj 𝒜).Modules) (n : ℤ), sectionToFraction 𝒜 n t = z := by
  classical
  choose ix hix using hcover
  have hne : ∀ x : Proj 𝒜, f (ix x) ≠ 0 := fun x h0 => hix x (h0 ▸ zero_mem _)
  choose jx ax hax hzx using fun x => hz _ (hne x)
  have hmem : ∀ x : Proj 𝒜, ax x ∈ gradedTwist 𝒜 (n : ℤ) (jx x : ℕ) := fun x =>
    (mem_gradedTwist_of_eq (by push_cast; ring)).2 (hax x)
  have hpow : ∀ x : Proj 𝒜, f (ix x) ^ jx x ∈ 𝒜 (jx x) := fun x =>
    by simpa using SetLike.pow_mem_graded (jx x) (hf (ix x))
  have hnot : ∀ (x y : Proj 𝒜), f (ix x) ∉ y.asHomogeneousIdeal →
      f (ix x) ^ jx x ∈ y.asHomogeneousIdeal.toIdeal.primeCompl := fun x y hy hp =>
    hy (y.isPrime.mem_of_pow_mem _ hp)
  have hfrac : ∀ (x y : Proj 𝒜) (hy : f (ix x) ∉ y.asHomogeneousIdeal),
      toFraction y (HomogeneousLocalizedModule.mk (jx x) (ax x) (hmem x) (f (ix x) ^ jx x)
        (hpow x) (hnot x y hy)).val = z := by
    intro x y hy
    rw [HomogeneousLocalizedModule.val_mk, toFraction_mk]
    have h0 := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2
      (pow_ne_zero (jx x) (hne x))
    rw [div_eq_iff h0, hzx x, map_pow, mul_comm]
  let val : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒜)),
      HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 n) x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    fun x => HomogeneousLocalizedModule.mk (jx x.1) (ax x.1) (hmem x.1) (f (ix x.1) ^ jx x.1)
      (hpow x.1) (hnot x.1 x.1 (hix x.1))
  have hval : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒜)), toFraction x.1 (val x).val = z :=
    fun x => hfrac x.1 x.1 (hix x.1)
  let g : (sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj (op ⊤) := ⟨val, fun x =>
    ⟨ProjectiveSpectrum.basicOpen 𝒜 (f (ix x.1)), hix x.1, homOfLE le_top, jx x.1, ax x.1,
      hmem x.1, f (ix x.1) ^ jx x.1, hpow x.1, fun y => hnot x.1 y.1 y.2, fun y =>
        HomogeneousLocalizedModule.val_injective (toFraction_injective y.1
          ((hval ⟨y.1, trivial⟩).trans (hfrac x.1 y.1 y.2).symm))⟩⟩
  obtain ⟨t, ht⟩ := (unitorGlobal_bijective (𝒜 := 𝒜) (n : ℤ)).2 g
  refine ⟨t, ?_⟩
  rw [sectionToFraction_apply h _ _ (genericPoint h)]
  unfold sectionValue
  rw [ht]
  exact hval ⟨genericPoint h, trivial⟩

/-! ### The chart rings `S_(f)` and `S_(f)[f]` inside `K` -/

variable {𝒜} in
theorem powers_le_nonZeroDivisors {f : A} (hf : f ≠ 0) :
    Submonoid.powers f ≤ nonZeroDivisors A :=
  Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero hf)

variable {𝒜} in
/-- The degree-zero localization `S_(f)` inside the fraction field `K`. -/
def awayToFraction {f : A} (hf : f ≠ 0) : Away 𝒜 f →+* FractionRing A :=
  (Localization.mapToFractionRing (FractionRing A) (Submonoid.powers f) (Localization.Away f)
    (powers_le_nonZeroDivisors hf)).toRingHom.comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))

variable {𝒜} in
theorem awayToFraction_mk {f : A} (hf : f ≠ 0) (c : NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    awayToFraction hf (HomogeneousLocalization.mk c) =
      algebraMap A (FractionRing A) c.num / algebraMap A (FractionRing A) c.den := by
  simp only [awayToFraction, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Localization.mapToFractionRing_apply,
    Localization.mk_eq_mk', IsLocalization.lift_mk']
  rw [div_eq_mul_inv, Units.val_inv_eq_inv_val, IsUnit.coe_liftRight]
  rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
variable {𝒜} in
theorem den_ne_zero {f : A} (hf : f ≠ 0) (c : NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (c.den : A) ≠ 0 := by
  obtain ⟨m, hm⟩ := c.den_mem
  rw [← hm]
  exact pow_ne_zero m hf

variable {𝒜} in
theorem awayToFraction_injective {f : A} (hf : f ≠ 0) :
    Function.Injective (awayToFraction (𝒜 := 𝒜) hf) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective c
  rw [awayToFraction_mk, div_eq_zero_iff, map_eq_zero_iff _ (IsFractionRing.injective A _),
    map_eq_zero_iff _ (IsFractionRing.injective A _)] at hc
  rcases hc with hc | hc
  · apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero, hc, Localization.mk_zero]
  · exact absurd hc (den_ne_zero hf c)

variable {𝒜} in
theorem isHomFrac_awayToFraction_mul_pow {f : A} (hf : f ≠ 0) (f_deg : f ∈ 𝒜 1)
    (c : Away 𝒜 f) (n : ℕ) :
    IsHomFrac (𝒜 := 𝒜) n
      (awayToFraction hf c * algebraMap A (FractionRing A) f ^ n) := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective c
  refine ⟨c.deg, c.num * f ^ n, c.den, ?_, c.den.2, den_ne_zero hf c, ?_⟩
  · exact SetLike.mul_mem_graded c.num.2 (by simpa using SetLike.pow_mem_graded n f_deg)
  · rw [awayToFraction_mk, map_mul, map_pow, div_mul_eq_mul_div]

variable {𝒜} in
/-- A chart component `c · f^n` with `c ∈ S_(f)` is `a / f^j` with `a ∈ S_{j + n}`. -/
theorem exists_mem_eq_pow_mul_awayToFraction {f : A} (hf : f ≠ 0) (f_deg : f ∈ 𝒜 1)
    (c : Away 𝒜 f) (n : ℕ) :
    ∃ (j : ℕ) (a : A), a ∈ 𝒜 (j + n) ∧ algebraMap A (FractionRing A) a =
      algebraMap A (FractionRing A) f ^ j *
        (awayToFraction hf c * algebraMap A (FractionRing A) f ^ n) := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective c
  obtain ⟨m, hm⟩ := c.den_mem
  have hdeg : c.deg = m := DirectSum.degree_eq_of_mem_mem 𝒜 c.den.2
    (by rw [← hm]; simpa using SetLike.pow_mem_graded m f_deg) (den_ne_zero hf c)
  refine ⟨m, c.num * f ^ n, ?_, ?_⟩
  · rw [← hdeg]
    exact SetLike.mul_mem_graded c.num.2 (by simpa using SetLike.pow_mem_graded n f_deg)
  · have h0 := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2
      (pow_ne_zero m hf)
    rw [awayToFraction_mk, ← hm]
    simp only [map_mul, map_pow] at h0 ⊢
    field_simp

variable {𝒜} in
/-- The polynomial ring `S_(f)[T]` mapped to `K` by `T ↦ f`. -/
def chartPoly {f : A} (hf : f ≠ 0) : Polynomial (Away 𝒜 f) →+* FractionRing A :=
  Polynomial.eval₂RingHom (awayToFraction hf) (algebraMap A (FractionRing A) f)

variable {𝒜} in
theorem chartPoly_eq_sum {f : A} (hf : f ≠ 0) (p : Polynomial (Away 𝒜 f)) {N : ℕ}
    (hN : p.natDegree < N) :
    chartPoly hf p = ∑ n ∈ Finset.range N,
      awayToFraction hf (p.coeff n) * algebraMap A (FractionRing A) f ^ n :=
  Polynomial.eval₂_eq_sum_range' _ hN _

variable {𝒜} in
theorem chartPoly_injective {f : A} (hf : f ≠ 0) (f_deg : f ∈ 𝒜 1) :
    Function.Injective (chartPoly (𝒜 := 𝒜) hf) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [chartPoly_eq_sum hf p (Nat.lt_succ_self _)] at hp
  have h0 := eq_zero_of_sum_isHomFrac_eq_zero _ _
    (fun n _ => isHomFrac_awayToFraction_mul_pow hf f_deg (p.coeff n) n) hp
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_zero]
  by_cases hn : n < p.natDegree.succ
  · have := h0 n (Finset.mem_range.2 hn)
    have hfn := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2
      (pow_ne_zero n hf)
    rw [map_pow] at hfn
    exact awayToFraction_injective hf
      (((mul_eq_zero.1 this).resolve_right hfn).trans (map_zero _).symm)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega)

variable {𝒜} in
/-- `S ⊆ S_(f)[f]`: each `s_d ∈ S_d` is `(s_d / f^d) · f^d`. -/
theorem exists_chartPoly_eq_algebraMap {f : A} (hf : f ≠ 0) (f_deg : f ∈ 𝒜 1) (s : A) :
    ∃ p : Polynomial (Away 𝒜 f), chartPoly hf p = algebraMap A (FractionRing A) s := by
  classical
  have hfd : ∀ d : ℕ, f ^ d ∈ 𝒜 d := fun d => by simpa using SetLike.pow_mem_graded d f_deg
  let e : ℕ → Away 𝒜 f := fun d => HomogeneousLocalization.mk
    ⟨d, ⟨(DirectSum.decompose 𝒜 s d : A), (DirectSum.decompose 𝒜 s d).2⟩, ⟨f ^ d, hfd d⟩, ⟨d, rfl⟩⟩
  refine ⟨∑ d ∈ (DirectSum.decompose 𝒜 s).support, Polynomial.C (e d) * Polynomial.X ^ d, ?_⟩
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 s]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h0 := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2
    (pow_ne_zero d hf)
  rw [map_mul, map_pow, chartPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X, awayToFraction_mk]
  rw [map_pow] at h0
  change algebraMap A (FractionRing A) (DirectSum.decompose 𝒜 s d : A) /
    algebraMap A (FractionRing A) (f ^ d) * _ = _
  rw [map_pow]
  field_simp

variable {𝒜} in
/-- **One normal chart.** If `S_(f)` is integrally closed, every `z ∈ K` integral over `S` lies in
`S_(f)[f]`: that ring is a polynomial ring over `S_(f)`, hence integrally closed, contains `S`, and
has fraction field `K`. -/
theorem exists_chartPoly_eq_of_isIntegral {f : A} (hf : f ≠ 0) (f_deg : f ∈ 𝒜 1)
    [IsIntegrallyClosed (Away 𝒜 f)] {z : FractionRing A} (hz : IsIntegral A z) :
    ∃ p : Polynomial (Away 𝒜 f), chartPoly hf p = z := by
  have : IsDomain (Away 𝒜 f) := (awayToFraction_injective hf).isDomain (awayToFraction hf)
  let _ : Algebra (Polynomial (Away 𝒜 f)) (FractionRing A) := (chartPoly hf).toAlgebra
  have : FaithfulSMul (Polynomial (Away 𝒜 f)) (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (chartPoly_injective hf f_deg)
  have : IsFractionRing (Polynomial (Away 𝒜 f)) (FractionRing A) :=
    IsFractionRing.of_field (Polynomial (Away 𝒜 f)) (FractionRing A) fun w => by
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) w
      obtain ⟨p, hp⟩ := exists_chartPoly_eq_algebraMap hf f_deg a
      obtain ⟨q, hq⟩ := exists_chartPoly_eq_algebraMap hf f_deg b
      exact ⟨p, q, by rw [← hp, ← hq]; rfl⟩
  have hint : IsIntegral (Polynomial (Away 𝒜 f)) z := by
    obtain ⟨P, hPm, hPz⟩ := hz
    have hdeg : P.natDegree ≠ 0 := by
      intro h0
      rw [hPm.natDegree_eq_zero] at h0
      rw [h0, Polynomial.eval₂_one] at hPz
      exact one_ne_zero hPz
    refine IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := P.map (algebraMap A _))
      (hPm.map _) (by rwa [hPm.natDegree_map]) ?_ ?_
    · rw [Polynomial.eval_map, hPz]
      exact isIntegral_zero
    · intro i
      rw [Polynomial.coeff_map]
      obtain ⟨p, hp⟩ := exists_chartPoly_eq_algebraMap hf f_deg (P.coeff i)
      rw [← hp]
      exact isIntegral_algebraMap
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨p, hp⟩

variable {𝒜} in
theorem genericPoint_mem_basicOpen (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) {f : A}
    (hf : f ≠ 0) : genericPoint h ∈ Proj.basicOpen 𝒜 f := by
  rw [Proj.mem_basicOpen]
  intro hmem
  have h0 : f ∈ (⊥ : HomogeneousIdeal 𝒜).toIdeal := hmem
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h0
  exact hf h0

variable {𝒜} in
theorem IsHomFrac.sub {n : ℕ} {z w : FractionRing A} (hz : IsHomFrac (𝒜 := 𝒜) n z)
    (hw : IsHomFrac (𝒜 := 𝒜) n w) : IsHomFrac (𝒜 := 𝒜) n (z - w) := by
  obtain ⟨e, a, s, ha, hs, hs0, rfl⟩ := hz
  obtain ⟨e', b, t, hb, ht, ht0, rfl⟩ := hw
  refine ⟨e + e', a * t - b * s, s * t, sub_mem ?_ ?_, SetLike.mul_mem_graded hs ht,
    mul_ne_zero hs0 ht0, ?_⟩
  · have := SetLike.mul_mem_graded ha ht
    rwa [show e + n + e' = e + e' + n by ring] at this
  · have := SetLike.mul_mem_graded hb hs
    rwa [show e' + n + e = e + e' + n by ring] at this
  · have h1 := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hs0
    have h2 := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 ht0
    rw [map_sub, map_mul, map_mul, map_mul]
    field_simp

end Fraction

/-! ## Integrality of a connected normal scheme -/

section ConnectedNormal

variable (X : Scheme.{u})

/-- On a scheme whose local rings are domains, two irreducible components through a point
coincide: both contain the image of `Spec 𝒪_{X,x}`, which is irreducible. -/
theorem eq_of_mem_irreducibleComponents [∀ x : X, IsDomain (X.presheaf.stalk x)] {Z₁ Z₂ : Set X}
    (h₁ : Z₁ ∈ irreducibleComponents X) (h₂ : Z₂ ∈ irreducibleComponents X) {x : X}
    (hx₁ : x ∈ Z₁) (hx₂ : x ∈ Z₂) : Z₁ = Z₂ := by
  let T : Set X := Set.range (X.fromSpecStalk x)
  have hT : IsIrreducible T := by
    have := (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image (X.fromSpecStalk x)
      (X.fromSpecStalk x).continuous.continuousOn
    rwa [Set.image_univ] at this
  have key : ∀ {Z : Set X}, Z ∈ irreducibleComponents X → x ∈ Z → Z = closure T := by
    intro Z hZ hxZ
    have hη := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
    have hηT : hZ.1.genericPoint ∈ T := by
      change _ ∈ Set.range (X.fromSpecStalk x)
      rw [Scheme.range_fromSpecStalk]
      exact hη.specializes hxZ
    have hle : Z ⊆ closure T := by
      rw [← hη.def]
      exact closure_mono (Set.singleton_subset_iff.2 hηT)
    exact le_antisymm hle (hZ.2 hT.closure hle)
  exact (key h₁ hx₁).trans (key h₂ hx₂).symm

/-- **A connected Noetherian scheme whose local rings are domains is irreducible.** The
irreducible components are disjoint, finitely many and closed, hence open. -/
theorem irreducibleSpace_of_connectedSpace [TopologicalSpace.NoetherianSpace X] [ConnectedSpace X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] : IrreducibleSpace X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  set Z := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hcompl : Zᶜ = ⋃ W ∈ irreducibleComponents X \ {Z}, W := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      rintro he
      exact hy (he ▸ mem_irreducibleComponent)
    · rintro ⟨W, ⟨hW, hWZ⟩, hyW⟩ hyZ
      exact hWZ (eq_of_mem_irreducibleComponents X hW hZ hyW hyZ)
  have hopen : IsOpen Z := by
    rw [← isClosed_compl_iff, hcompl]
    exact ((TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).sdiff).isClosed_biUnion
      fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  have huniv : Z = Set.univ := IsClopen.eq_univ ⟨isClosed_irreducibleComponent, hopen⟩
    ⟨x, mem_irreducibleComponent⟩
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set X)
  rw [← huniv]
  exact isIrreducible_irreducibleComponent

/-- **A connected normal Noetherian scheme is integral** (the first step of the hint to
Exercise 5.14(a)). -/
theorem isIntegral_of_connectedSpace [TopologicalSpace.NoetherianSpace X] [ConnectedSpace X]
    [Hartshorne.IsNormal X] : IsIntegral X := by
  have := irreducibleSpace_of_connectedSpace X
  have : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end ConnectedNormal

/-! ## The graded ring of an integral `Proj` -/

section IntegralProj

variable {𝒜}

theorem isNilpotent_of_forall_mem {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (h : ∀ x : Proj 𝒜, f ∈ x.asHomogeneousIdeal) : IsNilpotent f := by
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  by_contra hfJ
  have hq := hJ.homogeneousCore (𝒜 := 𝒜)
  have hfq : f ∉ (J.homogeneousCore 𝒜).toIdeal := fun hf => hfJ (Ideal.toIdeal_homogeneousCore_le 𝒜 J hf)
  let x : ProjectiveSpectrum 𝒜 := ⟨J.homogeneousCore 𝒜, hq, fun hle => hfq (hle (by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne 𝒜 f_deg (by omega)]))⟩
  exact hfq (h x)

theorem away_mk_eq_zero_iff {f : A} (c : NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    HomogeneousLocalization.mk c = 0 ↔ ∃ m : ℕ, f ^ m * c.num = 0 := by
  rw [← (HomogeneousLocalization.val_injective _).eq_iff, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨_, m, rfl⟩, hm⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨f ^ m, m, rfl⟩, hm⟩

theorem isDomain_away_of_isIntegral [IsIntegral (Proj 𝒜)] {f : A} (f_deg : f ∈ 𝒜 1)
    {x : Proj 𝒜} (hx : f ∉ x.asHomogeneousIdeal) : IsDomain (Away 𝒜 f) := by
  have : Nonempty (Proj.basicOpen 𝒜 f) := ⟨⟨x, hx⟩⟩
  have e := (Proj.basicOpenIsoAway 𝒜 f f_deg one_pos).commRingCatIsoToRingEquiv
  exact e.injective.isDomain e.toRingHom

/-- **Homogeneous zero divisors on an integral `Proj`.** Let `fᵢ ∈ S₁` be such that the charts
`D₊(fᵢ)` cover `Proj S`. If `X = Proj S` is integral and `a ∈ S_p`, `b ∈ S_q` satisfy `ab = 0`,
then `a` or `b` is killed by a power of every `fᵢ`. -/
theorem forall_pow_mul_eq_zero_or [IsIntegral (Proj 𝒜)] {ι : Type*} (f : ι → A)
    (hf : ∀ i, f i ∈ 𝒜 1) {a b : A} {p q : ℕ} (ha : a ∈ 𝒜 p) (hb : b ∈ 𝒜 q) (hab : a * b = 0) :
    (∀ i, ∃ m : ℕ, f i ^ m * a = 0) ∨ (∀ i, ∃ m : ℕ, f i ^ m * b = 0) := by
  classical
  have hpow : ∀ i (d : ℕ), f i ^ d ∈ 𝒜 d := fun i d => by
    simpa using SetLike.pow_mem_graded d (hf i)
  let good : ι → Prop := fun i => ∃ x : Proj 𝒜, f i ∉ x.asHomogeneousIdeal
  have hbad : ∀ i, ¬good i → ∀ c : A, ∃ m : ℕ, f i ^ m * c = 0 := by
    intro i hi c
    have hi' : ∀ x : Proj 𝒜, f i ∈ x.asHomogeneousIdeal := fun x => by
      by_contra h
      exact hi ⟨x, h⟩
    obtain ⟨m, hm⟩ := isNilpotent_of_forall_mem (hf i) one_pos hi'
    exact ⟨m, by rw [hm, zero_mul]⟩
  let Aₐ : ∀ i, Away 𝒜 (f i) := fun i => HomogeneousLocalization.mk ⟨p, ⟨a, ha⟩, ⟨_, hpow i p⟩, p, rfl⟩
  let Bₐ : ∀ i, Away 𝒜 (f i) := fun i => HomogeneousLocalization.mk ⟨q, ⟨b, hb⟩, ⟨_, hpow i q⟩, q, rfl⟩
  have hAB : ∀ i, Aₐ i * Bₐ i = 0 := by
    intro i
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero, Localization.mk_mul]
    change Localization.mk (a * b) _ = 0
    rw [hab, Localization.mk_zero]
  have hA0 : ∀ i, Aₐ i = 0 ↔ ∃ m : ℕ, f i ^ m * a = 0 := fun i => away_mk_eq_zero_iff _
  have hB0 : ∀ i, Bₐ i = 0 ↔ ∃ m : ℕ, f i ^ m * b = 0 := fun i => away_mk_eq_zero_iff _
  -- if `a` survives on one chart, it survives on every chart
  have hcross : ∀ i j, good i → good j → Aₐ i ≠ 0 → Aₐ j ≠ 0 := by
    rintro i j ⟨x, hx⟩ ⟨y, hy⟩ hAi hAj
    have := isDomain_away_of_isIntegral (hf i) hx
    obtain ⟨m, hm⟩ := (hA0 j).1 hAj
    let R : Away 𝒜 (f i) := HomogeneousLocalization.mk ⟨1, ⟨f j, hf j⟩, ⟨f i, hf i⟩, 1, pow_one _⟩
    have hRA : R ^ m * Aₐ i = 0 := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
        HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
        HomogeneousLocalization.val_zero, Localization.mk_pow, Localization.mk_mul]
      change Localization.mk (f j ^ m * a) _ = 0
      rw [hm, Localization.mk_zero]
    have hR : R = 0 := (pow_eq_zero_iff'.1 ((mul_eq_zero.1 hRA).resolve_right hAi)).1
    obtain ⟨l, hl⟩ := (away_mk_eq_zero_iff _).1 hR
    obtain ⟨z, hzi, hzj⟩ := nonempty_preirreducible_inter (Proj.basicOpen 𝒜 (f i)).isOpen
      (Proj.basicOpen 𝒜 (f j)).isOpen ⟨x, hx⟩ ⟨y, hy⟩
    have hnil : f i ^ (l + 1) * f j ∈ z.asHomogeneousIdeal := by
      rw [pow_succ, mul_assoc, mul_comm (f i), ← mul_assoc]
      change f i ^ l * f j * f i ∈ _
      rw [show f i ^ l * f j = 0 from hl, zero_mul]
      exact zero_mem _
    rcases z.isPrime.mem_or_mem hnil with h1 | h1
    · exact hzi (z.isPrime.mem_of_pow_mem _ h1)
    · exact hzj h1
  by_cases hex : ∃ i, good i ∧ Aₐ i ≠ 0
  · obtain ⟨i, hgi, hAi⟩ := hex
    right
    intro j
    by_cases hgj : good j
    · obtain ⟨y, hy⟩ := hgj
      have := isDomain_away_of_isIntegral (hf j) hy
      exact (hB0 j).1 ((mul_eq_zero.1 (hAB j)).resolve_left (hcross i j hgi ⟨y, hy⟩ hAi))
    · exact hbad j hgj b
  · left
    intro i
    by_cases hgi : good i
    · exact (hA0 i).1 (by
        by_contra h
        exact hex ⟨i, hgi, h⟩)
    · exact hbad i hgi a

end IntegralProj

/-! ## Closed subschemes of `ℙʳ_k` -/

section ClosedSubscheme

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {r : ℕ}
  (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k))

local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k
local notation "S" => MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal
local notation "𝒬" => gradedQuotient 𝒮 I

/-- The image `xᵢ ∈ S` of the coordinate `xᵢ`. -/
def coord (i : Fin (r + 1)) : S := Ideal.Quotient.mk I.toIdeal (X i)

theorem coord_mem (i : Fin (r + 1)) : coord I i ∈ 𝒬 1 :=
  mk_mem_gradedQuotient (isHomogeneous_X k i)

theorem mk_mem_of_mem {d : ℕ} {p : MvPolynomial (Fin (r + 1)) k} (hp : p ∈ 𝒮 d) :
    Ideal.Quotient.mk I.toIdeal p ∈ 𝒬 d :=
  mk_mem_gradedQuotient hp

instance noetherianSpace_proj : TopologicalSpace.NoetherianSpace (Proj 𝒬) :=
  (projQuotientι 𝒮 I).isClosedEmbedding.isInducing.noetherianSpace

/-- **A connected normal closed subscheme of `ℙʳ_k` is integral.** -/
theorem isIntegral_proj [ConnectedSpace (Proj 𝒬)] [Hartshorne.IsNormal (Proj 𝒬)] :
    IsIntegral (Proj 𝒬) :=
  isIntegral_of_connectedSpace (Proj 𝒬)

/-- **The homogeneous coordinate ring is a domain** (Exercise 5.14(a)): `X = Proj S` is integral
and `I` is saturated. -/
theorem isDomain_of_isIntegral [IsIntegral (Proj 𝒬)]
    (hsat : ∀ s : MvPolynomial (Fin (r + 1)) k, (∀ i, ∃ n : ℕ, X i ^ n * s ∈ I.toIdeal) →
      s ∈ I.toIdeal) :
    IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (Proj 𝒬))
  have hsat' : ∀ {d : ℕ} {a : MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal}, a ∈ 𝒬 d →
      (∀ i, ∃ m : ℕ, coord I i ^ m * a = 0) → a = 0 := by
    intro d a ha h
    obtain ⟨P, -, rfl⟩ := mem_gradedQuotient_iff.1 ha
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine hsat P fun i => ?_
    obtain ⟨m, hm⟩ := h i
    exact ⟨m, by rwa [coord, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm⟩
  have hbot : (⊥ : Ideal (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)).IsPrime := by
    have hhom : (⊥ : Ideal (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)).IsHomogeneous 𝒬 := by
      have := (⊥ : HomogeneousIdeal 𝒬).isHomogeneous
      rwa [HomogeneousIdeal.toIdeal_bot] at this
    refine hhom.isPrime_of_homogeneous_mem_or_mem ?_ ?_
    · intro htop
      apply x.isPrime.ne_top
      rw [eq_top_iff]
      intro y _
      have : (1 : MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal) = 0 := by
        rw [← Ideal.mem_bot, htop]
        trivial
      rw [← one_mul y, this, zero_mul]
      exact zero_mem _
    · rintro a b ⟨p, ha⟩ ⟨q, hb⟩ hab
      rw [Ideal.mem_bot] at hab ⊢
      rw [Ideal.mem_bot]
      rcases forall_pow_mul_eq_zero_or (coord I) (coord_mem I) ha hb hab with h | h
      · exact Or.inl (hsat' ha h)
      · exact Or.inr (hsat' hb h)
  exact IsDomain.of_bot_isPrime _

section Integral

variable [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)]

omit [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)] in
variable {I} in
/-- One chart: multiplying `z` by `xᵢ^{jᵢ}` (with `xᵢ^{jᵢ} z = aᵢ`) clears it on every monomial
with `βᵢ ≥ jᵢ`. -/
theorem exists_mem_mul_monomial {n : ℕ} {z : FractionRing S} {j : Fin (r + 1) → ℕ}
    {a : Fin (r + 1) → S} (ha : ∀ i, a i ∈ 𝒬 (j i + n))
    (hza : ∀ i, algebraMap S (FractionRing S) (a i) =
      algebraMap S (FractionRing S) (coord I i) ^ j i * z)
    (β : Fin (r + 1) →₀ ℕ) (i : Fin (r + 1)) (hi : j i ≤ β i) :
    ∃ b ∈ 𝒬 (β.degree + n), algebraMap S (FractionRing S) b =
      z * algebraMap S (FractionRing S) (Ideal.Quotient.mk I.toIdeal (monomial β 1)) := by
  set β' := β - Finsupp.single i (j i) with hβ'
  have hβ : β = Finsupp.single i (j i) + β' := by
    rw [hβ', add_tsub_cancel_of_le]
    exact Finsupp.single_le_iff.2 hi
  have hdeg : β.degree = j i + β'.degree := by
    conv_lhs => rw [hβ]
    rw [map_add, Finsupp.degree_single]
  refine ⟨a i * Ideal.Quotient.mk I.toIdeal (monomial β' 1), ?_, ?_⟩
  · have := SetLike.mul_mem_graded (ha i) (mk_mem_of_mem I (isHomogeneous_monomial (d := β') (1 : k) rfl))
    rwa [show j i + n + β'.degree = β.degree + n by omega] at this
  · rw [map_mul, hza i, hβ, monomial_single_add, map_mul, map_mul, map_pow, coord, map_pow]
    ring

omit [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)] in
variable {I} in
/-- If `z ∈ K` satisfies `xᵢ^{jᵢ} z ∈ S_{jᵢ + n}` for every `i`,
then `z · S_d ⊆ S_{d + n}` once `d ≥ ∑ jᵢ`. -/
theorem exists_mem_mul_of_le {n : ℕ} {z : FractionRing S} {j : Fin (r + 1) → ℕ}
    {a : Fin (r + 1) → S} (ha : ∀ i, a i ∈ 𝒬 (j i + n))
    (hza : ∀ i, algebraMap S (FractionRing S) (a i) =
      algebraMap S (FractionRing S) (coord I i) ^ j i * z)
    {d : ℕ} (hd : ∑ i, j i ≤ d) {g : S} (hg : g ∈ 𝒬 d) :
    ∃ b ∈ 𝒬 (d + n), algebraMap S (FractionRing S) b = z * algebraMap S (FractionRing S) g := by
  classical
  obtain ⟨p, hp, rfl⟩ := mem_gradedQuotient_iff.1 hg
  have hmono : ∀ β ∈ p.support, ∃ b ∈ 𝒬 (d + n), algebraMap S (FractionRing S) b =
      z * algebraMap S (FractionRing S) (Ideal.Quotient.mk I.toIdeal (monomial β 1)) := by
    intro β hβ
    have hβd : β.degree = d := by
      rw [Finsupp.degree_apply]
      exact ((mem_homogeneousSubmodule d p).1 hp).degree_eq_sum_deg_support hβ |>.symm
    obtain ⟨i, hi⟩ : ∃ i, j i ≤ β i := by
      by_contra! hlt
      have : ∑ i, β i < ∑ i, j i :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hlt i
      rw [← Finsupp.degree_eq_sum, hβd] at this
      omega
    have := exists_mem_mul_monomial ha hza β i hi
    rwa [hβd] at this
  choose! b hb hbz using hmono
  refine ⟨∑ β ∈ p.support, Ideal.Quotient.mk I.toIdeal (C (coeff β p)) * b β, ?_, ?_⟩
  · refine sum_mem fun β hβ => ?_
    have := SetLike.mul_mem_graded (mk_mem_of_mem I (isHomogeneous_C (Fin (r + 1)) (coeff β p)))
      (hb β hβ)
    rwa [zero_add] at this
  · conv_rhs => rw [p.as_sum]
    rw [map_sum, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [map_mul, hbz β hβ, show (monomial β (coeff β p) : MvPolynomial (Fin (r + 1)) k) =
      C (coeff β p) * monomial β 1 by rw [C_mul_monomial, mul_one], map_mul, map_mul]
    ring

variable {I} in
/-- **The determinant trick.** An element `z ∈ K` with `xᵢ^{jᵢ} z ∈ S_{jᵢ + n}` for every `i` is
integral over `S`: it stabilizes the nonzero finitely generated ideal `S_{≥ ∑ jᵢ}`. -/
theorem isIntegral_of_forall_coord {n : ℕ} {z : FractionRing S} {j : Fin (r + 1) → ℕ}
    {a : Fin (r + 1) → S} (ha : ∀ i, a i ∈ 𝒬 (j i + n))
    (hza : ∀ i, algebraMap S (FractionRing S) (a i) =
      algebraMap S (FractionRing S) (coord I i) ^ j i * z)
    (hne : ∃ i, coord I i ≠ 0) :
    IsIntegral S z := by
  set N := ∑ i, j i
  let G : Set S := {g | ∃ d, N ≤ d ∧ g ∈ 𝒬 d}
  let M : Submodule S (FractionRing S) := Submodule.span S (algebraMap S (FractionRing S) '' G)
  have hMfg : M.FG := by
    have h1 : (Submodule.span S G).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Algebra.linearMap S (FractionRing S))
    rwa [Submodule.map_span] at h2
  have hM0 : M ≠ ⊥ := by
    obtain ⟨i, hi⟩ := hne
    intro hM
    have hmem : algebraMap S (FractionRing S) (coord I i ^ N) ∈ M :=
      Submodule.subset_span ⟨_, ⟨N, le_rfl, by
        simpa using SetLike.pow_mem_graded N (coord_mem I i)⟩, rfl⟩
    rw [hM, Submodule.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective S (FractionRing S))] at hmem
    exact pow_ne_zero N hi hmem
  refine isIntegral_of_smul_mem_submodule M hM0 hMfg z fun w hw => ?_
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g, ⟨d, hd, hg⟩, rfl⟩ := hw
    obtain ⟨b, hb, hbz⟩ := exists_mem_mul_of_le ha hza hd hg
    rw [smul_eq_mul, ← hbz]
    exact Submodule.subset_span ⟨b, ⟨d + n, by omega, hb⟩, rfl⟩
  | zero => simp
  | add w w' _ _ hw hw' =>
    rw [smul_add]
    exact add_mem hw hw'
  | smul c w _ hw =>
    rw [smul_comm]
    exact M.smul_mem c hw

/-- **The image of `S'` consists of integral elements** (the first half of Exercise 5.14(a)):
each section of `𝒪_X(n)` is, on every chart `D₊(xᵢ)`, a fraction `a / xᵢ^{j}`. -/
theorem isIntegral_sectionToFraction (hne : ∃ i, coord I i ≠ 0) (n : ℕ)
    (t : twistGlobal (𝟙_ (Proj 𝒬).Modules) (n : ℤ)) :
    IsIntegral (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal) (sectionToFraction 𝒬 n t) := by
  classical
  have hchart : ∀ i, ∃ (j : ℕ) (a : MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal), a ∈ 𝒬 (j + n) ∧
      algebraMap _ (FractionRing (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)) a =
        algebraMap _ _ (coord I i) ^ j * sectionToFraction 𝒬 n t := by
    intro i
    by_cases hi : coord I i = 0
    · exact ⟨1, 0, zero_mem _, by rw [hi, map_zero, zero_pow one_ne_zero, zero_mul]⟩
    · exact exists_mem_eq_pow_mul_sectionToFraction (coord_mem I i) hi n t
  choose j a ha hza using hchart
  exact isIntegral_of_forall_coord ha hza hne

theorem isIntegral_sectionRingToFraction (hne : ∃ i, coord I i ≠ 0)
    (y : DirectSum ℕ fun n => twistGlobal (𝟙_ (Proj 𝒬).Modules) (n : ℤ)) :
    IsIntegral (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal) (sectionRingToFraction 𝒬 y) := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero]; exact isIntegral_zero
  | of n t => rw [sectionRingToFraction_of]; exact isIntegral_sectionToFraction I hne n t
  | add y y' hy hy' => rw [map_add]; exact hy.add hy'

omit [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)] in
theorem exists_coord_notMem (x : Proj 𝒬) : ∃ i, coord I i ∉ x.asHomogeneousIdeal := by
  classical
  by_contra! hall
  apply x.not_irrelevant_le
  intro a ha
  rw [← DirectSum.sum_support_decompose 𝒬 a]
  refine sum_mem fun d _ => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : (DirectSum.decompose 𝒬 a 0 : MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal) = 0 := ha
    rw [this]
    exact zero_mem _
  · obtain ⟨p, hp, hpa⟩ := mem_gradedQuotient_iff.1 (DirectSum.decompose 𝒬 a d).2
    rw [← hpa]
    have hspan : p ∈ Ideal.span (X '' (Set.univ : Set (Fin (r + 1)))) := by
      rw [mem_ideal_span_X_image]
      intro m hm
      have hdeg := ((mem_homogeneousSubmodule d p).1 hp).degree_eq_sum_deg_support hm
      obtain ⟨i, hi⟩ : m.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h0
        rw [h0, Finset.sum_empty] at hdeg
        omega
      exact ⟨i, Set.mem_univ _, Finsupp.mem_support_iff.1 hi⟩
    have hmap := Ideal.mem_map_of_mem (Ideal.Quotient.mk I.toIdeal) hspan
    rw [Ideal.map_span] at hmap
    refine (Ideal.span_le.2 ?_) hmap
    rintro _ ⟨_, ⟨i, -, rfl⟩, rfl⟩
    exact hall i

/-- **Normality of the charts.** On a normal integral `X = Proj S`, the coordinate ring
`S_(xᵢ) = 𝒪_X(D₊(xᵢ))` of each nonempty chart is integrally closed. -/
theorem isIntegrallyClosed_away [IsIntegral (Proj 𝒬)] [Hartshorne.IsNormal (Proj 𝒬)]
    (i : Fin (r + 1)) (hi : coord I i ≠ 0) : IsIntegrallyClosed (Away 𝒬 (coord I i)) := by
  have hU := Proj.isAffineOpen_basicOpen 𝒬 (coord I i) (coord_mem I i) one_pos
  have h := not_irrelevant_le_bot_of_mem_one (coord_mem I i) hi
  have : Nonempty (Proj.basicOpen 𝒬 (coord I i)) :=
    ⟨⟨genericPoint h, genericPoint_mem_basicOpen h hi⟩⟩
  have := isIntegrallyClosed_sections_of_isNormal (Proj 𝒬) hU
  exact IsIntegrallyClosed.of_equiv
    (Proj.basicOpenIsoAway 𝒬 (coord I i) (coord_mem I i) one_pos).commRingCatIsoToRingEquiv.symm

/-- **Every element of `K` integral over `S` comes from `S'`** (the second half of
Exercise 5.14(a)). On each chart `z ∈ S_(xᵢ)[xᵢ]`; the degree-`n` parts agree across the charts,
so each glues to a section of `𝒪_X(n)`. -/
theorem mem_range_sectionRingToFraction [IsIntegral (Proj 𝒬)] [Hartshorne.IsNormal (Proj 𝒬)]
    (hne : ∃ i, coord I i ≠ 0) {z : FractionRing (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)}
    (hz : IsIntegral (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal) z) :
    z ∈ Set.range (sectionRingToFraction 𝒬) := by
  classical
  obtain ⟨i0, hi0⟩ := hne
  have h := not_irrelevant_le_bot_of_mem_one (coord_mem I i0) hi0
  have hp : ∀ i (hi : coord I i ≠ 0), ∃ p : Polynomial (Away 𝒬 (coord I i)),
      chartPoly hi p = z := fun i hi => by
    have := isIntegrallyClosed_away I i hi
    exact exists_chartPoly_eq_of_isIntegral hi (coord_mem I i) hz
  choose p hpz using hp
  let comp : ∀ i, coord I i ≠ 0 → ℕ → FractionRing (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal) :=
    fun i hi n => awayToFraction hi ((p i hi).coeff n) * algebraMap _ _ (coord I i) ^ n
  let N : ℕ := ∑ i, if hi : coord I i ≠ 0 then (p i hi).natDegree + 1 else 0
  have hN : ∀ i (hi : coord I i ≠ 0), (p i hi).natDegree < N := by
    intro i hi
    have := Finset.single_le_sum (f := fun i => if hi : coord I i ≠ 0 then
      (p i hi).natDegree + 1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [dif_pos hi] at this
    omega
  have hsum : ∀ i (hi : coord I i ≠ 0), z = ∑ n ∈ Finset.range N, comp i hi n := fun i hi =>
    (hpz i hi).symm.trans (chartPoly_eq_sum hi (p i hi) (hN i hi))
  have huniq : ∀ i (hi : coord I i ≠ 0) n, n < N → comp i hi n = comp i0 hi0 n := by
    intro i hi
    have h0 := eq_zero_of_sum_isHomFrac_eq_zero (Finset.range N)
      (fun n => comp i hi n - comp i0 hi0 n)
      (fun n _ => (isHomFrac_awayToFraction_mul_pow hi (coord_mem I i) _ n).sub
        (isHomFrac_awayToFraction_mul_pow hi0 (coord_mem I i0) _ n))
      (by rw [Finset.sum_sub_distrib, ← hsum, ← hsum, sub_self])
    intro n hn
    exact sub_eq_zero.1 (h0 n (Finset.mem_range.2 hn))
  have ht : ∀ n : ℕ, ∃ t : twistGlobal (𝟙_ (Proj 𝒬).Modules) (n : ℤ),
      sectionToFraction 𝒬 n t = comp i0 hi0 n := by
    intro n
    refine exists_sectionToFraction_eq (coord I) (coord_mem I) (exists_coord_notMem I) h n _ ?_
    intro i hi
    by_cases hn : n < N
    · rw [← huniq i hi n hn]
      exact exists_mem_eq_pow_mul_awayToFraction hi (coord_mem I i) _ n
    · have hc : (p i0 hi0).coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hN i0 hi0; omega)
      refine ⟨0, 0, zero_mem _, ?_⟩
      simp only [comp, hc, map_zero, zero_mul, mul_zero]
  choose t htz using ht
  refine ⟨∑ n ∈ Finset.range N, DirectSum.of _ n (t n), ?_⟩
  rw [map_sum, hsum i0 hi0]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [sectionRingToFraction_of, htz]

omit [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)] in
theorem exists_coord_ne_zero (x : Proj 𝒬) : ∃ i, coord I i ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_coord_notMem I x
  exact ⟨i, fun h0 => hi (h0 ▸ zero_mem _)⟩

/-- **`S'` is the integral closure of `S`**, for a domain `S` with `Proj S` integral and normal:
the map `S' → K` is injective and multiplicative, and its image is the integral closure of `S`
in `K`. (It is the identity on `S`: `sectionToFraction_mulGlobal_unitSection`.) -/
theorem sectionRing_isIntegralClosure [IsIntegral (Proj 𝒬)] [Hartshorne.IsNormal (Proj 𝒬)] :
    Function.Injective (sectionRingToFraction 𝒬) ∧
    (∀ (n m : ℤ) (y : twistGlobal (𝟙_ (Proj 𝒬).Modules) n)
      (z : twistGlobal (𝟙_ (Proj 𝒬).Modules) m),
      sectionToFraction 𝒬 (n + m) (sectionMul 𝒬 n m y z) =
        sectionToFraction 𝒬 n y * sectionToFraction 𝒬 m z) ∧
    Set.range (sectionRingToFraction 𝒬) =
      (integralClosure (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)
        (FractionRing (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)) :
            Set (FractionRing (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal))) := by
  have hne := exists_coord_ne_zero I
    (Classical.choice (AlgebraicGeometry.IsIntegral.nonempty : Nonempty (Proj 𝒬)))
  have h := not_irrelevant_le_bot_of_mem_one (coord_mem I hne.choose) hne.choose_spec
  refine ⟨sectionRingToFraction_injective (𝒜 := 𝒬) h,
    fun n m y z => sectionToFraction_sectionMul (𝒜 := 𝒬) n m y z, ?_⟩
  exact Set.Subset.antisymm
    (Set.range_subset_iff.2 fun y => isIntegral_sectionRingToFraction I hne y)
    fun _ hz => mem_range_sectionRingToFraction I hne hz

end Integral

/-- **Hartshorne II, Exercise 5.14(a).** Let `k` be algebraically closed and let `X ⊆ ℙʳ_k` be a
connected normal closed subscheme, presented as `X = Proj S` for its homogeneous coordinate ring
`S = k[x₀, …, xᵣ] / I`, where `I = Γ_*(ℐ_X)` is the saturated homogeneous ideal of `X`
(hypothesis `hsat`; Corollary 5.16 and Exercise 5.10). Then `S` is a domain, and
`S' = ⨁_{n ≥ 0} Γ(X, 𝒪_X(n))` is the integral closure of `S` in its fraction field `K`:
the natural map `S' → K` (`sectionRingToFraction`, the value at the generic point) is injective
and multiplicative, and its image is exactly `integralClosure S K`. On `S` it is the inclusion
`S ⊆ K` (`sectionToFraction_mulGlobal_unitSection`). The algebraic closedness of `k` is the
book's standing hypothesis; the proof does not use it. -/
theorem projectiveSectionRing_isIntegralClosure [IsAlgClosed k]
    (hsat : ∀ s : MvPolynomial (Fin (r + 1)) k, (∀ i, ∃ n : ℕ, X i ^ n * s ∈ I.toIdeal) →
      s ∈ I.toIdeal)
    [ConnectedSpace (Proj 𝒬)] [Hartshorne.IsNormal (Proj 𝒬)] :
    IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal) ∧
      ∀ [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)],
        Function.Injective (sectionRingToFraction 𝒬) ∧
        (∀ (n m : ℤ) (y : twistGlobal (𝟙_ (Proj 𝒬).Modules) n)
          (z : twistGlobal (𝟙_ (Proj 𝒬).Modules) m),
          sectionToFraction 𝒬 (n + m) (sectionMul 𝒬 n m y z) =
            sectionToFraction 𝒬 n y * sectionToFraction 𝒬 m z) ∧
        Set.range (sectionRingToFraction 𝒬) =
          (integralClosure (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)
            (FractionRing (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)) :
              Set (FractionRing (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal))) := by
  have := isIntegral_proj I
  refine ⟨isDomain_of_isIntegral I hsat, ?_⟩
  intro _
  exact sectionRing_isIntegralClosure I

end ClosedSubscheme

end ProjectiveSectionRing

end Hartshorne
