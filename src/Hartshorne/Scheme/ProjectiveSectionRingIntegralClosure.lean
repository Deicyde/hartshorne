/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceSectionRing
import Hartshorne.Scheme.ProjClosedSubschemeTruncation
import Hartshorne.Scheme.AbsoluteNormalizationUniversal

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
      (unitorGlobal (0 + d) (mulGlobal _ 0 d ⟨s, hs⟩ (unitSection 𝒜))) x).val =
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
    sectionToFraction 𝒜 (0 + d) (mulGlobal _ 0 d ⟨s, hs⟩ (unitSection 𝒜)) =
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

end Fraction

end ProjectiveSectionRing

end Hartshorne
