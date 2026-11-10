/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.RamificationIndex
import Hartshorne.Scheme.FrobeniusTwist
import Hartshorne.Scheme.Differentials.FrobeniusDifferentials
import Hartshorne.Weil.FiniteFieldFrobenius
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular

/-!
# Frobenius is ramified everywhere

Hartshorne, *Algebraic Geometry*, IV.2, Example 2.5.1 (p. 303).

Let `Y` be a nonsingular curve over a perfect field `k` of characteristic `p` (Hartshorne works
over an algebraically closed field), and let `F : Y_p ⟶ Y` be the `k`-linear Frobenius
(`frobeniusTwistHom`, the underlying map of `AlgebraicGeometry.Scheme.frobeniusTwistTo`), whose
underlying scheme map is the absolute Frobenius.

* `frobeniusTwistHom_apply`: `F` is the identity on points.
* `isNonsingularCurve_frobeniusTwist`, `locallyQuasiFinite_frobeniusTwistHom`: `Y_p` is again a
  nonsingular curve over `k` and `F` is locally quasi-finite, so ramification indices are defined.
* `ramificationIndex_frobeniusTwistHom`: every closed point has ramification index `p`.
* `pullbackRelativeDifferentialsToComp_frobeniusTwistHom_eq_zero`: `F^*Ω_{Y/k} ⟶ Ω_{Y_p/k}` is
  zero, so `Ω_{Y_p/k} ≅ Ω_{Y_p/Y}` (`relativeDifferentialsFrobeniusTwistIso`).
* `not_isSeparable_frobeniusTwistHom`: `F` is inseparable.
* `relativeDifferentials_frobeniusTwistHom_isLocallyFreeOfRank_one`: over an algebraically closed
  field, `Ω_{Y_p/Y}` is locally free of rank one.
-/

noncomputable section

open CategoryTheory Limits Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
variable (Y : Scheme.{u}) [Y.Over (Spec (.of k))]

variable (k) in
/-- `Y` as an object of the category of `k`-schemes. -/
def asOverSpec : Over (Spec (.of k)) := Over.mk (Y ↘ Spec (.of k))

variable (k p) in
/-- Hartshorne's `Y_p`: the scheme `Y` with structure morphism followed by Frobenius of `k`. -/
def frobeniusTwistScheme : Scheme.{u} := (frobeniusTwist (p := p) k (asOverSpec k Y)).left

instance : (frobeniusTwistScheme k p Y).Over (Spec (.of k)) :=
  ⟨(frobeniusTwist (p := p) k (asOverSpec k Y)).hom⟩

instance [IsIntegral Y] : IsIntegral (frobeniusTwistScheme k p Y) :=
  inferInstanceAs (IsIntegral Y)

variable (k p) in
/-- Hartshorne's `k`-linear Frobenius `F : Y_p ⟶ Y`; its underlying map is the absolute
Frobenius. -/
def frobeniusTwistHom : frobeniusTwistScheme k p Y ⟶ Y :=
  (frobeniusTwistTo (p := p) k (asOverSpec k Y)).left

lemma frobeniusTwistHom_eq :
    frobeniusTwistHom k p Y = (asOverSpec k Y).left.absoluteFrobenius p := rfl

/-- `F` raises germs to their `p`th powers. -/
theorem frobeniusTwistHom_stalkMap_apply (x : frobeniusTwistScheme k p Y)
    (a : Y.presheaf.stalk (frobeniusTwistHom k p Y x)) :
    (frobeniusTwistHom k p Y).stalkMap x a = a ^ p :=
  absoluteFrobenius_stalkMap_apply (asOverSpec k Y).left p x a

/-- `F` is the identity on points. -/
theorem frobeniusTwistHom_apply (x : frobeniusTwistScheme k p Y) :
    frobeniusTwistHom k p Y x = (x : Y) :=
  rfl

/-- `F` is a morphism of `k`-schemes. -/
theorem frobeniusTwistHom_comp_structureMap :
    frobeniusTwistHom k p Y ≫ (Y ↘ Spec (.of k)) = frobeniusTwistScheme k p Y ↘ Spec (.of k) :=
  (absoluteFrobenius_comp_structureMap k (asOverSpec k Y))

/-- The first map `F^*Ω_{Y/k} ⟶ Ω_{Y_p/k}` of the transitivity sequence is zero, since
`d(a ^ p) = 0`. -/
theorem pullbackRelativeDifferentialsToComp_frobeniusTwistHom_eq_zero :
    pullbackRelativeDifferentialsToComp (frobeniusTwistHom k p Y) (Y ↘ Spec (.of k)) = 0 := by
  apply pullbackRelativeDifferentialsToComp_eq_zero_of_d
  intro V b
  exact relativeDifferentialsDerivation_d_pow_eq_zero _
    (natCast_eq_zero_of_hom_spec (frobeniusTwistHom k p Y ≫ (Y ↘ Spec (.of k))) _) b

/-- `Ω_{Y_p/k} ≅ Ω_{Y_p/Y}`. -/
def relativeDifferentialsFrobeniusTwistIso :
    relativeDifferentials (frobeniusTwistScheme k p Y ↘ Spec (.of k)) ≅
      relativeDifferentials (frobeniusTwistHom k p Y) :=
  have := isIso_relativeDifferentialsCompToLeft_of_eq_zero _ _
    (pullbackRelativeDifferentialsToComp_frobeniusTwistHom_eq_zero (k := k) (p := p) Y)
  relativeDifferentialsCongr (frobeniusTwistHom_comp_structureMap Y).symm ≪≫
    asIso (relativeDifferentialsCompToLeft (frobeniusTwistHom k p Y) (Y ↘ Spec (.of k)))

variable [IsIntegral Y]

/-- Over a perfect field, `Y_p` is again a nonsingular curve. -/
theorem isNonsingularCurve_frobeniusTwist [PerfectRing k p] (hY : Y.IsNonsingularCurve k) :
    (frobeniusTwistScheme k p Y).IsNonsingularCurve k where
  isSeparated := by
    have := hY.isSeparated
    change IsSeparated ((Y ↘ Spec (.of k)) ≫ specFrobenius p k)
    infer_instance
  locallyOfFiniteType := by
    have := hY.locallyOfFiniteType
    change LocallyOfFiniteType ((Y ↘ Spec (.of k)) ≫ specFrobenius p k)
    infer_instance
  quasiCompact := by
    have := hY.quasiCompact
    change QuasiCompact ((Y ↘ Spec (.of k)) ≫ specFrobenius p k)
    infer_instance
  topologicalKrullDim_eq_one := hY.topologicalKrullDim_eq_one
  isRegularLocalRing_stalk := hY.isRegularLocalRing_stalk

/-- Over a perfect field, `F` is locally quasi-finite. -/
theorem locallyQuasiFinite_frobeniusTwistHom [PerfectRing k p] (hY : Y.IsNonsingularCurve k) :
    LocallyQuasiFinite (frobeniusTwistHom k p Y) := by
  have := (isNonsingularCurve_frobeniusTwist Y hY).locallyOfFiniteType
  have : LocallyOfFiniteType (frobeniusTwistHom k p Y ≫ (Y ↘ Spec (.of k))) := by
    rw [frobeniusTwistHom_comp_structureMap]; infer_instance
  have : LocallyOfFiniteType (frobeniusTwistHom k p Y) :=
    locallyOfFiniteType_of_comp _ (Y ↘ Spec (.of k))
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
  refine Set.Subsingleton.finite fun a ha b hb => ?_
  have ha : (a : Y) = y := ha
  have hb : (b : Y) = y := hb
  exact ha.trans hb.symm

/-- **Every point of a nonsingular curve is ramified of index `p` under Frobenius**
(Hartshorne IV.2, Example 2.5.1). At every closed point `P` (a point of codimension one; the
points of Hartshorne's curve), `e_P = p` for `F : Y_p ⟶ Y`. -/
theorem ramificationIndex_frobeniusTwistHom [PerfectRing k p] (hY : Y.IsNonsingularCurve k)
    {P : frobeniusTwistScheme k p Y} (hP : coheight P = 1) :
    letI := locallyQuasiFinite_frobeniusTwistHom Y hY
    (isNonsingularCurve_frobeniusTwist Y hY).ramificationIndex hY (frobeniusTwistHom k p Y) P =
      p := by
  let := locallyQuasiFinite_frobeniusTwistHom Y hY
  set hYp := isNonsingularCurve_frobeniusTwist Y hY
  have hQ : coheight (frobeniusTwistHom k p Y P) = 1 := hP
  have ht := hY.irreducible_localParameter hQ
  rw [hYp.ramificationIndex_eq hY _ hP ht, hYp.finiteCurveFunctionFieldMap_algebraMap,
    frobeniusTwistHom_stalkMap_apply, ← one_mul (_ ^ p)]
  exact_mod_cast hYp.ord_algebraMap_unit_mul_pow hP (π := hY.localParameter P) ht 1 p

/-- On function fields, `F^#` is the `p`th power map. -/
theorem finiteCurveFunctionFieldMap_frobeniusTwistHom [PerfectRing k p]
    (hY : Y.IsNonsingularCurve k) (x : Y.functionField) :
    letI := locallyQuasiFinite_frobeniusTwistHom Y hY
    (isNonsingularCurve_frobeniusTwist Y hY).finiteCurveFunctionFieldMap hY
      (frobeniusTwistHom k p Y) x = x ^ p := by
  let := locallyQuasiFinite_frobeniusTwistHom Y hY
  change (frobeniusTwistHom k p Y).stalkMap _
    ((Y.presheaf.stalkSpecializes (specializes_refl (genericPoint Y))) x) = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact frobeniusTwistHom_stalkMap_apply Y _ x

/-- A nonsingular curve has a closed point (a point of codimension one). -/
theorem IsNonsingularCurve.exists_coheight_eq_one {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsIntegral X] (hX : X.IsNonsingularCurve k) : ∃ P : X, coheight P = 1 := by
  by_contra! h
  have : Subsingleton X := ⟨fun a b => by
    have ha : a = genericPoint X := by
      by_contra ha; exact h a ((hX.coheight_eq_one_iff a).mpr ha)
    have hb : b = genericPoint X := by
      by_contra hb; exact h b ((hX.coheight_eq_one_iff b).mpr hb)
    rw [ha, hb]⟩
  have h0 := Hartshorne.topologicalKrullDim_eq_zero_of_subsingleton X
  rw [hX.topologicalKrullDim_eq_one] at h0
  exact one_ne_zero h0

/-- **Frobenius is inseparable.** The function field extension `F^# : K(Y) → K(Y_p)` is not
separable. -/
theorem not_isSeparable_frobeniusTwistHom [PerfectRing k p] (hY : Y.IsNonsingularCurve k) :
    letI := locallyQuasiFinite_frobeniusTwistHom Y hY
    letI := ((isNonsingularCurve_frobeniusTwist Y hY).finiteCurveFunctionFieldMap hY
      (frobeniusTwistHom k p Y)).toAlgebra
    ¬ Algebra.IsSeparable Y.functionField (frobeniusTwistScheme k p Y).functionField := by
  let := locallyQuasiFinite_frobeniusTwistHom Y hY
  set hYp := isNonsingularCurve_frobeniusTwist Y hY
  let := (hYp.finiteCurveFunctionFieldMap hY (frobeniusTwistHom k p Y)).toAlgebra
  intro hsep
  have : Y.IsCharP p := isCharP_of_hom_spec (Y ↘ Spec (.of k))
  have : CharP Y.functionField p := IsCharP.charP_stalk (genericPoint Y)
  have hφ := finiteCurveFunctionFieldMap_frobeniusTwistHom Y hY
  have : IsPurelyInseparable Y.functionField (frobeniusTwistScheme k p Y).functionField :=
    (isPurelyInseparable_iff_pow_mem _ p).mpr fun x => ⟨1, x, by
      rw [pow_one, RingHom.algebraMap_toAlgebra]; exact hφ x⟩
  have hsurj := IsPurelyInseparable.surjective_algebraMap_of_isSeparable Y.functionField
    (frobeniusTwistScheme k p Y).functionField
  obtain ⟨P, hP⟩ := hYp.exists_coheight_eq_one
  let _ := hYp.satisfiesConditionStar.isNoetherian
  let π : (frobeniusTwistScheme k p Y).presheaf.stalk P := hY.localParameter P
  have ht : Irreducible π := hY.irreducible_localParameter (x := P) hP
  have h1 : (frobeniusTwistScheme k p Y).ord (algebraMap _ _ π) P = 1 := by
    have := hYp.ord_algebraMap_unit_mul_pow hP (π := π) ht 1 1
    simpa using this
  obtain ⟨y, hy⟩ := hsurj (algebraMap _ _ π)
  rw [RingHom.algebraMap_toAlgebra, hφ] at hy
  rw [← hy] at h1
  let z : (frobeniusTwistScheme k p Y).functionField := y
  have h1' : (frobeniusTwistScheme k p Y).ord (z ^ p) P = 1 := h1
  have hz0 : z ≠ 0 := by
    intro hz
    have hy' : (0 : (frobeniusTwistScheme k p Y).functionField) = algebraMap _ _ π := by
      rw [← hy]; exact ((congrArg (· ^ p) hz).trans (zero_pow (Fact.out : p.Prime).ne_zero)).symm
    exact ht.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp hy'.symm)
  have hpow : ∀ n : ℕ, (frobeniusTwistScheme k p Y).ord (z ^ n) P =
      n * (frobeniusTwistScheme k p Y).ord z P := by
    intro n
    induction n with
    | zero =>
      have h : (frobeniusTwistScheme k p Y).ord 1 P =
          (frobeniusTwistScheme k p Y).ord 1 P + (frobeniusTwistScheme k p Y).ord 1 P := by
        simpa using (frobeniusTwistScheme k p Y).ord_mul (x := P)
          (one_ne_zero (α := (frobeniusTwistScheme k p Y).functionField)) one_ne_zero
      rw [pow_zero, Nat.cast_zero, zero_mul]
      omega
    | succ n ih =>
      rw [pow_succ, (frobeniusTwistScheme k p Y).ord_mul (pow_ne_zero n hz0) hz0, ih]
      push_cast
      ring
  rw [hpow] at h1'
  have hp2 := (Fact.out : p.Prime).two_le
  have : (p : ℤ) ∣ 1 := ⟨_, h1'.symm⟩
  have := Int.eq_one_of_dvd_one (by positivity) this
  omega

/-- Over an algebraically closed field, `Ω_{Y_p/Y}` is locally free of rank one; in particular it
is not supported on finitely many points. -/
theorem relativeDifferentials_frobeniusTwistHom_isLocallyFreeOfRank_one [IsAlgClosed k]
    (hY : Y.IsNonsingularCurve k) :
    (relativeDifferentials (frobeniusTwistHom k p Y)).IsLocallyFreeOfRank 1 := by
  have hYp := isNonsingularCurve_frobeniusTwist Y hY
  have := hYp.locallyOfFiniteType
  have hreg : (frobeniusTwistScheme k p Y).IsRegular :=
    ⟨LocallyOfFiniteType.isLocallyNoetherian (frobeniusTwistScheme k p Y ↘ Spec (.of k)),
      hYp.isRegularLocalRing_stalk⟩
  have h := (Hartshorne.isRegular_iff_relativeDifferentials_isLocallyFreeOfRank
    (frobeniusTwistScheme k p Y ↘ Spec (.of k)) ⟨hYp.locallyOfFiniteType, hYp.quasiCompact⟩ 1
    (by exact_mod_cast hYp.topologicalKrullDim_eq_one)).mp hreg
  exact Modules.isLocallyFreeOfRank_of_iso
    (relativeDifferentialsFrobeniusTwistIso (k := k) (p := p) Y) h

end AlgebraicGeometry.Scheme
