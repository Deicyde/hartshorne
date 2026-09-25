/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.CoordinateRing
import Hartshorne.Affine.DimensionCoordinateRing
import Hartshorne.Curve.Basic
import Hartshorne.Curve.DVR
import Hartshorne.Morphism.AffineGermCompare
import Hartshorne.Morphism.FunctionFieldFractions
import Hartshorne.Morphism.LocalRingFunctionField
import Hartshorne.Morphism.LocalRingLocalization
import Hartshorne.Morphism.PointsMaximal
import Hartshorne.Nonsingular.IntrinsicNonsingular

/-!
# Dedekind domains as affine curves

The affine model of a finite-type Dedekind domain is chosen compatibly with a
specified fraction field and with localization at a specified maximal ideal.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

universe u v w

variable {k : Type u} [Field k]

/-- The canonical map from a localization at a prime into a chosen fraction
field. -/
noncomputable def localizationAtPrimeToFractionField
    (B : Type v) (K : Type w) [CommRing B] [IsDomain B] [Field K]
    [Algebra k B] [Algebra B K] [IsFractionRing B K]
    [Algebra k K] [IsScalarTower k B K]
    (p : Ideal B) [p.IsPrime] :
    Localization.AtPrime p →ₐ[k] K :=
  IsLocalization.liftAlgHom (M := p.primeCompl)
    (f := IsScalarTower.toAlgHom k B K) fun y ↦
      IsLocalization.map_units K
        ⟨y.1, mem_nonZeroDivisors_of_ne_zero fun hy ↦ y.2 (hy ▸ p.zero_mem)⟩

@[simp]
theorem localizationAtPrimeToFractionField_algebraMap
    (B : Type v) (K : Type w) [CommRing B] [IsDomain B] [Field K]
    [Algebra k B] [Algebra B K] [IsFractionRing B K]
    [Algebra k K] [IsScalarTower k B K]
    (p : Ideal B) [p.IsPrime] (b : B) :
    localizationAtPrimeToFractionField (k := k) B K p
        (algebraMap B (Localization.AtPrime p) b) = algebraMap B K b := by
  change IsLocalization.lift _ (algebraMap B (Localization.AtPrime p) b) =
    algebraMap B K b
  exact IsLocalization.lift_eq _ b

/-- The standard localization description of an affine local ring, as a
`k`-algebra equivalence. -/
noncomputable def localizationEquivLocalRingAlg
    {n : ℕ} {Y : Set (Fin n → k)} (hY : IsAffineVariety Y) (P : Y) :
    Localization.AtPrime (maximalIdealAt Y P) ≃ₐ[k]
      LocalRingAt hY.isIrreducible P where
  __ := localizationEquivLocalRing hY.isIrreducible P
  commutes' c := by
    change localizationToLocal hY.isIrreducible P
        (algebraMap (coordinateRing Y)
          (Localization.AtPrime (maximalIdealAt Y P))
          (algebraMap k (coordinateRing Y) c)) =
      algebraMap k (LocalRingAt hY.isIrreducible P) c
    rw [localizationToLocal, IsLocalization.lift_eq]
    exact (coordToLocal hY.isIrreducible P).commutes c

@[simp]
theorem localizationEquivLocalRingAlg_algebraMap
    {n : ℕ} {Y : Set (Fin n → k)} (hY : IsAffineVariety Y) (P : Y)
    (a : coordinateRing Y) :
    localizationEquivLocalRingAlg hY P
        (algebraMap (coordinateRing Y)
          (Localization.AtPrime (maximalIdealAt Y P)) a) =
      coordToLocal hY.isIrreducible P a := by
  change localizationToLocal hY.isIrreducible P
      (algebraMap (coordinateRing Y)
        (Localization.AtPrime (maximalIdealAt Y P)) a) =
    coordToLocal hY.isIrreducible P a
  rw [localizationToLocal, IsLocalization.lift_eq]
  rfl

@[simp]
theorem localizationEquivLocalRingAlg_symm_coordToLocal
    {n : ℕ} {Y : Set (Fin n → k)} (hY : IsAffineVariety Y) (P : Y)
    (a : coordinateRing Y) :
    (localizationEquivLocalRingAlg hY P).symm
        (coordToLocal hY.isIrreducible P a) =
      algebraMap (coordinateRing Y)
        (Localization.AtPrime (maximalIdealAt Y P)) a := by
  apply (localizationEquivLocalRingAlg hY P).injective
  simp

/-- The canonical inclusion of an affine local ring into its function field,
bundled as a `k`-algebra homomorphism. -/
private noncomputable def affineLocalToFunctionFieldAlgHom
    {n : ℕ} {Y : Set (Fin n → k)} (hY : IsAffineVariety Y) (P : Y) :
    LocalRingAt hY.isIrreducible P →ₐ[k] FunctionField hY.isIrreducible where
  toFun := localToFunctionField hY.isIrreducible P
  map_one' := rfl
  map_mul' := by
    refine Quotient.ind fun a ↦ Quotient.ind fun b ↦ ?_
    exact Quotient.sound fun _ _ _ ↦ rfl
  map_zero' := rfl
  map_add' := by
    refine Quotient.ind fun a ↦ Quotient.ind fun b ↦ ?_
    exact Quotient.sound fun _ _ _ ↦ rfl
  commutes' _ := rfl

@[simp]
private theorem affineLocalToFunctionFieldAlgHom_apply
    {n : ℕ} {Y : Set (Fin n → k)} (hY : IsAffineVariety Y) (P : Y)
    (z : LocalRingAt hY.isIrreducible P) :
    affineLocalToFunctionFieldAlgHom hY P z =
      localToFunctionField hY.isIrreducible P z :=
  rfl

/-- Transport the standard affine-local-ring description through an
equivalence of coordinate rings. -/
noncomputable def localRingAtEquivLocalizationAtPrime
    {n : ℕ} {Y : Set (Fin n → k)} (hY : IsAffineVariety Y) (P : Y)
    (B : Type v) [CommRing B] [Algebra k B]
    (eB : coordinateRing Y ≃ₐ[k] B) (p : Ideal B) [p.IsPrime]
    (hP : maximalIdealAt Y P = Ideal.comap eB.toRingHom p) :
    LocalRingAt hY.isIrreducible P ≃ₐ[k] Localization.AtPrime p := by
  have hsub :
      Submonoid.map eB (maximalIdealAt Y P).primeCompl = p.primeCompl := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      change a ∉ maximalIdealAt Y P at ha
      change eB a ∉ p
      intro hea
      apply ha
      rw [hP, Ideal.mem_comap]
      exact hea
    · intro hb
      refine ⟨eB.symm b, ?_, eB.apply_symm_apply b⟩
      change b ∉ p at hb
      change eB.symm b ∉ maximalIdealAt Y P
      intro he
      apply hb
      have hc : eB.symm b ∈ Ideal.comap eB.toRingHom p := by
        rw [← hP]
        exact he
      rw [Ideal.mem_comap] at hc
      simpa using hc
  exact (localizationEquivLocalRingAlg hY P).symm.trans
    (IsLocalization.algEquivOfAlgEquiv
      (Localization.AtPrime (maximalIdealAt Y P))
      (Localization.AtPrime p) eB hsub)

@[simp]
theorem localRingAtEquivLocalizationAtPrime_coordToLocal
    {n : ℕ} {Y : Set (Fin n → k)} (hY : IsAffineVariety Y) (P : Y)
    (B : Type v) [CommRing B] [Algebra k B]
    (eB : coordinateRing Y ≃ₐ[k] B) (p : Ideal B) [p.IsPrime]
    (hP : maximalIdealAt Y P = Ideal.comap eB.toRingHom p)
    (a : coordinateRing Y) :
    localRingAtEquivLocalizationAtPrime hY P B eB p hP
        (coordToLocal hY.isIrreducible P a) =
      algebraMap B (Localization.AtPrime p) (eB a) := by
  unfold localRingAtEquivLocalizationAtPrime
  rw [AlgEquiv.trans_apply,
    localizationEquivLocalRingAlg_symm_coordToLocal,
    IsLocalization.algEquivOfAlgEquiv_eq]

/-- A finite-type Dedekind domain of dimension one, together with a chosen
maximal ideal and fraction field, is the coordinate ring of a nonsingular
affine curve.  All three ring identifications commute with the canonical maps.
-/
theorem exists_dedekind_affine_model
    (B : Type v) (K : Type w) [IsAlgClosed k]
    [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (hdim : ringKrullDim B = 1)
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Algebra k K] [IsScalarTower k B K]
    (p : Ideal B) [p.IsMaximal] :
    ∃ (n : ℕ) (Y : Set (Fin n → k)) (hY : IsAffineVariety Y) (P : Y)
      (eB : coordinateRing Y ≃ₐ[k] B)
      (eK : FunctionField hY.isIrreducible ≃ₐ[k] K)
      (eP : LocalRingAt hY.isIrreducible P ≃ₐ[k] Localization.AtPrime p),
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).IsCurve ∧
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).Nonsingular ∧
      Ideal.map eB.toRingHom (maximalIdealAt Y P) = p ∧
      (∀ a : coordinateRing Y,
        eK (coordToRational hY.isIrreducible a) = algebraMap B K (eB a)) ∧
      ∀ z : LocalRingAt hY.isIrreducible P,
        eK (localToFunctionField hY.isIrreducible P z) =
          localizationAtPrimeToFractionField (k := k) B K p (eP z) := by
  obtain ⟨n, Y, hY, ⟨eB⟩⟩ :=
    exists_isAffineVariety_coordinateRing_equiv (k := k) (B := B)
  let m : Ideal (coordinateRing Y) := Ideal.comap eB.toRingHom p
  let _ : m.IsMaximal := by
    dsimp [m]
    exact Ideal.comap_isMaximal_of_surjective eB.toRingHom eB.surjective
  obtain ⟨P, hP⟩ :=
    maximalIdealAt_surjective hY.isAlgebraicSet (m := m)
      (show m.IsMaximal from inferInstance)
  have hP' : maximalIdealAt Y P = Ideal.comap eB.toRingHom p := hP
  let _ : IsDomain (coordinateRing Y) := isDomain_coordinateRing hY
  let _ : IsFractionRing (coordinateRing Y)
      (FunctionField hY.isIrreducible) :=
    isFractionRing_functionField hY.isIrreducible
  let eK : FunctionField hY.isIrreducible ≃ₐ[k] K :=
    IsFractionRing.algEquivOfAlgEquiv eB
  let eP : LocalRingAt hY.isIrreducible P ≃ₐ[k] Localization.AtPrime p :=
    localRingAtEquivLocalizationAtPrime hY P B eB p hP'
  have hcurve :
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).IsCurve := by
    change dim Y = 1
    rw [dim_eq_ringKrullDim_coordinateRing hY.isAlgebraicSet,
      ringKrullDim_eq_of_ringEquiv eB.toRingEquiv, hdim]
  have hnfield : ¬ IsField B := fun hB ↦
    zero_ne_one ((ringKrullDim_eq_zero_of_isField hB).symm.trans hdim)
  have hns :
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).Nonsingular := by
    intro Q
    rw [Variety.NonsingularAt]
    let Q' : Y := affinePoint hY.isQuasiAffineVariety Q
    let q : Ideal B := Ideal.map eB.toRingHom (maximalIdealAt Y Q')
    let _ : q.IsMaximal := by
      dsimp [q]
      exact (maximalIdealAt_isMaximal Q').map_bijective
        eB.toRingHom eB.bijective
    let _ : q.IsPrime := (show q.IsMaximal from inferInstance).isPrime
    have hQ : maximalIdealAt Y Q' = Ideal.comap eB.toRingHom q := by
      dsimp [q]
      exact (Ideal.comap_map_of_bijective eB.toRingHom eB.bijective).symm
    have hq : q ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField
        (show q.IsMaximal from inferInstance) hnfield
    let _ : IsDiscreteValuationRing (Localization.AtPrime q) :=
      dedekind_localization_dvr B hdim q hq
    let eQ : LocalRingAt hY.isIrreducible Q' ≃ₐ[k]
        Localization.AtPrime q :=
      localRingAtEquivLocalizationAtPrime hY Q' B eB q hQ
    let eAbstract :
        (Variety.ofQuasiAffine hY.isQuasiAffineVariety).LocalRingAt Q ≃+*
          Localization.AtPrime q :=
      (localRingEquivAffine hY.isQuasiAffineVariety Q).trans eQ.toRingEquiv
    exact (isRegularLocalRing_iff_of_ringEquiv eAbstract).mpr inferInstance
  have hideal : Ideal.map eB.toRingHom (maximalIdealAt Y P) = p := by
    rw [hP']
    exact Ideal.map_comap_of_surjective eB.toRingHom eB.surjective p
  have hcoord : ∀ a : coordinateRing Y,
      eK (coordToRational hY.isIrreducible a) =
        algebraMap B K (eB a) := by
    intro a
    change eK (algebraMap (coordinateRing Y)
      (FunctionField hY.isIrreducible) a) = algebraMap B K (eB a)
    exact IsFractionRing.algEquivOfAlgEquiv_algebraMap eB a
  have hlocal : ∀ z : LocalRingAt hY.isIrreducible P,
      eK (localToFunctionField hY.isIrreducible P z) =
        localizationAtPrimeToFractionField (k := k) B K p (eP z) := by
    let f : LocalRingAt hY.isIrreducible P →ₐ[k] K :=
      eK.toAlgHom.comp (affineLocalToFunctionFieldAlgHom hY P)
    let g : LocalRingAt hY.isIrreducible P →ₐ[k] K :=
      (localizationAtPrimeToFractionField (k := k) B K p).comp eP.toAlgHom
    let e0 := localizationEquivLocalRingAlg hY P
    have hcomp :
        f.comp e0.toAlgHom = g.comp e0.toAlgHom := by
      apply IsLocalization.algHom_ext (maximalIdealAt Y P).primeCompl
      apply DFunLike.ext _ _
      intro a
      simp only [AlgHom.comp_apply]
      change f
          (e0 (algebraMap (coordinateRing Y)
            (Localization.AtPrime (maximalIdealAt Y P)) a)) =
        g (e0 (algebraMap (coordinateRing Y)
          (Localization.AtPrime (maximalIdealAt Y P)) a))
      rw [localizationEquivLocalRingAlg_algebraMap]
      change eK
          (localToFunctionField hY.isIrreducible P
            (coordToLocal hY.isIrreducible P a)) =
        localizationAtPrimeToFractionField (k := k) B K p
          (eP (coordToLocal hY.isIrreducible P a))
      rw [localToFunctionField_coordToLocal hY.isQuasiAffineVariety P a,
        localRingAtEquivLocalizationAtPrime_coordToLocal hY P B eB p hP' a,
        localizationAtPrimeToFractionField_algebraMap (k := k) B K p (eB a)]
      exact IsFractionRing.algEquivOfAlgEquiv_algebraMap eB a
    intro z
    have hz := DFunLike.congr_fun hcomp (e0.symm z)
    simpa [f, g, e0] using hz
  exact ⟨n, Y, hY, P, eB, eK, eP, hcurve, hns, hideal, hcoord, hlocal⟩

end Hartshorne
