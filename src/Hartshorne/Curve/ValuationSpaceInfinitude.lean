/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.Cofinite
import Hartshorne.Curve.DedekindAffineModel
import Hartshorne.Curve.SeparableNormalizationCharts
import Hartshorne.Curve.ValuationSpaceTopology
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Infinitude of the valuation space

Hartshorne, *Algebraic Geometry*, I.6 (p. 42).

The discrete valuation rings of a one-dimensional function field form an
infinite set.  We obtain infinitely many of them from the height-one primes of
one Dedekind normalization chart.  The cofinite topology on this set is
therefore irreducible, and all its nonempty open subsets are infinite.
-/

namespace Hartshorne

open IsDedekindDomain MvPolynomial Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u v

/-- Points are closed in affine space with its Zariski topology. -/
private theorem isClosed_singleton_affineSpace
    {k : Type u} [Field k] {σ : Type*} (x : σ → k) :
    IsClosed ({x} : Set (σ → k)) := by
  rw [isClosed_iff_isAlgebraicSet]
  refine ⟨Set.range (fun i : σ ↦ X i - C (x i)), ?_⟩
  ext y
  constructor
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    intro f
    rintro ⟨i, rfl⟩
    simp
  · intro hy
    rw [Set.mem_singleton_iff]
    funext i
    have hi := hy (X i - C (x i)) ⟨i, rfl⟩
    exact sub_eq_zero.mp (by simpa using hi)

namespace FunctionFieldDVR

variable {k : Type u} {B : Type*} {K : Type v}
variable [Field k] [CommRing B] [Field K] [Algebra k B] [Algebra B K]
variable [Algebra k K] [IsScalarTower k B K]

/-- The embedded localization at a height-one prime, regarded as a
function-field DVR. -/
private noncomputable def ofHeightOne
    [IsDedekindDomain B] [IsFractionRing B K]
    (p : HeightOneSpectrum B) : FunctionFieldDVR k K := by
  let _ : IsDiscreteValuationRing
      (HeightOneSpectrum.valuationSubringAtPrime K p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      B p.ne_bot _
  refine ⟨HeightOneSpectrum.valuationSubringAtPrime K p, inferInstance, ?_⟩
  intro c
  rw [IsScalarTower.algebraMap_apply k B K]
  exact (algebraMap B (HeightOneSpectrum.valuationSubringAtPrime K p)
    (algebraMap k B c)).2

/-- Distinct height-one primes give distinct embedded valuation subrings. -/
private theorem ofHeightOne_injective
    [IsDedekindDomain B] [IsFractionRing B K] :
    Function.Injective (ofHeightOne (k := k) (K := K) (B := B)) := by
  intro p q hpq
  apply HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
  rw [Valuation.isEquiv_iff_valuationSubring]
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact congrArg (fun R : FunctionFieldDVR k K ↦ R.toValuationSubring) hpq

/-- A finite-type Dedekind domain of dimension one has infinitely many
height-one primes.  We prove this through its nonsingular affine model. -/
private theorem infinite_heightOneSpectrum_of_affine_model
    [IsAlgClosed k] [IsDedekindDomain B] [Algebra.FiniteType k B]
    [IsFractionRing B K] (hdim : ringKrullDim B = 1) :
    Infinite (HeightOneSpectrum B) := by
  obtain ⟨p, hp⟩ := Ideal.exists_maximal B
  let _ : p.IsMaximal := hp
  obtain ⟨n, Y, hY, _, eB, _, _, hcurve, _, _, _, _⟩ :=
    exists_dedekind_affine_model (k := k) B K hdim p
  let _ : T1Space (Fin n → k) := ⟨isClosed_singleton_affineSpace⟩
  let _ : Infinite Y := infinite_of_topologicalKrullDim_eq_one Y hcurve
  have hnfield : ¬ IsField B := fun hB ↦
    zero_ne_one ((ringKrullDim_eq_zero_of_isField hB).symm.trans hdim)
  let pointPrime (P : Y) : HeightOneSpectrum B := by
    let q := Ideal.map eB.toRingHom (maximalIdealAt Y P)
    have hq : q.IsMaximal :=
      (maximalIdealAt_isMaximal P).map_bijective eB.toRingHom eB.bijective
    exact ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq hnfield⟩
  apply Infinite.of_injective pointPrime
  intro P Q hPQ
  apply maximalIdealAt_injective
  have hmap := congrArg HeightOneSpectrum.asIdeal hPQ
  have hcomap := congrArg (Ideal.comap eB.toRingHom) hmap
  dsimp [pointPrime] at hcomap
  calc
    maximalIdealAt Y P =
        (Ideal.map eB.toRingEquiv.toRingHom
          (maximalIdealAt Y P)).comap eB.toRingEquiv.toRingHom :=
      (Ideal.comap_map_of_bijective eB.toRingEquiv.toRingHom
        eB.bijective).symm
    _ = (Ideal.map eB.toRingEquiv.toRingHom
          (maximalIdealAt Y Q)).comap eB.toRingEquiv.toRingHom := hcomap
    _ = maximalIdealAt Y Q :=
      Ideal.comap_map_of_bijective eB.toRingEquiv.toRingHom eB.bijective

/-- **Hartshorne I.6.** The set of discrete valuation rings of a
one-dimensional function field over an algebraically closed field is
infinite. -/
theorem infinite_of_trdeg_eq_one [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1) :
    Infinite (FunctionFieldDVR k K) := by
  let C := separableNormalizationCharts k K htrdeg
  let _ : Infinite (HeightOneSpectrum C.atZero.normalization) :=
    infinite_heightOneSpectrum_of_affine_model
      (k := k) (B := C.atZero.normalization) (K := K)
      C.atZero.ringKrullDim_normalization
  exact Infinite.of_injective
    (ofHeightOne (k := k) (K := K) (B := C.atZero.normalization))
    ofHeightOne_injective

end FunctionFieldDVR

namespace ValuationSpace

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- The cofinite valuation space of a one-dimensional function field is
irreducible. -/
theorem irreducibleSpace_of_trdeg_eq_one [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1) :
    IrreducibleSpace (ValuationSpace k K) := by
  let _ : Infinite (FunctionFieldDVR k K) :=
    FunctionFieldDVR.infinite_of_trdeg_eq_one htrdeg
  infer_instance

/-- Every nonempty open subset of the cofinite valuation space of a
one-dimensional function field is infinite. -/
theorem infinite_of_isOpen_of_nonempty [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    {U : Set (ValuationSpace k K)} (hU : IsOpen U) (hne : U.Nonempty) :
    U.Infinite := by
  let _ : Infinite (FunctionFieldDVR k K) :=
    FunctionFieldDVR.infinite_of_trdeg_eq_one htrdeg
  have hfinite : Uᶜ.Finite :=
    (ValuationSpace.isOpen_iff_nonempty_imp_compl_finite k K).mp hU hne
  simpa only [compl_compl] using hfinite.infinite_compl

end ValuationSpace

end


end Hartshorne
