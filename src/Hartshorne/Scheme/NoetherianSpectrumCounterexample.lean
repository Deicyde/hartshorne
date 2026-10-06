/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.NoetherianSpace

/-!
# A non-Noetherian ring with Noetherian spectrum

The trivial square-zero extension of `ℚ` by the countably generated free
`ℚ`-module has a one-point prime spectrum, but an infinite strictly
increasing chain of ideals.
-/

open TopologicalSpace

namespace Hartshorne

noncomputable section

private abbrev noetherianSpectrumCounterexampleRing :=
  TrivSqZeroExt ℚ (ℕ →₀ ℚ)

private def noetherianSpectrumGenerator (n : ℕ) :
    noetherianSpectrumCounterexampleRing :=
  TrivSqZeroExt.inr (Finsupp.single n 1)

private def noetherianSpectrumIdeal (n : ℕ) :
    Ideal noetherianSpectrumCounterexampleRing :=
  Ideal.span (noetherianSpectrumGenerator '' Set.Iio n)

private def noetherianSpectrumIdealChain :
    ℕ →o Ideal noetherianSpectrumCounterexampleRing where
  toFun := noetherianSpectrumIdeal
  monotone' := by
    intro m n hmn
    apply Ideal.span_mono
    apply Set.image_mono
    intro i hi
    exact lt_of_lt_of_le hi hmn

private lemma noetherianSpectrumIdealChain_strict (n : ℕ) :
    noetherianSpectrumIdealChain n <
      noetherianSpectrumIdealChain (n + 1) := by
  have hle : noetherianSpectrumIdealChain n ≤
      noetherianSpectrumIdealChain (n + 1) :=
    noetherianSpectrumIdealChain.monotone (Nat.le_succ n)
  have hmem : noetherianSpectrumGenerator n ∈
      noetherianSpectrumIdealChain (n + 1) := by
    apply Ideal.subset_span
    exact ⟨n, Nat.lt_succ_self n, rfl⟩
  have hnot : noetherianSpectrumGenerator n ∉
      noetherianSpectrumIdealChain n := by
    let φ := (TrivSqZeroExt.map
      (Finsupp.lapply n : (ℕ →₀ ℚ) →ₗ[ℚ] ℚ)).toRingHom
    have hker : noetherianSpectrumIdealChain n ≤ RingHom.ker φ := by
      rw [show noetherianSpectrumIdealChain n =
        Ideal.span (noetherianSpectrumGenerator '' Set.Iio n) from rfl]
      rw [Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      change φ (noetherianSpectrumGenerator i) = 0
      simp [φ, noetherianSpectrumGenerator, Finsupp.lapply_apply,
        Nat.ne_of_lt hi]
    intro hn
    have hzero := hker hn
    rw [RingHom.mem_ker] at hzero
    have hsnd := congrArg
      (TrivSqZeroExt.snd (R := ℚ) (M := ℚ)) hzero
    simp [φ, noetherianSpectrumGenerator, Finsupp.lapply_apply] at hsnd
  exact lt_of_le_of_ne hle (fun h ↦ hnot (h ▸ hmem))

private theorem noetherianSpectrumCounterexample_not_noetherian :
    ¬ IsNoetherianRing noetherianSpectrumCounterexampleRing := by
  intro h
  let _ : IsNoetherianRing noetherianSpectrumCounterexampleRing := h
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (show IsNoetherian noetherianSpectrumCounterexampleRing
      noetherianSpectrumCounterexampleRing from inferInstance)
    noetherianSpectrumIdealChain
  exact (noetherianSpectrumIdealChain_strict n).ne
    (hn (n + 1) (Nat.le_succ n))

private theorem noetherianSpectrumCounterexample_primeSpectrum_subsingleton :
    Subsingleton (PrimeSpectrum noetherianSpectrumCounterexampleRing) := by
  constructor
  intro P Q
  apply PrimeSpectrum.ext
  ext x
  have mem_iff (p : PrimeSpectrum noetherianSpectrumCounterexampleRing) :
      x ∈ p.asIdeal ↔ x.fst = 0 := by
    constructor
    · intro hx
      by_contra hfst
      have hunitFst : IsUnit x.fst := isUnit_iff_ne_zero.mpr hfst
      have hunit : IsUnit x :=
        TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hunitFst
      exact (Ideal.notMem_of_isUnit p.asIdeal hunit) hx
    · intro hfst
      apply p.isPrime.mem_of_pow_mem 2
      have hsquare : x ^ 2 = 0 := by
        rw [pow_two]
        apply TrivSqZeroExt.ext
        · simp [hfst]
        · simp [hfst]
      rw [hsquare]
      exact p.asIdeal.zero_mem
  exact (mem_iff P).trans (mem_iff Q).symm

/-- There exists a non-Noetherian commutative ring whose prime spectrum is a
Noetherian topological space. -/
theorem exists_not_isNoetherianRing_and_noetherianSpace_primeSpectrum :
    ∃ A : CommRingCat,
      ¬ IsNoetherianRing (A : Type) ∧
        NoetherianSpace (PrimeSpectrum (A : Type)) := by
  let A : CommRingCat := CommRingCat.of noetherianSpectrumCounterexampleRing
  refine ⟨A, noetherianSpectrumCounterexample_not_noetherian, ?_⟩
  let _ : Subsingleton (PrimeSpectrum (A : Type)) :=
    noetherianSpectrumCounterexample_primeSpectrum_subsingleton
  let _ : Finite (PrimeSpectrum (A : Type)) :=
    Finite.of_injective (fun _ : PrimeSpectrum (A : Type) ↦ PUnit.unit)
      (Function.injective_of_subsingleton _)
  infer_instance

end

end Hartshorne
