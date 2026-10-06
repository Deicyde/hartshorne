/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.Flatness.FlatModulesShortExactCalculus
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Zeroth cohomology of a bounded flat acyclic complex

For a bounded-above cochain complex of flat modules in nonnegative degrees, acyclicity in
positive degrees implies that its zeroth cohomology is flat.
-/

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

universe u v

/-- Let `C` be a bounded-above cochain complex of flat modules, indexed in nonnegative
degrees. If its positive-degree cohomology vanishes, then its zeroth cohomology is flat. -/
theorem boundedFlatAcyclicComplex_homology_zero_flat
    {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{v} R) ℕ)
    (N : ℕ)
    (hbounded : ∀ i, N < i → IsZero (C.X i))
    (hflat : ∀ i, Module.Flat R (C.X i))
    (hacyclic : ∀ i, 0 < i → IsZero (C.homology i)) :
    Module.Flat R (C.homology 0) := by
  have hseq (i : ℕ) :
      Function.Exact (C.iCycles i).hom (C.toCycles i (i + 1)).hom := by
    intro x
    constructor
    · intro hx
      have hdx : C.d i (i + 1) x = 0 := by
        rw [← C.toCycles_i i (i + 1)]
        change C.iCycles (i + 1) (C.toCycles i (i + 1) x) = 0
        rw [hx, map_zero]
      refine ⟨C.cyclesMk x (i + 1) (by simp) hdx, ?_⟩
      exact C.i_cyclesMk x (i + 1) (by simp) hdx
    · rintro ⟨z, rfl⟩
      apply (ModuleCat.mono_iff_injective (C.iCycles (i + 1))).1 inferInstance
      rw [map_zero, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
      rw [C.toCycles_i, C.iCycles_d]
      rfl
  have hsurj (i : ℕ) (h : IsZero (C.homology (i + 1))) :
      Function.Surjective (C.toCycles i (i + 1)).hom := by
    have hexact : C.ExactAt (i + 1) :=
      (C.exactAt_iff_isZero_homology (i + 1)).2 h
    have hsc' : (C.sc' i (i + 1) (i + 2)).Exact :=
      (C.exactAt_iff' i (i + 1) (i + 2) (by simp) (by simp)).1 hexact
    let e := C.cyclesIsoSc' i (i + 1) (i + 2) (by simp) (by simp)
    have hepi : Epi ((C.sc' i (i + 1) (i + 2)).toCycles) := hsc'.epi_toCycles
    have hs : Function.Surjective ((C.sc' i (i + 1) (i + 2)).toCycles).hom :=
      (ModuleCat.epi_iff_surjective _).1 hepi
    intro z
    obtain ⟨x, hx⟩ := hs (e.hom z)
    change C.X i at x
    refine ⟨x, ?_⟩
    apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
    change e.hom (C.toCycles i (i + 1) x) = e.hom z
    rw [← ConcreteCategory.comp_apply,
      C.toCycles_cyclesIsoSc'_hom i (i + 1) (i + 2) (by simp) (by simp)]
    exact hx
  have hbase : Module.Flat R (C.cycles N) := by
    have hz : IsZero (C.X (N + 1)) := hbounded (N + 1) (Nat.lt_succ_self N)
    have hd : C.d N (N + 1) = 0 := hz.eq_of_tgt _ _
    exact (Module.Flat.equiv_iff
      (C.iCyclesIso N (N + 1) (by simp) hd).toLinearEquiv).2 (hflat N)
  have hcycles0 : Module.Flat R (C.cycles 0) :=
    Nat.decreasingInduction (n := N)
      (fun i _ hi ↦
        (flat_shortExact_calculus (C.iCycles i).hom (C.toCycles i (i + 1)).hom
          ((ModuleCat.mono_iff_injective _).1 inferInstance)
          (hsurj i (hacyclic (i + 1) (Nat.succ_pos i))) (hseq i)).2
          ⟨hflat i, hi⟩)
      hbase (Nat.zero_le N)
  exact (Module.Flat.equiv_iff C.isoHomologyπ₀.toLinearEquiv).1 hcycles0

end Hartshorne
