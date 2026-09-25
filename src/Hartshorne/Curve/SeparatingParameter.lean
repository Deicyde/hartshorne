/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.SeparablyGenerated

/-!
# Separating parameters for one-dimensional function fields

Hartshorne, *Algebraic Geometry*, I.4, Theorem 4.8A (p. 27), and I.6,
Lemma 6.5 (p. 41).

An essentially finitely generated field extension of transcendence degree one
over an algebraically closed field has a transcendental parameter over which
it is finite and separable. The parameter and its inverse generate the same
intermediate field.
-/

namespace Hartshorne

open IntermediateField

universe u v

/-- An element and its inverse generate the same intermediate field. -/
theorem adjoin_inv_eq_adjoin
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] (t : K) :
    adjoin k ({t⁻¹} : Set K) = adjoin k ({t} : Set K) := by
  apply le_antisymm
  · rw [adjoin_simple_le_iff]
    exact (adjoin k ({t} : Set K)).inv_mem (mem_adjoin_simple_self k t)
  · rw [adjoin_simple_le_iff]
    simpa using
      (adjoin k ({t⁻¹} : Set K)).inv_mem (mem_adjoin_simple_self k t⁻¹)

/-- A one-dimensional function field over an algebraically closed field has a
transcendental parameter over which it is finite and separable. -/
theorem exists_separatingParameter
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) :
    ∃ t : K,
      Transcendental k t ∧
      FiniteDimensional (adjoin k ({t} : Set K)) K ∧
      Algebra.IsSeparable (adjoin k ({t} : Set K)) K ∧
      adjoin k ({t⁻¹} : Set K) = adjoin k ({t} : Set K) := by
  classical
  obtain ⟨s, _, hs, hsep, hfinite, _, hcard⟩ :=
    exists_separatingTranscendenceBasis_and_primitiveElement k K
  have hs_card : s.card = 1 := by
    exact_mod_cast hcard.trans htrdeg
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hs_card
  have hset : ((↑({t} : Finset K)) : Set K) = ({t} : Set K) :=
    Finset.coe_singleton t
  rw [hset] at hsep hfinite
  refine ⟨t, ?_, hfinite, hsep, adjoin_inv_eq_adjoin k K t⟩
  simpa using hs.1.transcendental ⟨t, by simp⟩

end Hartshorne
