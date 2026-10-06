/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# A cotangent criterion for surjectivity of a local homomorphism

Hartshorne II.7, Lemma 7.4: a finite local map of Noetherian local rings is
surjective when it induces an isomorphism on residue fields and a surjection
on cotangent spaces.
-/

namespace Hartshorne

open IsLocalRing

universe u v

/-- The map `𝔪_A ⟶ 𝔪_B / 𝔪_B²` induced by a local homomorphism `A ⟶ B`. -/
noncomputable def maximalIdealToCotangent
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] :
    maximalIdeal A →ₗ[A] CotangentSpace B :=
  Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
      (Ideal.map_le_iff_le_comap.mp
        (IsLocalRing.map_maximalIdeal_le (algebraMap A B))) ∘ₗ
    (maximalIdeal A).toCotangent

/-- **Hartshorne II.7, Lemma 7.4.** A finite local homomorphism from a
Noetherian local ring is surjective if it induces an isomorphism on residue
fields and a surjection from the maximal ideal onto the target cotangent
space. -/
theorem localRingHom_surjective_of_residueField_bijective_of_cotangent_surjective
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap A B)))
    (hcot : Function.Surjective (maximalIdealToCotangent A B)) :
    Function.Surjective (algebraMap A B) := by
  let _ : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let J : Ideal B := (maximalIdeal A).map (algebraMap A B)
  let M : Submodule B (maximalIdeal B) :=
    Submodule.comap (maximalIdeal B).subtype J
  have hM : M = ⊤ := by
    apply IsLocalRing.CotangentSpace.map_eq_top_iff.mp
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hx⟩ := hcot y
    let z : maximalIdeal B :=
      ⟨algebraMap A B x, map_nonunit (algebraMap A B) x x.2⟩
    have hz : z ∈ M := by
      change z.1 ∈ J
      exact Ideal.mem_map_of_mem (algebraMap A B) x.2
    refine Submodule.mem_map.mpr ⟨z, hz, ?_⟩
    simpa [maximalIdealToCotangent, z] using hx
  have hmB_le : maximalIdeal B ≤ J := by
    intro b hb
    have hb' : (⟨b, hb⟩ : maximalIdeal B) ∈ M := by
      rw [hM]
      trivial
    change b ∈ J at hb'
    exact hb'
  have hJ : J = maximalIdeal B :=
    le_antisymm (IsLocalRing.map_maximalIdeal_le (algebraMap A B)) hmB_le
  let N : Submodule A B := LinearMap.range (Algebra.linearMap A B)
  have htop : (⊤ : Submodule A B) ≤
      N ⊔ maximalIdeal A • (⊤ : Submodule A B) := by
    intro b _
    obtain ⟨k, hk⟩ := hres.2 (IsLocalRing.residue B b)
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective k
    have haB : algebraMap A (ResidueField B) a = IsLocalRing.residue B b := by
      calc
        algebraMap A (ResidueField B) a =
            IsLocalRing.ResidueField.map (algebraMap A B) (IsLocalRing.residue A a) := rfl
        _ = IsLocalRing.ResidueField.map (algebraMap A B) k := congrArg _ ha
        _ = IsLocalRing.residue B b := hk
    have hdiff : b - algebraMap A B a ∈ maximalIdeal B := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [map_sub]
      change IsLocalRing.residue B b - algebraMap A (ResidueField B) a = 0
      rw [haB, sub_self]
    have hdiff' : b - algebraMap A B a ∈
        maximalIdeal A • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]
      change b - algebraMap A B a ∈ J
      simpa [hJ] using hdiff
    rw [show b = algebraMap A B a + (b - algebraMap A B a) by abel]
    exact Submodule.add_mem _
      ((le_sup_left : N ≤ N ⊔ maximalIdeal A • (⊤ : Submodule A B)) ⟨a, rfl⟩)
      ((le_sup_right : maximalIdeal A • (⊤ : Submodule A B) ≤
        N ⊔ maximalIdeal A • (⊤ : Submodule A B)) hdiff')
  have hjac : maximalIdeal A ≤ Ideal.jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
  have hle : (⊤ : Submodule A B) ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      Module.Finite.fg_top hjac htop
  exact LinearMap.range_eq_top.mp (eq_top_iff.mpr hle)

end Hartshorne
