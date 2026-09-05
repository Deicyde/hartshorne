/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.HomAffine
import Hartshorne.Morphism.GlobalRegularTop

/-!
# Corollary 3.7: affine varieties are classified by their coordinate rings

Hartshorne, *Algebraic Geometry*, I.3, Corollary 3.7 (p. 20).

Two affine varieties are isomorphic if and only if their coordinate rings are
isomorphic as `k`-algebras.

Both directions run through the same identity: the map of Proposition 3.5 is
pullback of regular functions composed with `A(Y) ≅ 𝒪(Y)`. Since pullback is
contravariantly functorial, an isomorphism of varieties gives a two-sided
inverse pair of algebra maps directly, and conversely an isomorphism of algebras
gives morphisms both ways whose composites correspond, under the bijection of
Proposition 3.5, to the identities.

The "conversely" is where the trap in the definition of isomorphism is paid for.
Exercise 3.2 shows a bijective bicontinuous morphism need not be an isomorphism,
so producing a two-sided *inverse morphism* is the whole content, and it is
Proposition 3.5 that produces one.

## Main results

* `Hartshorne.homToAlgHom_eq_pullback_comp`
* `Hartshorne.nonempty_isIso_iff_nonempty_algEquiv`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The map of Proposition 3.5 is pullback of regular functions, precomposed
with `A(Y) ≅ 𝒪(Y)`.

This is what makes Proposition 3.5 functorial, and it is the only thing
Corollary 3.7 needs from the construction. -/
theorem homToAlgHom_eq_pullback_comp {σ : Type v} [Finite σ] {Y : Set (σ → k)}
    {X : Variety k} (hY : IsAffineVariety Y)
    (ρ : VarietyHom X (Variety.ofQuasiAffine hY.isQuasiAffineVariety)) :
    homToAlgHom hY ρ = ρ.pullback.comp (coordinateRingEquivRegularTop hY).toAlgHom :=
  AlgHom.ext fun _ => Subtype.ext (funext fun _ => rfl)

variable {σ τ : Type v} [Finite σ] [Finite τ] {X : Set (σ → k)} {Y : Set (τ → k)}

/-- **Corollary 3.7**: affine varieties are isomorphic exactly when their
coordinate rings are. -/
theorem nonempty_isIso_iff_nonempty_algEquiv (hX : IsAffineVariety X)
    (hY : IsAffineVariety Y) :
    (∃ ρ : VarietyHom (Variety.ofQuasiAffine hX.isQuasiAffineVariety)
        (Variety.ofQuasiAffine hY.isQuasiAffineVariety), ρ.IsIso) ↔
      Nonempty (coordinateRing X ≃ₐ[k] coordinateRing Y) := by
  constructor
  · rintro ⟨ρ, τ', hτρ, hρτ⟩
    -- Pullback is functorial, so the two pullbacks are mutually inverse.
    have h₁ : ρ.pullback.comp τ'.pullback = AlgHom.id k _ := by
      rw [← VarietyHom.pullback_comp, hτρ, VarietyHom.pullback_id]
    have h₂ : τ'.pullback.comp ρ.pullback = AlgHom.id k _ := by
      rw [← VarietyHom.pullback_comp, hρτ, VarietyHom.pullback_id]
    exact ⟨(((coordinateRingEquivRegularTop hY).trans
      (AlgEquiv.ofAlgHom ρ.pullback τ'.pullback h₁ h₂)).trans
      (coordinateRingEquivRegularTop hX).symm).symm⟩
  · rintro ⟨Φ⟩
    -- Transport `Φ` through Theorem 3.2(a) and Proposition 3.5 in both
    -- directions.
    set EX := coordinateRingEquivRegularTop hX with hEX
    set EY := coordinateRingEquivRegularTop hY with hEY
    set ρ := (homEquivAlgHom hY).symm (EX.toAlgHom.comp Φ.symm.toAlgHom) with hρ
    set τ' := (homEquivAlgHom hX).symm (EY.toAlgHom.comp Φ.toAlgHom) with hτ
    -- What each morphism does to regular functions, read off Proposition 3.5.
    have hpρ : ρ.pullback.comp EY.toAlgHom = EX.toAlgHom.comp Φ.symm.toAlgHom := by
      rw [← homToAlgHom_eq_pullback_comp hY ρ, hρ]
      exact (homEquivAlgHom hY).apply_symm_apply _
    have hpτ : τ'.pullback.comp EX.toAlgHom = EY.toAlgHom.comp Φ.toAlgHom := by
      rw [← homToAlgHom_eq_pullback_comp hX τ', hτ]
      exact (homEquivAlgHom hX).apply_symm_apply _
    refine ⟨ρ, τ', ?_, ?_⟩
    · -- `τ' ∘ ρ = id` because both sides have the same image under 3.5.
      refine (homEquivAlgHom hX).injective ?_
      show homToAlgHom hX (τ'.comp ρ) = homToAlgHom hX (VarietyHom.id _)
      rw [homToAlgHom_eq_pullback_comp hX (τ'.comp ρ),
        homToAlgHom_eq_pullback_comp hX (VarietyHom.id _),
        VarietyHom.pullback_comp, VarietyHom.pullback_id, AlgHom.id_comp,
        AlgHom.comp_assoc, hpτ, ← AlgHom.comp_assoc, hpρ, AlgHom.comp_assoc]
      simp [hEX]
    · refine (homEquivAlgHom hY).injective ?_
      show homToAlgHom hY (ρ.comp τ') = homToAlgHom hY (VarietyHom.id _)
      rw [homToAlgHom_eq_pullback_comp hY (ρ.comp τ'),
        homToAlgHom_eq_pullback_comp hY (VarietyHom.id _),
        VarietyHom.pullback_comp, VarietyHom.pullback_id, AlgHom.id_comp,
        AlgHom.comp_assoc, hpρ, ← AlgHom.comp_assoc, hpτ, AlgHom.comp_assoc]
      simp [hEY]

end Hartshorne
