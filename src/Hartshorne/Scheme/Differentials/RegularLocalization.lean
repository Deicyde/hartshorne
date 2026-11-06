/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RegularLocalCohenMacaulay

/-!
# Localizations of regular local rings: the elementary cases

Hartshorne, *Algebraic Geometry*, II, Theorem 8.14A, p. 177 (Matsumura, p. 139; Stacks,
tag 0AFS): if `A` is a regular local ring and `𝔭` is a prime ideal of `A`, then `A_𝔭` is a
regular local ring.

This module is **partial progress** towards that theorem; the general statement is not proved
here. Every standard proof is homological (Serre): a regular local ring has finite global
dimension, projective dimension localizes, and a Noetherian local ring whose residue field has
finite projective dimension is regular. The pinned Mathlib provides projective dimension, its
behaviour under localization and under quotients by regular sequences, but neither the
global-dimension bound for regular local rings nor Serre's converse characterization.

What is proved here are the cases that need no homological algebra:

* `𝔭 = 𝔪`: then `A_𝔪 ≅ A`;
* `𝔭 = 0`: a regular local ring is a domain, so `A_(0)` is its fraction field;
* `dim A ≤ 1`: every prime of the domain `A` is then `0` or `𝔪`.

## Main results

* `Hartshorne.RegularLocalization.isRegularLocalRing_localization_atPrime_maximalIdeal`
* `Hartshorne.RegularLocalization.isRegularLocalRing_localization_atPrime_of_eq_bot`
* `Hartshorne.RegularLocalization.isRegularLocalRing_localization_atPrime_of_ringKrullDim_le_one`
-/

open IsLocalRing Ideal

namespace Hartshorne.RegularLocalization

variable {A : Type*} [CommRing A] [IsRegularLocalRing A]

/-- A regular local ring localized at its maximal ideal is regular (it is isomorphic to the ring
itself). -/
theorem isRegularLocalRing_localization_atPrime_maximalIdeal :
    IsRegularLocalRing (Localization.AtPrime (maximalIdeal A)) := by
  let e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun x ↦ by simpa using! fun a ↦ a)
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

/-- The localization of a regular local ring at its zero ideal (a prime, since a regular local
ring is a domain) is a field, hence regular. -/
theorem isRegularLocalRing_localization_atPrime_of_eq_bot (p : Ideal A) [p.IsPrime]
    (hp : p = ⊥) : IsRegularLocalRing (Localization.AtPrime p) := by
  have := Hartshorne.RegularLocal.isDomain A
  let : Field (Localization.AtPrime p) := IsField.toField <| by
    simp [isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal, hp]
  infer_instance

/-- In a regular local ring of dimension at most one, every prime ideal is either zero or the
maximal ideal. -/
theorem eq_bot_or_eq_maximalIdeal_of_ringKrullDim_le_one (p : Ideal A) [p.IsPrime]
    (h : ringKrullDim A ≤ 1) : p = ⊥ ∨ p = maximalIdeal A := by
  have := Hartshorne.RegularLocal.isDomain A
  by_contra hne
  push Not at hne
  have h1 : (⊥ : Ideal A) < p := bot_lt_iff_ne_bot.mpr hne.1
  have h2 : p < maximalIdeal A := lt_of_le_of_ne (le_maximalIdeal (IsPrime.ne_top ‹_›)) hne.2
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have h3 : ((maximalIdeal A).height : WithBot ℕ∞) ≤ 1 :=
    maximalIdeal_height_eq_ringKrullDim (R := A) ▸ h
  rw [Ideal.height_bot, zero_add] at e1
  have : (2 : ℕ∞) ≤ (maximalIdeal A).height := le_trans (by
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p.height + 1 := by gcongr) e2
  have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1 := le_trans (WithBot.coe_le_coe.mpr this) h3
  exact absurd this (by decide)

/-- Hartshorne II, Theorem 8.14A, in the case `dim A ≤ 1`: every prime localization of a regular
local ring of dimension at most one is regular. -/
theorem isRegularLocalRing_localization_atPrime_of_ringKrullDim_le_one (p : Ideal A) [p.IsPrime]
    (h : ringKrullDim A ≤ 1) : IsRegularLocalRing (Localization.AtPrime p) := by
  rcases eq_bot_or_eq_maximalIdeal_of_ringKrullDim_le_one p h with hp | hp
  · exact isRegularLocalRing_localization_atPrime_of_eq_bot p hp
  · subst hp
    exact isRegularLocalRing_localization_atPrime_maximalIdeal

end Hartshorne.RegularLocalization
