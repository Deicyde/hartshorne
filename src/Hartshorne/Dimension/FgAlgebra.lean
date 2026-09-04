/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.Integral
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# The dimension of a finitely generated algebra over a field

Toward Hartshorne, *Algebraic Geometry*, I.1, Theorem 1.8A(a).

Noether normalisation presents a finitely generated `k`-algebra `R` as an
injective integral extension of a polynomial ring `k[y₁,…,y_s]`. Integral
extensions preserve the Krull dimension (`Hartshorne.ringKrullDim_eq_of_isIntegral`)
and Mathlib computes `dim k[y₁,…,y_s] = s`, so `dim R = s`.

In particular the dimension of a finitely generated algebra over a field is a
natural number: it is neither `⊥` nor `∞`. That finiteness is the part of
Theorem 1.8A that is used constantly and quoted without comment.

Identifying `s` with the transcendence degree of the fraction field, which is
what Hartshorne actually states, is separate and not done here.

## Main results

* `Hartshorne.exists_ringKrullDim_eq_natCast`
* `Hartshorne.finiteRingKrullDim_of_finiteType`
-/

namespace Hartshorne

variable (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
  [Algebra.FiniteType k R]

-- None of the statements below mention `k`, only the proofs do.
include k

/-- **Noether normalisation computes the dimension.**

A finitely generated algebra over a field has the dimension of the polynomial
ring it is integral over, so its dimension is a natural number.

Hartshorne's Theorem 1.8A(a) identifies that number with the transcendence
degree of the fraction field; this is the half that does not need the
identification. -/
theorem exists_ringKrullDim_eq_natCast : ∃ s : ℕ, ringKrullDim R = s := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k R
  refine ⟨s, ?_⟩
  -- View `R` as an algebra over the polynomial ring via the normalisation map.
  let : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) R := ⟨hint⟩
  have : FaithfulSMul (MvPolynomial (Fin s) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) R,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- A finitely generated algebra over a field has finite Krull dimension.

This is the consequence that gets used: every chain of primes is bounded, so
dimension arguments in §1 and §3 never have to worry about `⊤`, and the
dimension is a genuine natural number rather than a `WithBot ℕ∞`.

Not an instance, because `k` cannot be recovered from the conclusion. -/
theorem finiteRingKrullDim_of_finiteType : FiniteRingKrullDim R := by
  obtain ⟨s, hs⟩ := exists_ringKrullDim_eq_natCast k R
  rw [finiteRingKrullDim_iff_ne_bot_and_top, hs]
  refine ⟨?_, ?_⟩
  · rw [← WithBot.coe_natCast]
    exact WithBot.coe_ne_bot
  · rw [← WithBot.coe_natCast, ne_eq, ← WithBot.coe_top, WithBot.coe_inj]
    exact ENat.natCast_ne_top s

end Hartshorne
