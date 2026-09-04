/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Krull dimension under integral extensions

Toward Hartshorne, *Algebraic Geometry*, I.1, Theorem 1.8A(a).

Hartshorne quotes `dim B = trdeg_k K(B)` for a finitely generated `k`-algebra
domain without proof. The standard route is Noether normalisation — `B` is
finite over a polynomial subring `k[y₁,…,y_s]` — plus the fact that an integral
extension does not change the Krull dimension. Mathlib has Noether
normalisation and the dimension of a polynomial ring, but not that last fact.

This file supplies the inequality that follows directly from incomparability:
a strict inclusion of primes upstairs contracts to a strict inclusion
downstairs, so contraction is strictly monotone on prime spectra and dimension
cannot go up.

The reverse inequality needs going-up to lift a chain rather than contract one,
which is a construction rather than a map, and is not done here.

## Main results

* `Hartshorne.ringKrullDim_le_of_isIntegral`
-/

namespace Hartshorne

open Ideal

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Contraction along an integral extension is strictly monotone on prime
spectra.

This is incomparability: two distinct comparable primes upstairs cannot have the
same contraction. -/
theorem strictMono_primeSpectrum_comap [Algebra.IsIntegral R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro p q hpq
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hpq ⊢
  exact Ideal.IsIntegral.comap_lt_comap hpq

/-- An integral extension cannot increase the Krull dimension.

Half of the fact Hartshorne's Theorem 1.8A rests on. Mathlib has the
ingredients — `IsIntegral.comap_lt_comap` for incomparability and
`krullDim_le_of_strictMono` — but not the conclusion. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono _ (strictMono_primeSpectrum_comap R S)

end Hartshorne
