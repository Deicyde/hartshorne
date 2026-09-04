/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.HasGoingUp
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

This file supplies both inequalities.

One direction is incomparability: a strict inclusion of primes upstairs
contracts to a strict inclusion downstairs, so contraction is strictly monotone
on prime spectra and the dimension cannot go up. That needs no hypothesis beyond
integrality.

The other direction is lying over and going up. A chain downstairs is *lifted*
rather than contracted, so it is a construction by induction on the chain, not a
map; Mathlib packages exactly that induction as
`Ideal.exists_ltSeries_of_hasGoingUp`, and integral algebras satisfy going up.
Lying over supplies the prime above the head of the chain, and it is the step
that needs the extension to be injective — the surjection `S → S/𝔭` is integral
but drops the dimension.

## Main results

* `Hartshorne.ringKrullDim_le_of_isIntegral`
* `Hartshorne.le_ringKrullDim_of_isIntegral`
* `Hartshorne.ringKrullDim_eq_of_isIntegral`
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

/-- An injective integral extension cannot decrease the Krull dimension.

Given a chain of primes in `R`, lying over produces a prime of `S` above its
smallest term, and going up extends that to a chain in `S` of the same length.

Injectivity is needed and not decoration: `S → S/𝔭` is integral for every prime
`𝔭`, and quotienting by a maximal ideal takes any positive dimension to `0`. -/
theorem le_ringKrullDim_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  refine iSup_le fun l => ?_
  -- Lying over: some prime of `S` sits above the bottom of the chain.
  obtain ⟨P, hPprime, hPover⟩ := Classical.arbitrary (Ideal.primesOver l.head.asIdeal S)
  have := hPprime
  have := hPover
  -- Going up: extend it along the chain, keeping the length.
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp (S := S) l P
  rw [← hlen]
  exact Order.LTSeries.length_le_krullDim L

/-- **Krull dimension is invariant under injective integral extensions.**

This is the fact Hartshorne's Theorem 1.8A rests on but does not state: combined
with Noether normalisation it computes the dimension of any finitely generated
algebra over a field. -/
theorem ringKrullDim_eq_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R :=
  le_antisymm (ringKrullDim_le_of_isIntegral R S) (le_ringKrullDim_of_isIntegral R S)

end Hartshorne
