/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# One inequality of the dimension formula

Toward Hartshorne, *Algebraic Geometry*, I.1, Theorem 1.8A(b).

Hartshorne quotes `height 𝔭 + dim B/𝔭 = dim B` for a finitely generated
`k`-algebra domain. One inequality holds in any commutative ring and needs no
hypotheses at all: a chain of primes below `𝔭` and a chain above it splice at
`𝔭` into a single chain, so the two lengths add to at most the dimension.

The content is the translation, not the chain argument. Mathlib has the order
theory — `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty` does the
splicing — but the ring-theoretic statement needs `dim R/𝔭` identified with the
coheight of `𝔭`, and that identification is not upstream. It comes from
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus`, once one observes that the zero
locus of a prime is its up-set.

The reverse inequality is the catenary property and is genuinely hard; it fails
for general Noetherian rings and needs finite generation over a field.

## Main results

* `Hartshorne.ringKrullDim_quotient_eq_coheight`
* `Hartshorne.height_add_ringKrullDim_quotient_le`
-/

namespace Hartshorne

variable {R : Type*} [CommRing R]

/-- The dimension of `R ⧸ 𝔭` is the coheight of `𝔭`.

Primes of the quotient are the primes containing `𝔭`, which is the up-set of
`𝔭` in the prime spectrum, and the coheight of a point is the dimension of its
up-set. -/
theorem ringKrullDim_quotient_eq_coheight (p : Ideal R) [hp : p.IsPrime] :
    ringKrullDim (R ⧸ p) = (Order.coheight (⟨p, hp⟩ : PrimeSpectrum R) : ℕ∞) := by
  have hset : PrimeSpectrum.zeroLocus (R := R) (p : Set R)
      = Set.Ici (⟨p, hp⟩ : PrimeSpectrum R) := by
    ext q
    simp [PrimeSpectrum.mem_zeroLocus, ← PrimeSpectrum.asIdeal_le_asIdeal, Set.mem_Ici]
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso p.primeSpectrumQuotientOrderIsoZeroLocus,
    Order.coheight_eq_krullDim_Ici, hset]

/-- **One inequality of Theorem 1.8A(b)**, valid in any commutative ring:
`height 𝔭 + dim R/𝔭 ≤ dim R`.

A chain below `𝔭` and a chain above it meet at `𝔭` and splice. -/
theorem height_add_ringKrullDim_quotient_le (p : Ideal R) [hp : p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  have hne : Nonempty (PrimeSpectrum R) := ⟨⟨p, hp⟩⟩
  rw [ringKrullDim_quotient_eq_coheight,
    show p.height = Order.height (⟨p, hp⟩ : PrimeSpectrum R) from
      PrimeSpectrum.height_eq_orderHeight ⟨p, hp⟩,
    ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  norm_cast
  exact le_iSup (fun a : PrimeSpectrum R => Order.height a + Order.coheight a) _

end Hartshorne
