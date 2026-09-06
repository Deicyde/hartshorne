/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Height is preserved by contraction along an integral extension

Toward Hartshorne, *Algebraic Geometry*, I.1, Theorem 1.8A(b).

For `R ⊆ S` integral with `R` an integrally closed domain and `S` a domain,
a prime of `S` has the same height as its contraction to `R`.

This is what lets the dimension formula move a prime of an affine domain down to
a Noether normalisation, where it becomes a prime of a polynomial ring and can
be handled by unique factorisation.

The two inequalities come from the two halves of the classical picture.
Contracting a chain below `P` gives a chain below `P ∩ R` which is still
strictly increasing, because primes of an integral extension lying over
comparable primes are comparable only if they are equal; that is
`Ideal.IsIntegral.comap_lt_comap`. Conversely a chain below `P ∩ R` lifts to one
below `P`, which is going down — supplied by Mathlib for an integral extension
of an integrally closed domain.

Going down was expected to be the large missing prerequisite here. It is not:
Mathlib has the instance, and the only work left was to assemble it with
incomparability into the height statement.

## Main results

* `Hartshorne.height_comap_eq_height_of_isIntegral`
-/

namespace Hartshorne

open Ideal

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Contracting a chain of primes along an integral extension keeps it strictly
increasing, so the contraction has at least the height. -/
theorem height_le_height_comap_of_isIntegral [Algebra.IsIntegral R S]
    (P : Ideal S) [P.IsPrime] [P.FiniteHeight] :
    P.height ≤ (P.comap (algebraMap R S)).height := by
  obtain ⟨l, hlast, hlen⟩ := P.exists_ltSeries_length_eq_height
  have hmono : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
    intro x y hxy
    exact Ideal.IsIntegral.comap_lt_comap hxy
  have hL := Order.length_le_height_last (p := l.map _ hmono)
  rw [show (l.map _ hmono).last = PrimeSpectrum.comap (algebraMap R S) l.last from rfl,
    hlast, ← PrimeSpectrum.height_eq_orderHeight] at hL
  rw [← hlen]
  exact hL

/-- Going down lifts a chain below the contraction to one below `P`, so the
height is at least that of the contraction. -/
theorem height_comap_le_height_of_hasGoingDown [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] [(P.comap (algebraMap R S)).FiniteHeight] :
    (P.comap (algebraMap R S)).height ≤ P.height := by
  obtain ⟨l, hlast, hlen⟩ := (P.comap (algebraMap R S)).exists_ltSeries_length_eq_height
  have _ : P.LiesOver l.last.asIdeal := ⟨by rw [hlast]⟩
  obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  have hle := Order.length_le_height_last (p := L)
  rw [hLlast, ← PrimeSpectrum.height_eq_orderHeight] at hle
  rw [← hlen, ← hLlen]
  exact hle

/-- **Height is preserved by contraction along an integral extension of an
integrally closed domain.** -/
theorem height_comap_eq_height_of_isIntegral [IsDomain S] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] [IsIntegrallyClosed R]
    (P : Ideal S) [P.IsPrime] [P.FiniteHeight] [(P.comap (algebraMap R S)).FiniteHeight] :
    (P.comap (algebraMap R S)).height = P.height :=
  le_antisymm (height_comap_le_height_of_hasGoingDown R S P)
    (height_le_height_comap_of_isIntegral R S P)

end Hartshorne
