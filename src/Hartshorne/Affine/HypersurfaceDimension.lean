/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Nullstellensatz
import Hartshorne.Affine.DimensionCoordinateRing
import Hartshorne.Dimension.AdjoinRootTrdeg
import Hartshorne.Dimension.FgDomain
import Hartshorne.Dimension.DimFormula

/-!
# Hypersurfaces have dimension `n − 1`

Hartshorne, *Algebraic Geometry*, I.1, Proposition 1.13 (p. 7), the forward
direction.

For `f ∈ k[x₁,…,x_n]` irreducible, the hypersurface `Z(f)` has dimension
`n − 1`.

Hartshorne's route is through Krull's Hauptidealsatz: `(f)` is prime of height
one, and the dimension formula converts height one into dimension `n − 1`. The
route taken here is shorter, because the transcendence-degree computation the
dimension formula was itself built on already says what is wanted:

* `I(Z(f)) = (f)`, by the Nullstellensatz, `(f)` being prime and so radical;
* so `A(Z(f)) = k[x]/(f)`, and Proposition 1.7 makes `dim Z(f)` its Krull
  dimension;
* Theorem 1.8A(a) makes that the transcendence degree of its fraction field;
* and cutting by an irreducible drops the transcendence degree by exactly one.

Krull's theorem is not needed at all on this side. It is needed for the
converse, which is not proved here.

## Main results

* `Hartshorne.exists_dim_zeroSet_irreducible`
* `Hartshorne.exists_irreducible_eq_zeroSet`
-/

namespace Hartshorne

open MvPolynomial

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Proposition 1.13**, forward direction: an irreducible polynomial cuts out a
hypersurface of dimension one less than the ambient space. -/
theorem exists_dim_zeroSet_irreducible {n : ℕ} {f : MvPolynomial (Fin n) k}
    (hf : Irreducible f) :
    ∃ m : ℕ, m + 1 = n ∧
      dim (zeroSet ({f} : Set (MvPolynomial (Fin n) k))) = m := by
  classical
  -- `(f)` is prime, hence radical, so it is the vanishing ideal of its zero set.
  have hfne : f ≠ 0 := hf.ne_zero
  haveI hprime : (Ideal.span {f}).IsPrime :=
    (Ideal.span_singleton_prime hfne).2 (UniqueFactorizationMonoid.irreducible_iff_prime.1 hf)
  have hvi : vanishingIdeal k (zeroSet ({f} : Set (MvPolynomial (Fin n) k)))
      = Ideal.span {f} := by
    have hspan : zeroSet ({f} : Set (MvPolynomial (Fin n) k))
        = zeroSet ((Ideal.span {f} : Ideal (MvPolynomial (Fin n) k)) :
          Set (MvPolynomial (Fin n) k)) := by
      rw [zeroSet_eq_zeroLocus_span, zeroLocus_eq_zeroSet]
    rw [hspan, vanishingIdeal_zeroSet_eq_radical, hprime.radical]
  -- So the coordinate ring is the quotient, whose dimension is a transcendence degree.
  obtain ⟨m, hm, htr⟩ := exists_trdeg_quotient_span_irreducible hf
  refine ⟨m, hm, ?_⟩
  have halg : IsAlgebraicSet (zeroSet ({f} : Set (MvPolynomial (Fin n) k))) :=
    ⟨_, rfl⟩
  rw [dim_eq_ringKrullDim_coordinateRing halg]
  have e : coordinateRing (zeroSet ({f} : Set (MvPolynomial (Fin n) k)))
      ≃+* (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) := Ideal.quotEquivOfEq hvi
  obtain ⟨s, hs, hts⟩ :=
    exists_ringKrullDim_eq_trdeg k (MvPolynomial (Fin n) k ⧸ Ideal.span {f})
      (FractionRing (MvPolynomial (Fin n) k ⧸ Ideal.span {f}))
  have hsm : s = m := by
    rw [trdeg_fractionRing] at hts
    exact_mod_cast hts.symm.trans htr
  rw [ringKrullDim_eq_of_ringEquiv e, hs, hsm]

/-- **Proposition 1.13**, converse: a variety of dimension `n − 1` in `𝔸ⁿ` is a
hypersurface.

Here the dimension formula is used in earnest: it turns `dim A(Y) = n − 1` into
`height I(Y) = 1`, and a height-one prime of a unique factorisation domain is
principal. -/
theorem exists_irreducible_eq_zeroSet {n : ℕ} {Y : Set (Fin n → k)}
    (hY : IsAffineVariety Y) {m : ℕ} (hm : m + 1 = n) (hdim : dim Y = m) :
    ∃ f : MvPolynomial (Fin n) k, Irreducible f ∧
      Y = zeroSet ({f} : Set (MvPolynomial (Fin n) k)) := by
  classical
  haveI hprime : (vanishingIdeal k Y).IsPrime :=
    (isIrreducible_iff_isPrime hY.isAlgebraicSet).1 hY.1
  haveI : FiniteRingKrullDim (MvPolynomial (Fin n) k) :=
    finiteRingKrullDim_of_finiteType k (MvPolynomial (Fin n) k)
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (vanishingIdeal k Y).height = h :=
    ENat.ne_top_iff_exists.mp ((vanishingIdeal k Y).height_ne_top hprime.ne_top) |>.imp
      fun _ e => e.symm
  have hcoord : ringKrullDim (coordinateRing Y) = (m : WithBot ℕ∞) := by
    rw [← dim_eq_ringKrullDim_coordinateRing hY.isAlgebraicSet, hdim]
  have hdimA : ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hform := height_add_ringKrullDim_quotient_eq k (MvPolynomial (Fin n) k)
    (vanishingIdeal k Y) h hh
  rw [hcoord, hdimA] at hform
  have hh1 : h = 1 := by
    have hcast : (h : WithBot ℕ∞) + (m : WithBot ℕ∞) = ((h + m : ℕ) : WithBot ℕ∞) := by
      push_cast; ring
    rw [hcast] at hform
    have hnat : h + m = n := by exact_mod_cast hform
    omega
  rw [hh1] at hh
  obtain ⟨f, hf⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
  rw [Ideal.submodule_span_eq] at hf
  have hfne : f ≠ 0 := by
    rintro rfl
    exact Ideal.ne_bot_of_height_eq_one hh (by simpa using hf)
  have hspanprime : (Ideal.span {f}).IsPrime := by rw [← hf]; infer_instance
  refine ⟨f, (UniqueFactorizationMonoid.irreducible_iff_prime).2
    ((Ideal.span_singleton_prime hfne).1 hspanprime), ?_⟩
  have hZ := hY.isAlgebraicSet.zeroLocus_vanishingIdeal
  rw [hf] at hZ
  rw [← hZ]
  exact (zeroSet_eq_zeroLocus_span _).symm

end Hartshorne
