/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# One step of a chain, seen in the quotient

Toward Hartshorne, *Algebraic Geometry*, I.1, Theorem 1.8A(b).

If `𝔮 < 𝔭` are primes with `height 𝔮 = h` and `height 𝔭 = h + 1`, then `𝔭/𝔮` has
height one in `R/𝔮`.

This is what turns the general dimension formula into repeated application of
the height-one case: each step of a maximal chain below `𝔭` is a height-one
prime in the quotient by the step before it.

The content is that no prime lies strictly between `𝔮` and `𝔭`. That is not an
extra hypothesis but a consequence of the heights: an intermediate `𝔯` would
have height greater than `h`, and `𝔭` greater than that, so at least `h + 2`.

Two small mismatches make this longer in Lean than on paper. Strict monotonicity
of height lives on `Order.height` over `PrimeSpectrum`, not on `Ideal.height`,
so the two have to be bridged; and the primes of `R/𝔮` have to be pushed back to
primes of `R` above `𝔮`, where the height hypotheses live.

## Main results

* `Hartshorne.height_map_quotient_eq_one`
-/

namespace Hartshorne

open Ideal

variable {R : Type*} [CommRing R] {𝔮 𝔭 : Ideal R}

/-- Strict monotonicity of height, in the `Ideal.height` spelling. -/
theorem height_lt_height_of_lt [h1 : 𝔮.IsPrime] [h2 : 𝔭.IsPrime] (h : 𝔮 < 𝔭)
    (hfin : 𝔮.height < ⊤) : 𝔮.height < 𝔭.height := by
  rw [PrimeSpectrum.height_eq_orderHeight (⟨𝔮, h1⟩ : PrimeSpectrum R),
    PrimeSpectrum.height_eq_orderHeight (⟨𝔭, h2⟩ : PrimeSpectrum R)]
  refine Order.height_strictMono h ?_
  rwa [← PrimeSpectrum.height_eq_orderHeight (⟨𝔮, h1⟩ : PrimeSpectrum R)]

/-- The image of `𝔭` in `R/𝔮` is prime, `𝔮` being contained in `𝔭`. -/
theorem isPrime_map_quotient [𝔭.IsPrime] (hle : 𝔮 ≤ 𝔭) :
    (𝔭.map (Ideal.Quotient.mk 𝔮)).IsPrime := by
  refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
  rwa [Ideal.mk_ker]

/-- Contracting the image recovers `𝔭`. -/
theorem comap_map_quotient (hle : 𝔮 ≤ 𝔭) :
    (𝔭.map (Ideal.Quotient.mk 𝔮)).comap (Ideal.Quotient.mk 𝔮) = 𝔭 := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hle]

/-- Contraction along the quotient map is strictly monotone. -/
theorem comap_lt_comap_quotient {q q' : Ideal (R ⧸ 𝔮)} (h : q < q') :
    q.comap (Ideal.Quotient.mk 𝔮) < q'.comap (Ideal.Quotient.mk 𝔮) := by
  refine lt_of_le_of_ne (Ideal.comap_mono h.le) fun heq => h.ne ?_
  rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q, heq,
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

/-- An ideal of `R/𝔮` contracting to `𝔮` is zero. -/
theorem eq_bot_of_comap_eq {q : Ideal (R ⧸ 𝔮)}
    (h : q.comap (Ideal.Quotient.mk 𝔮) = 𝔮) : q = ⊥ := by
  rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q, h,
    Ideal.map_quotient_self]

/-- The zero ideal of a domain has height zero. -/
theorem height_bot_eq_zero (A : Type*) [CommRing A] [IsDomain A] :
    (⊥ : Ideal A).height = 0 := by
  rw [PrimeSpectrum.height_eq_orderHeight
    (⟨(⊥ : Ideal A), Ideal.bot_prime⟩ : PrimeSpectrum A)]
  exact Order.IsMin.height_eq_zero fun y _ => show (⊥ : Ideal A) ≤ y.asIdeal from bot_le

/-- **A consecutive pair of a chain has height one in the quotient.** -/
theorem height_map_quotient_eq_one [h1 : 𝔮.IsPrime] [h2 : 𝔭.IsPrime] (hlt : 𝔮 < 𝔭)
    {h : ℕ} (hq : 𝔮.height = h) (hp : 𝔭.height = h + 1) :
    (𝔭.map (Ideal.Quotient.mk 𝔮)).height = 1 := by
  haveI hmp := isPrime_map_quotient (𝔮 := 𝔮) hlt.le
  have hqfin : 𝔮.height < ⊤ := by rw [hq]; exact ENat.coe_lt_top h
  refine le_antisymm (Ideal.height_le_iff.2 fun q hq' hlt' => ?_) ?_
  · -- Anything strictly below is the zero ideal, because nothing sits between
    -- `𝔮` and `𝔭`.
    haveI := hq'
    haveI : (q.comap (Ideal.Quotient.mk 𝔮)).IsPrime := Ideal.comap_isPrime _ _
    have hlt3 : q.comap (Ideal.Quotient.mk 𝔮) < 𝔭 := by
      rw [← comap_map_quotient (𝔭 := 𝔭) hlt.le]
      exact comap_lt_comap_quotient hlt'
    have hcomap : q.comap (Ideal.Quotient.mk 𝔮) = 𝔮 := by
      by_contra hne
      have hqle : 𝔮 ≤ q.comap (Ideal.Quotient.mk 𝔮) := fun x hx => by
        simpa [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx] using q.zero_mem
      have hlt2 : 𝔮 < q.comap (Ideal.Quotient.mk 𝔮) := lt_of_le_of_ne hqle (Ne.symm hne)
      have hmono : (q.comap (Ideal.Quotient.mk 𝔮)).height ≤ 𝔭.height := by
        rw [PrimeSpectrum.height_eq_orderHeight
            (⟨q.comap (Ideal.Quotient.mk 𝔮), ‹_›⟩ : PrimeSpectrum R),
          PrimeSpectrum.height_eq_orderHeight (⟨𝔭, h2⟩ : PrimeSpectrum R)]
        exact Order.height_mono hlt3.le
      have hfin2 : (q.comap (Ideal.Quotient.mk 𝔮)).height < ⊤ :=
        lt_of_le_of_lt hmono (by rw [hp]; simp)
      have hstep1 := height_lt_height_of_lt hlt2 hqfin
      have hstep2 := height_lt_height_of_lt hlt3 hfin2
      rw [hq] at hstep1
      rw [hp] at hstep2
      exact absurd hstep2 (not_lt.2 (Order.add_one_le_of_lt hstep1))
    rw [eq_bot_of_comap_eq hcomap, height_bot_eq_zero]
    exact zero_lt_one
  · -- The zero ideal sits strictly below, so the height is at least one.
    rw [PrimeSpectrum.height_eq_orderHeight
      (⟨𝔭.map (Ideal.Quotient.mk 𝔮), hmp⟩ : PrimeSpectrum (R ⧸ 𝔮)),
      ENat.one_le_iff_ne_zero, Order.height_ne_zero]
    intro hmin
    have hle : (⟨(⊥ : Ideal (R ⧸ 𝔮)), Ideal.bot_prime⟩ : PrimeSpectrum (R ⧸ 𝔮))
        ≤ ⟨𝔭.map (Ideal.Quotient.mk 𝔮), hmp⟩ := show (⊥ : Ideal (R ⧸ 𝔮)) ≤ _ from bot_le
    have hge := hmin hle
    have hbot : 𝔭.map (Ideal.Quotient.mk 𝔮) = ⊥ :=
      le_antisymm (show 𝔭.map (Ideal.Quotient.mk 𝔮) ≤ ⊥ from hge) bot_le
    have := comap_map_quotient (𝔭 := 𝔭) hlt.le
    rw [hbot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this
    exact hlt.ne this

end Hartshorne
