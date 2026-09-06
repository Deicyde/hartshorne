/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.HeightOneTrdeg
import Hartshorne.Dimension.QuotientHeight
import Hartshorne.Dimension.DimFormulaReduction

/-!
# Theorem 1.8A(b): the dimension formula

Hartshorne, *Algebraic Geometry*, I.1, Theorem 1.8A(b) (p. 6).

For `B` a finitely generated domain over `k` and `𝔭 ⊆ B` a prime of height `h`,

`trdeg_k K(B) = trdeg_k K(B/𝔭) + h`,

and hence `height 𝔭 + dim B/𝔭 = dim B`.

The induction is on `h`. At height zero the prime is `(0)` and there is nothing
to prove. At height `h + 1`, a chain realising the height supplies a prime
`𝔮 < 𝔭` of height `h`; the height-one case applied to `B/𝔮` and `𝔭/𝔮` removes
one, and the inductive hypothesis applied to `𝔮` removes the rest.

Two facts make the step go through, both proved separately: that `𝔭/𝔮` has
height one in `B/𝔮`, which is forced by the heights rather than assumed, and
that a chain realising a height assigns each of its terms its own index, which
is how `𝔮` is found.

## Main results

* `Hartshorne.trdeg_eq_trdeg_quotient_add_height`
* `Hartshorne.height_add_ringKrullDim_quotient_eq`
* `Hartshorne.height_eq_ringKrullDim_of_isMaximal`
-/

namespace Hartshorne

universe u

variable (k : Type u) [Field k]

/-- **Theorem 1.8A(b)**, in transcendence-degree form. -/
theorem trdeg_eq_trdeg_quotient_add_height :
    ∀ (h : ℕ) (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
      (𝔭 : Ideal B) (_ : 𝔭.IsPrime) (_ : 𝔭.height = h),
      Algebra.trdeg k (FractionRing B) = Algebra.trdeg k (FractionRing (B ⧸ 𝔭)) + h := by
  intro h
  induction h with
  | zero =>
    intro B _ _ _ _ 𝔭 hp hh
    haveI := hp
    -- Height zero in a domain means the zero ideal.
    have hbot : 𝔭 = ⊥ := by
      by_contra hne
      have hlt : (⊥ : Ideal B) < 𝔭 := lt_of_le_of_ne bot_le (Ne.symm hne)
      haveI : (⊥ : Ideal B).IsPrime := Ideal.bot_prime
      have := height_lt_height_of_lt hlt (by rw [height_bot_eq_zero]; exact ENat.top_pos)
      rw [height_bot_eq_zero, hh] at this
      simp at this
    subst hbot
    have e : (B ⧸ (⊥ : Ideal B)) ≃ₐ[k] B := AlgEquiv.quotientBot k B
    rw [Nat.cast_zero, add_zero, trdeg_fractionRing, trdeg_fractionRing]
    exact e.trdeg_eq.symm
  | succ h ih =>
    intro B _ _ _ _ 𝔭 hp hh
    haveI := hp
    haveI : FiniteRingKrullDim B := finiteRingKrullDim_of_finiteType k B
    -- A chain realising the height supplies a predecessor of height `h`.
    obtain ⟨l, hlast, hlen⟩ := 𝔭.exists_ltSeries_length_eq_height
    have hlen' : l.length = h + 1 := by
      have hcast : (l.length : ℕ∞) = ((h + 1 : ℕ) : ℕ∞) := by rw [hlen, hh]
      exact_mod_cast hcast
    have hidx : Order.height l.last = (l.length : ℕ∞) := by
      rw [hlast, hlen]
      exact (PrimeSpectrum.height_eq_orderHeight _).symm
    set i : Fin (l.length + 1) := ⟨h, by omega⟩ with hi
    set 𝔮 : Ideal B := (l i).asIdeal with h𝔮
    haveI : 𝔮.IsPrime := (l i).isPrime
    have hqh : 𝔮.height = h := by
      rw [h𝔮, PrimeSpectrum.height_eq_orderHeight,
        Order.height_eq_index_of_length_eq_height_last hidx.symm i]
    have hqlt : 𝔮 < 𝔭 := by
      have hlt : l i < l.last := by
        rw [RelSeries.last]
        exact l.strictMono (by simp [hi, Fin.lt_def]; omega)
      rw [hlast] at hlt
      exact hlt
    -- The step is a height-one prime upstairs.
    have hone := height_map_quotient_eq_one hqlt hqh hh
    haveI := isPrime_map_quotient (𝔮 := 𝔮) hqlt.le
    obtain ⟨n, hn1, hn2⟩ := exists_trdeg_of_height_eq_one k (B ⧸ 𝔮)
      (𝔭.map (Ideal.Quotient.mk 𝔮)) hone
    -- Collapsing the double quotient.
    have e : ((B ⧸ 𝔮) ⧸ (𝔭.map (Ideal.Quotient.mk 𝔮))) ≃ₐ[k] (B ⧸ 𝔭) :=
      DoubleQuot.quotQuotEquivQuotOfLEₐ k hqlt.le
    have hpq : Algebra.trdeg k (FractionRing (B ⧸ 𝔭)) = n := by
      rw [trdeg_fractionRing, ← e.trdeg_eq, ← trdeg_fractionRing]
      exact hn1
    -- Assemble with the inductive hypothesis.
    have hih := ih B 𝔮 ‹_› hqh
    rw [hih, hn2, hpq]
    push_cast
    ring

/-- **Theorem 1.8A(b)**: `height 𝔭 + dim B/𝔭 = dim B`.

The transcendence-degree form above, fed through the reduction: part (a)
computes both dimensions as transcendence degrees, and `B/𝔭` is again a
finitely generated domain, so part (a) applies to it too. -/
theorem height_add_ringKrullDim_quotient_eq (B : Type u) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (𝔭 : Ideal B) [hp : 𝔭.IsPrime]
    (h : ℕ) (hh : 𝔭.height = h) :
    (h : WithBot ℕ∞) + ringKrullDim (B ⧸ 𝔭) = ringKrullDim B := by
  refine height_add_ringKrullDim_quotient_eq_of_trdeg k B (FractionRing B) 𝔭 h ?_
  intro d e hd he
  have hkey := trdeg_eq_trdeg_quotient_add_height k h B 𝔭 hp hh
  rw [hd, he] at hkey
  exact_mod_cast hkey

/-- **Every maximal ideal of a finitely generated domain has height the whole
dimension.**

The quotient by a maximal ideal is a field, so it contributes nothing to the
dimension formula and the height absorbs everything. This is what makes such a
ring equidimensional, and it is the form in which the formula is used
geometrically. -/
theorem height_eq_ringKrullDim_of_isMaximal (B : Type u) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (𝔪 : Ideal B) [hm : 𝔪.IsMaximal] :
    ((𝔪.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim B := by
  haveI : FiniteRingKrullDim B := finiteRingKrullDim_of_finiteType k B
  haveI : 𝔪.IsPrime := hm.isPrime
  obtain ⟨h, hh⟩ : ∃ h : ℕ, 𝔪.height = h :=
    ENat.ne_top_iff_exists.mp (𝔪.height_ne_top hm.ne_top) |>.imp fun _ e => e.symm
  have hquot : ringKrullDim (B ⧸ 𝔪) = 0 :=
    ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hm)
  have hform := height_add_ringKrullDim_quotient_eq k B 𝔪 h hh
  rw [hquot, add_zero] at hform
  rw [hh]
  exact hform

end Hartshorne
