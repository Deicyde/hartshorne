/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Nullstellensatz

/-!
# Algebraic sets and radical ideals

Hartshorne, *Algebraic Geometry*, I.1, Corollary 1.4 (p. 4).

`Y ↦ I(Y)` and `𝔞 ↦ Z(𝔞)` are mutually inverse, inclusion-reversing bijections
between the algebraic sets of affine space and the radical ideals of the
polynomial ring, and under them irreducible algebraic sets correspond to prime
ideals.

The bijection is formal from the Galois connection once the Nullstellensatz
supplies `I(Z(𝔞)) = √𝔞`. The irreducible-iff-prime half is the part with
content and follows Hartshorne's argument.

## Main results

* `Hartshorne.algebraicSetEquivRadicalIdeal` : the bijection, Hartshorne 1.4.
* `Hartshorne.isIrreducible_iff_isPrime` : irreducible iff prime.
* `Hartshorne.isIrreducible_univ` : `𝔸ⁿ` is irreducible (Example 1.4.1).
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- The vanishing ideal of any set is radical: a power of `f` vanishing on `Y`
forces `f` to vanish on `Y`, because `k` has no nilpotents. This needs no
hypothesis on `k` beyond being a field. -/
theorem isRadical_vanishingIdeal (Y : Set (σ → k)) :
    (vanishingIdeal k Y).IsRadical := by
  intro f hf x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hf
  have hpow : (aeval x f : k) ^ n = 0 := by simpa [map_pow] using hn x hx
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp at hpow
  · exact pow_eq_zero_iff hpos.ne' |>.1 hpow

/-- The vanishing ideal of a nonempty set is proper. -/
theorem vanishingIdeal_ne_top {Y : Set (σ → k)} (hY : Y.Nonempty) :
    vanishingIdeal k Y ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hY
  intro h
  have h1 : (1 : MvPolynomial σ k) ∈ vanishingIdeal k Y := (Ideal.eq_top_iff_one _).1 h
  have : (1 : k) = 0 := by simpa using h1 x hx
  exact one_ne_zero this

section AlgClosed

variable [IsAlgClosed k] [Finite σ]

/-- Half of Hartshorne 1.4: on radical ideals, `I ∘ Z` is the identity. -/
theorem vanishingIdeal_zeroLocus_of_isRadical {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsRadical) : vanishingIdeal k (zeroLocus k I) = I := by
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hI.radical]

/-- **Hartshorne 1.4**: the inclusion-reversing bijection between algebraic sets
in affine space and radical ideals of the polynomial ring. -/
def algebraicSetEquivRadicalIdeal :
    {Y : Set (σ → k) // IsAlgebraicSet Y} ≃ {I : Ideal (MvPolynomial σ k) // I.IsRadical} where
  toFun Y := ⟨vanishingIdeal k Y.1, isRadical_vanishingIdeal Y.1⟩
  invFun I := ⟨zeroLocus k I.1, isAlgebraicSet_iff_exists_ideal.2 ⟨I.1, rfl⟩⟩
  left_inv Y := Subtype.ext Y.2.zeroLocus_vanishingIdeal
  right_inv I := Subtype.ext (vanishingIdeal_zeroLocus_of_isRadical I.2)

@[simp]
theorem algebraicSetEquivRadicalIdeal_apply (Y : {Y : Set (σ → k) // IsAlgebraicSet Y}) :
    (algebraicSetEquivRadicalIdeal Y).1 = vanishingIdeal k Y.1 :=
  rfl

/-- The bijection reverses inclusions. -/
theorem algebraicSetEquivRadicalIdeal_anti_mono
    {Y Z : {Y : Set (σ → k) // IsAlgebraicSet Y}} (h : Y.1 ⊆ Z.1) :
    (algebraicSetEquivRadicalIdeal Z).1 ≤ (algebraicSetEquivRadicalIdeal Y).1 :=
  vanishingIdeal_anti_mono h

/-- The zero locus of a proper radical ideal is nonempty. This is the
Nullstellensatz again: a radical ideal with empty zero locus would equal its own
radical `⊤`. -/
theorem zeroLocus_nonempty_of_isRadical {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsRadical) (hne : I ≠ ⊤) : (zeroLocus k I).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  refine hne ?_
  have := vanishingIdeal_zeroLocus_of_isRadical hI
  rw [h, vanishingIdeal_empty] at this
  exact this.symm

/-- **Hartshorne 1.4**, second half: an algebraic set is irreducible exactly when
its ideal is prime.

Forward is Hartshorne's argument: if `fg ∈ I(Y)` then `Y` is covered by the two
closed sets `Y ∩ Z(f)` and `Y ∩ Z(g)`, so irreducibility puts `Y` inside one of
them. Backward uses that a prime is radical and proper, so `Z(𝔭)` is nonempty,
and the same covering argument run in reverse. -/
theorem isIrreducible_iff_isPrime {Y : Set (σ → k)} (hY : IsAlgebraicSet Y) :
    IsIrreducible Y ↔ (vanishingIdeal k Y).IsPrime := by
  constructor
  · rintro ⟨hne, hpre⟩
    refine ⟨vanishingIdeal_ne_top hne, fun {f g} hfg => ?_⟩
    have hcov : Y ⊆ zeroSet {f} ∪ zeroSet {g} := by
      intro x hx
      have : aeval x f * aeval x g = 0 := by simpa [map_mul] using hfg x hx
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)
    rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hpre) _ _
      (isClosed_zeroSet {f}) (isClosed_zeroSet {g}) hcov with h | h
    · exact Or.inl fun x hx => by simpa using h hx f rfl
    · exact Or.inr fun x hx => by simpa using h hx g rfl
  · intro hp
    refine ⟨?_, ?_⟩
    · have hne := zeroLocus_nonempty_of_isRadical hp.isRadical hp.ne_top
      rwa [hY.zeroLocus_vanishingIdeal] at hne
    · rw [isPreirreducible_iff_isClosed_union_isClosed]
      intro z₁ z₂ hz₁ hz₂ hcov
      by_contra hcon
      rw [not_or, Set.not_subset, Set.not_subset] at hcon
      obtain ⟨⟨x, hx, hxz₁⟩, ⟨y, hy, hyz₂⟩⟩ := hcon
      obtain ⟨f, hf, hfx⟩ : ∃ f ∈ vanishingIdeal k z₁, aeval x f ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hxz₁ ((isClosed_iff_isAlgebraicSet.1 hz₁).zeroLocus_vanishingIdeal ▸ hc)
      obtain ⟨g, hg, hgy⟩ : ∃ g ∈ vanishingIdeal k z₂, aeval y g ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hyz₂ ((isClosed_iff_isAlgebraicSet.1 hz₂).zeroLocus_vanishingIdeal ▸ hc)
      have hfg : f * g ∈ vanishingIdeal k Y := by
        intro z hz
        rcases hcov hz with h | h
        · simp [map_mul, hf z h]
        · simp [map_mul, hg z h]
      rcases hp.2 hfg with h | h
      · exact hfx (h x hx)
      · exact hgy (h y hy)

/-- Example 1.4.1: affine space is irreducible, because it is the zero locus of
the zero ideal, which is prime. -/
theorem isIrreducible_univ : IsIrreducible (Set.univ : Set (σ → k)) := by
  have hbot : zeroLocus k (⊥ : Ideal (MvPolynomial σ k)) = (Set.univ : Set (σ → k)) := by
    rw [zeroLocus_bot]; rfl
  rw [← hbot]
  refine (isIrreducible_iff_isPrime (isAlgebraicSet_iff_exists_ideal.2 ⟨⊥, rfl⟩)).2 ?_
  rw [vanishingIdeal_zeroLocus_of_isRadical Ideal.isRadical_bot]
  exact Ideal.isPrime_bot

end AlgClosed

end Hartshorne
