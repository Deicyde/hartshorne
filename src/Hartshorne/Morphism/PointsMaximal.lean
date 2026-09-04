/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.Injections
import Hartshorne.Affine.CoordinateRing

/-!
# Points and maximal ideals

Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.2(b) (p. 17).

For an affine algebraic set `Y`, sending `P` to the ideal of functions vanishing
at `P` is a bijection from the points of `Y` to the maximal ideals of `A(Y)`.

This is Corollary 1.4 pushed through the quotient by `I(Y)`. Evaluation at `P`
descends to `A(Y)` because every element of `I(Y)` vanishes at `P`, and it is
surjective onto `k`, so its kernel is maximal.

## Main definitions

* `Hartshorne.evalAt`, `Hartshorne.maximalIdealAt`

## Main results

* `Hartshorne.maximalIdealAt_isMaximal`
* `Hartshorne.maximalIdealAt_injective`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)}

/-- Evaluation at a point of `Y`, as a `k`-algebra map `A(Y) → k`. It is well
defined because every element of `I(Y)` vanishes at every point of `Y`. -/
noncomputable def evalAt (Y : Set (σ → k)) (P : Y) : coordinateRing Y →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (aeval (P : σ → k)) (fun a ha => ha (P : σ → k) P.2)

@[simp]
theorem evalAt_mk (P : Y) (p : MvPolynomial σ k) :
    evalAt Y P (Ideal.Quotient.mk _ p) = aeval (P : σ → k) p :=
  rfl

theorem evalAt_surjective (P : Y) : Function.Surjective (evalAt Y P) := by
  intro c
  exact ⟨Ideal.Quotient.mk _ (C c), by simp⟩

/-- Hartshorne's `𝔪_P`: the functions in `A(Y)` vanishing at `P`. -/
noncomputable def maximalIdealAt (Y : Set (σ → k)) (P : Y) : Ideal (coordinateRing Y) :=
  RingHom.ker (evalAt Y P).toRingHom

theorem mem_maximalIdealAt {P : Y} {a : coordinateRing Y} :
    a ∈ maximalIdealAt Y P ↔ evalAt Y P a = 0 :=
  Iff.rfl

/-- `𝔪_P` is maximal: it is the kernel of a surjection onto the field `k`. -/
theorem maximalIdealAt_isMaximal (P : Y) : (maximalIdealAt Y P).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (evalAt Y P).toRingHom (evalAt_surjective P)

/-- The residue field at `P` is `k`, which is Hartshorne's observation that
`𝒪_P/𝔪 ≅ k`, at the level of the coordinate ring. -/
noncomputable def residueEquiv (P : Y) : (coordinateRing Y ⧸ maximalIdealAt Y P) ≃ₐ[k] k :=
  Ideal.quotientKerAlgEquivOfSurjective (evalAt_surjective P)

/-- Distinct points of affine space are separated by a coordinate function.
This is what makes `P ↦ 𝔪_P` injective. -/
theorem exists_coord_ne {x y : σ → k} (h : x ≠ y) : ∃ i, x i ≠ y i := by
  by_contra hc
  push Not at hc
  exact h (funext hc)

/-- **Theorem 3.2(b)**, injectivity: distinct points give distinct maximal
ideals.

If `P ≠ Q` then some coordinate separates them, and `Xᵢ - Q ᵢ` lies in `𝔪_Q`
but not in `𝔪_P`. -/
theorem maximalIdealAt_injective : Function.Injective (maximalIdealAt Y) := by
  intro P Q h
  by_contra hPQ
  have hne : (P : σ → k) ≠ (Q : σ → k) := fun hc => hPQ (Subtype.ext hc)
  obtain ⟨i, hi⟩ := exists_coord_ne hne
  -- `Xᵢ - C (Q i)` vanishes at `Q` but not at `P`.
  set p : MvPolynomial σ k := X i - C ((Q : σ → k) i) with hp
  have hQmem : Ideal.Quotient.mk _ p ∈ maximalIdealAt Y Q := by
    rw [mem_maximalIdealAt, evalAt_mk]
    simp [hp]
  have hPmem : Ideal.Quotient.mk _ p ∈ maximalIdealAt Y P := h ▸ hQmem
  rw [mem_maximalIdealAt, evalAt_mk] at hPmem
  simp only [hp, map_sub, aeval_X, aeval_C, sub_eq_zero] at hPmem
  exact hi hPmem

/-- Pulling `𝔪_P` back to the polynomial ring gives the ideal of the point. -/
theorem comap_maximalIdealAt (P : Y) :
    Ideal.comap (Ideal.Quotient.mk (vanishingIdeal k Y)) (maximalIdealAt Y P)
      = vanishingIdeal k ({(P : σ → k)} : Set (σ → k)) := by
  ext p
  rw [Ideal.mem_comap, mem_maximalIdealAt, evalAt_mk,
    mem_vanishingIdeal_singleton_iff]

section AlgClosed

variable [IsAlgClosed k] [Finite σ]

/-- **Theorem 3.2(b)**, surjectivity: every maximal ideal of `A(Y)` is `𝔪_P`
for a point `P` of `Y`.

A maximal ideal of `A(Y)` pulls back to a maximal ideal of `k[x₁,…,xₙ]`, which
by the Nullstellensatz is the ideal of a point `x`. Since the pullback contains
`I(Y)`, that point lies in `Z(I(Y)) = Y`. -/
theorem maximalIdealAt_surjective (hY : IsAlgebraicSet Y)
    {m : Ideal (coordinateRing Y)} (hm : m.IsMaximal) :
    ∃ P : Y, maximalIdealAt Y P = m := by
  haveI := hm
  have hcm : (Ideal.comap (Ideal.Quotient.mk (vanishingIdeal k Y)) m).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨x, hx⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hcm
  -- The pullback contains `I(Y)`, so `x` lies in `Y`.
  have hle : vanishingIdeal k Y ≤ vanishingIdeal k ({x} : Set (σ → k)) := by
    rw [← hx]
    intro p hp
    rw [Ideal.mem_comap]
    have : Ideal.Quotient.mk (vanishingIdeal k Y) p = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hp
    rw [this]
    exact Ideal.zero_mem _
  have hxY : x ∈ Y := by
    have hmem : x ∈ zeroLocus k (vanishingIdeal k ({x} : Set (σ → k))) := fun p hp => hp x rfl
    have := zeroLocus_anti_mono (K := k) hle hmem
    rwa [hY.zeroLocus_vanishingIdeal] at this
  refine ⟨⟨x, hxY⟩, ?_⟩
  refine Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_
  rw [comap_maximalIdealAt, hx]

/-- **Theorem 3.2(b)**: the points of `Y` correspond to the maximal ideals of
`A(Y)`. -/
noncomputable def pointsEquivMaximalIdeals (hY : IsAlgebraicSet Y) :
    Y ≃ {m : Ideal (coordinateRing Y) // m.IsMaximal} where
  toFun P := ⟨maximalIdealAt Y P, maximalIdealAt_isMaximal P⟩
  invFun m := (maximalIdealAt_surjective hY m.2).choose
  left_inv P := maximalIdealAt_injective
    (maximalIdealAt_surjective hY (maximalIdealAt_isMaximal P)).choose_spec
  right_inv m := Subtype.ext (maximalIdealAt_surjective hY m.2).choose_spec

end AlgClosed

end Hartshorne
