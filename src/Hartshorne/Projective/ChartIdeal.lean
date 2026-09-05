/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ChartDictionary
import Hartshorne.Projective.AffineCover

/-!
# The chart dictionary at the level of ideals

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(b) and (c).

`S_(xᵢ) ≅ k[y]` identifies the two ambient rings. To cut it down to
`S(Y)_(xᵢ) ≅ A(Yᵢ)` the two vanishing ideals have to be matched, and this file
does that.

The statement is not that `α` carries `J(Y)` onto `I(Yᵢ)` on the nose — it does
not, because `xᵢ − 1` and its multiples are killed by `α` for free. What is true,
and is what the localisation needs, is that for homogeneous `g`

`α(g) ∈ I(Yᵢ) ↔ xᵢ · g ∈ J(Y)`,

with a single power of `xᵢ` rather than an unspecified one. The reason it is a
single power is geometric: `xᵢ · g` vanishes off the chart because `xᵢ` does, and
on the chart because `g` does.

## Main results

* `Hartshorne.homogeneousVanish_iff_eval_dehomogenize`
* `Hartshorne.dehomogenize_mem_vanishingIdeal_iff`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*} [DecidableEq σ]

/-- On the chart, a homogeneous `g` vanishes at `P` exactly when its
dehomogenisation vanishes at `φᵢ(P)`.

Homogeneity is what makes this an equivalence: rescaling the representative
multiplies the value by a nonzero power. -/
theorem homogeneousVanish_iff_eval_dehomogenize {i : σ} {n : ℕ} {g : MvPolynomial σ k}
    (hg : g.IsHomogeneous n) {P : ProjectiveSpace k σ} (hP : P ∈ standardChart i) :
    HomogeneousVanish g P ↔ eval (chartMap i P) (dehomogenize i g) = 0 := by
  have hi : P.rep i ≠ 0 := rep_ne_zero_of_mem_standardChart hP
  have hcv : chartInvVec i (chartMap i P) = (P.rep i)⁻¹ • P.rep := chartInvVec_div i hi
  rw [eval_dehomogenize, hcv, hg.eval_smul, HomogeneousVanish]
  refine ⟨fun h => by rw [h, mul_zero], fun h => ?_⟩
  rcases mul_eq_zero.1 h with hc | hc
  · exact absurd hc (pow_ne_zero n (inv_ne_zero hi))
  · exact hc

omit [DecidableEq σ] in
/-- Every element of `J(Y)` vanishes on `Y`. -/
theorem homogeneousVanish_of_mem_homogeneousVanishingIdeal
    {Y : Set (ProjectiveSpace k σ)} {f : MvPolynomial σ k}
    (hf : f ∈ homogeneousVanishingIdeal Y) {P : ProjectiveSpace k σ} (hP : P ∈ Y) :
    HomogeneousVanish f P := by
  have hsub : Y ⊆ projZeroSet (homogeneousVanishingIdeal Y : Set (MvPolynomial σ k)) := by
    rw [projZeroSet_homogeneousVanishingIdeal]
    exact fun Q hQ h hh => hh.2 Q hQ
  exact hsub hP f hf

/-- **The chart dictionary for ideals.**

For homogeneous `g`, the dehomogenisation lies in `I(Yᵢ)` exactly when `xᵢ · g`
lies in `J(Y)`. One power of `xᵢ` suffices, because it is what clears the part
of `Y` outside the chart. -/
theorem dehomogenize_mem_vanishingIdeal_iff {i : σ} {n : ℕ} {g : MvPolynomial σ k}
    (hg : g.IsHomogeneous n) (Y : Set (ProjectiveSpace k σ)) :
    dehomogenize i g ∈ vanishingIdeal k (chartMap i '' (Y ∩ standardChart i))
      ↔ X i * g ∈ homogeneousVanishingIdeal Y := by
  constructor
  · intro h
    refine Ideal.subset_span ⟨⟨1 + n, (isHomogeneous_X k i).mul hg⟩, fun P hP => ?_⟩
    show eval P.rep (X i * g) = 0
    rw [map_mul, eval_X]
    by_cases hPc : P ∈ standardChart i
    · have : eval P.rep g = 0 :=
        (homogeneousVanish_iff_eval_dehomogenize hg hPc).2
          (h _ ⟨P, ⟨hP, hPc⟩, rfl⟩)
      rw [this, mul_zero]
    · have : P.rep i = 0 := by
        simpa [HomogeneousVanish] using (mem_standardChart_iff (i := i) (P := P)).not.1 hPc
      rw [this, zero_mul]
  · rintro h y ⟨P, ⟨hPY, hPc⟩, rfl⟩
    have hi : P.rep i ≠ 0 := rep_ne_zero_of_mem_standardChart hPc
    have hz : eval P.rep (X i * g) = 0 :=
      homogeneousVanish_of_mem_homogeneousVanishingIdeal h hPY
    rw [map_mul, eval_X] at hz
    refine (homogeneousVanish_iff_eval_dehomogenize hg hPc).1 ?_
    show eval P.rep g = 0
    rcases mul_eq_zero.1 hz with hc | hc
    · exact absurd hc hi
    · exact hc

end Hartshorne
