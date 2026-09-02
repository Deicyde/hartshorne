/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.VanishingIdeal
import Hartshorne.Affine.Nullstellensatz

/-!
# The homogeneous Nullstellensatz

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.1 (p. 11).

If `𝔞` is a homogeneous ideal and `f` is homogeneous of positive degree
vanishing at every point of `Z(𝔞) ⊆ ℙⁿ`, then some positive power of `f` lies
in `𝔞`.

Hartshorne's hint is to reduce to the affine Nullstellensatz through the cone:
read `S` as the coordinate ring of `𝔸ⁿ⁺¹`, where the affine zero set of `𝔞` is
the cone over `Z(𝔞)` together with the origin. The origin is handled by the
degree hypothesis, which is also why the statement fails for degree-zero `f`.

The step that makes the reduction work is that the affine zero set of a
homogeneous ideal is stable under scaling, so a nonzero affine point of it
determines a projective point of `Z(𝔞)`.

## Main results

* `Hartshorne.zeroSet_smul_of_isHomogeneousIdeal` : scaling stability.
* `Hartshorne.exists_pow_mem_of_forall_homogeneousVanish` : Exercise 2.1.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- The affine zero set of a homogeneous ideal is stable under scaling by a
nonzero constant.

This is what lets a nonzero point of the affine zero set be read as a point of
projective space, and it is the technical heart of the reduction to the affine
Nullstellensatz. -/
theorem zeroSet_smul_of_isHomogeneousIdeal {I : Ideal (MvPolynomial σ k)}
    (hI : IsHomogeneousIdeal I) {a : k} {v : σ → k}
    (hv : v ∈ zeroSet (I : Set (MvPolynomial σ k))) :
    a • v ∈ zeroSet (I : Set (MvPolynomial σ k)) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists (𝒜 := homogeneousSubmodule σ k) (I := I)).1 hI
  have hspan : zeroSet (I : Set (MvPolynomial σ k))
      = zeroSet ((↑) '' S : Set (MvPolynomial σ k)) := by
    rw [zeroSet_eq_zeroLocus_span, zeroSet_eq_zeroLocus_span, Ideal.span_eq, ← hS]
  rw [hspan] at hv ⊢
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨n, hn⟩ := isHomogeneousElem_iff.1 g.2
  have := hv _ ⟨g, hg, rfl⟩
  rw [hn.eval_smul]
  simp [this]

/-- A homogeneous polynomial of positive degree vanishes at the origin. -/
theorem eval_zero_of_isHomogeneous {f : MvPolynomial σ k} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : 0 < n) : eval (0 : σ → k) f = 0 := by
  -- Scaling by `0`: `eval 0 f = 0ⁿ * eval 0 f = 0` since `n > 0`.
  have h := hf.eval_smul (0 : k) (0 : σ → k)
  simpa [zero_pow hn.ne'] using h

section AlgClosed

variable [IsAlgClosed k] [Finite σ]

/-- **The homogeneous Nullstellensatz**, Hartshorne's Exercise 2.1.

A homogeneous polynomial of positive degree vanishing on `Z(𝔞)` has a positive
power in `𝔞`. -/
theorem exists_pow_mem_of_forall_homogeneousVanish
    {I : Ideal (MvPolynomial σ k)} (hI : IsHomogeneousIdeal I)
    {f : MvPolynomial σ k} {n : ℕ} (hn : 0 < n) (hf : f.IsHomogeneous n)
    (hvan : ∀ P ∈ projZeroSet (I : Set (MvPolynomial σ k)), HomogeneousVanish f P) :
    ∃ q : ℕ, 0 < q ∧ f ^ q ∈ I := by
  refine exists_pow_mem_of_forall_eval_eq_zero (I := I) (f := f) ?_
  intro v hv
  rw [zeroLocus_eq_zeroSet] at hv
  rcases eq_or_ne v 0 with rfl | hv0
  · exact eval_zero_of_isHomogeneous hf hn
  · -- A nonzero affine zero gives a projective point of `Z(𝔞)`.
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv0
    have hrep : (Projectivization.mk k v hv0).rep ∈ zeroSet (I : Set (MvPolynomial σ k)) := by
      rw [← ha, Units.smul_def]
      exact zeroSet_smul_of_isHomogeneousIdeal hI hv
    have hfP : eval (Projectivization.mk k v hv0).rep f = 0 :=
      hvan _ fun g hg => hrep g hg
    rw [← ha, Units.smul_def, hf.eval_smul] at hfP
    rcases mul_eq_zero.1 hfP with h | h
    · exact absurd ((pow_eq_zero_iff hn.ne').1 h) (Units.ne_zero a)
    · exact h

end AlgClosed

end Hartshorne
