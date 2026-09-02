/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.RegularFunction
import Hartshorne.Projective.VanishingIdeal

/-!
# Regular functions on a quasi-projective variety

Hartshorne, *Algebraic Geometry*, I.3, the definition on p. 15.

The definition copies the quasi-affine one with two changes: the numerator and
denominator are homogeneous, and they have **the same degree**.

Equal degrees is not bookkeeping. Neither `g` nor `h` is a function on `ℙⁿ`, but
their ratio is, because rescaling the representative multiplies both by the same
`aⁿ` and the ratio is unchanged. Drop the condition and the definition is not
merely weaker, it is meaningless: the value would depend on the representative.

## Main definitions

* `Hartshorne.IsRegularAtProj`, `Hartshorne.IsRegularProj`

## Main results

* `Hartshorne.ratio_eq_of_smul` : the ratio is independent of the
  representative. This is what equal degrees buys.
* `Hartshorne.isClosed_eqLocusProj` : Lemma 3.1's content, projective case.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- The ratio of two homogeneous polynomials **of the same degree** is unchanged
by rescaling, which is exactly why it defines a function on projective space. -/
theorem ratio_eq_of_smul {n : ℕ} {g h : MvPolynomial σ k}
    (hg : g.IsHomogeneous n) (hh : h.IsHomogeneous n) {a : k} (ha : a ≠ 0)
    (v : σ → k) :
    eval (a • v) g / eval (a • v) h = eval v g / eval v h := by
  rw [hg.eval_smul, hh.eval_smul, mul_div_mul_left _ _ (pow_ne_zero n ha)]

/-- `f` is *regular at* `P` when near `P` it is a ratio of homogeneous
polynomials of equal degree, with the denominator nowhere zero. -/
def IsRegularAtProj {Y : Set (ProjectiveSpace k σ)} (f : Y → k) (P : Y) : Prop :=
  ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧ ∃ (n : ℕ) (g h : MvPolynomial σ k),
    g.IsHomogeneous n ∧ h.IsHomogeneous n ∧
      (∀ x ∈ U, eval (x : ProjectiveSpace k σ).rep h ≠ 0) ∧
        ∀ x ∈ U, f x = eval (x : ProjectiveSpace k σ).rep g
          / eval (x : ProjectiveSpace k σ).rep h

/-- `f` is *regular* when it is regular at every point. -/
def IsRegularProj {Y : Set (ProjectiveSpace k σ)} (f : Y → k) : Prop :=
  ∀ P, IsRegularAtProj f P

/-- **Lemma 3.1** for the projective case: the agreement locus of two regular
functions is closed.

Locally `f = g₁/h₁` and `f' = g₂/h₂` with the pairs homogeneous of degrees `n₁`
and `n₂`. Agreement is the vanishing of `g₁h₂ − g₂h₁`, and that is homogeneous
of degree `n₁ + n₂` — both terms have the same total degree — so it cuts out a
closed set. Without equal degrees within each pair the difference would not be
homogeneous and the argument would collapse. -/
theorem isClosed_eqLocusProj {Y : Set (ProjectiveSpace k σ)} {f f' : Y → k}
    (hf : IsRegularProj f) (hf' : IsRegularProj f') :
    IsClosed {P : Y | f P = f' P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro P hP
  obtain ⟨U, hU, hPU, n₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := hf P
  obtain ⟨V, hV, hPV, n₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := hf' P
  have hhom : IsHomogeneousSet ({g₁ * h₂ - g₂ * h₁} : Set (MvPolynomial σ k)) := by
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨n₁ + n₂, (hg₁.mul hh₂).sub (by simpa [Nat.add_comm] using hg₂.mul hh₁)⟩
  refine ⟨(U ∩ V) ∩ (Subtype.val ⁻¹' (projZeroSet {g₁ * h₂ - g₂ * h₁})ᶜ), ?_, ?_, ?_⟩
  · rintro Q ⟨⟨hQU, hQV⟩, hQz⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, mem_projZeroSet_iff] at hQz
    intro hQeq
    refine hQz fun p hp => ?_
    rw [Set.mem_singleton_iff] at hp
    subst hp
    show eval _ _ = 0
    rw [Set.mem_ofPred_eq, he₁ Q hQU, he₂ Q hQV,
      div_eq_div_iff (hne₁ Q hQU) (hne₂ Q hQV)] at hQeq
    simp only [map_sub, map_mul]
    rw [hQeq, sub_self]
  · exact ((hU.inter hV).inter
      (((isClosed_projZeroSet_of_isHomogeneousSet hhom).isOpen_compl).preimage
        continuous_subtype_val))
  · refine ⟨⟨hPU, hPV⟩, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, mem_projZeroSet_iff, not_forall]
    refine ⟨g₁ * h₂ - g₂ * h₁, rfl, ?_⟩
    show ¬ (eval _ _ = 0)
    simp only [map_sub, map_mul, sub_eq_zero]
    intro hcon
    exact hP (by
      rw [Set.mem_ofPred_eq, he₁ P hPU, he₂ P hPV,
        div_eq_div_iff (hne₁ P hPU) (hne₂ P hPV), hcon])

end Hartshorne
