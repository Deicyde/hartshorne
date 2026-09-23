/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Basic

/-!
# Linear forms separating projective points

The projective-coordinate separation used in Hartshorne, *Algebraic Geometry*,
I.6, Lemma 6.4 (p. 41).
-/

namespace Hartshorne

open MvPolynomial

universe u v

variable {k : Type u} [Field k] {σ : Type v}

private theorem exists_linear_form_vanish_not
    {P Q : ProjectiveSpace k σ} (hPQ : P ≠ Q) :
    ∃ h : MvPolynomial σ k,
      h.IsHomogeneous 1 ∧ HomogeneousVanish h P ∧ ¬ HomogeneousVanish h Q := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp P.rep_nonzero
  have hex : ∃ j, P.rep i * Q.rep j ≠ P.rep j * Q.rep i := by
    by_contra hn
    push Not at hn
    apply hPQ
    let a : k := Q.rep i / P.rep i
    have hsmul : a • P.rep = Q.rep := by
      funext j
      show a * P.rep j = Q.rep j
      rw [show a = Q.rep i / P.rep i from rfl, div_mul_eq_mul_div,
        div_eq_iff hi]
      simpa [mul_comm] using (hn j).symm
    have hmk : Projectivization.mk k Q.rep Q.rep_nonzero =
        Projectivization.mk k P.rep P.rep_nonzero :=
      (Projectivization.mk_eq_mk_iff' k _ _ Q.rep_nonzero P.rep_nonzero).2
        ⟨a, hsmul⟩
    simpa only [Q.mk_rep, P.mk_rep] using hmk.symm
  obtain ⟨j, hj⟩ := hex
  let h : MvPolynomial σ k :=
    C (P.rep i) * X j - C (P.rep j) * X i
  refine ⟨h, ?_, ?_, ?_⟩
  · exact (isHomogeneous_C_mul_X (P.rep i) j).sub
      (isHomogeneous_C_mul_X (P.rep j) i)
  · simp [h, HomogeneousVanish, mul_comm]
  · simpa [h, HomogeneousVanish, sub_eq_zero] using hj

/-- Distinct projective points can be separated by degree-one homogeneous
polynomials: the denominator vanishes only at the first point, while the
numerator vanishes at neither. -/
theorem exists_linear_forms_separating_projective_points
    {P Q : ProjectiveSpace k σ} (hPQ : P ≠ Q) :
    ∃ g h : MvPolynomial σ k,
      g.IsHomogeneous 1 ∧ h.IsHomogeneous 1 ∧
      ¬ HomogeneousVanish g P ∧ ¬ HomogeneousVanish g Q ∧
      HomogeneousVanish h P ∧ ¬ HomogeneousVanish h Q := by
  obtain ⟨h, hhhom, hhP, hhQ⟩ := exists_linear_form_vanish_not hPQ
  obtain ⟨l, hlhom, hlQ, hlP⟩ := exists_linear_form_vanish_not hPQ.symm
  refine ⟨h + l, h, hhhom.add hlhom, hhhom, ?_, ?_, hhP, hhQ⟩
  · change eval P.rep (h + l) ≠ 0
    rw [map_add, show eval P.rep h = 0 from hhP]
    simpa [HomogeneousVanish] using hlP
  · change eval Q.rep (h + l) ≠ 0
    rw [map_add, show eval Q.rep l = 0 from hlQ, add_zero]
    simpa [HomogeneousVanish] using hhQ

end Hartshorne
