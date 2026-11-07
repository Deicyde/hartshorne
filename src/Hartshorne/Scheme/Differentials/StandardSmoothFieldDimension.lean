/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.JacobianRegularQuotient
import Hartshorne.Dimension.DimFormula
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Local dimension of a standard smooth algebra over a field

Let `S` be a standard smooth algebra over a field `K`, given by a submersive presentation
`S = K[x_i : i ∈ ι] ⧸ (f_j : j ∈ σ)` of relative dimension `n = #ι - #σ`. For every prime `q` of
`S`, the local ring `S_q` is regular and

`dim S_q + dim S ⧸ q = n`.

In particular every irreducible component of `Spec S` (a minimal prime `q`, where
`dim S_q = 0`) has dimension `n`.

Let `Q` be the preimage of `q` in the polynomial ring `R = K[x]`. The Jacobian determinant of the
presentation is a unit in `S`, so the differentials of the relations are linearly independent in
`κ(Q) ⊗_R Ω_{R/K}`; hence `R_Q ⧸ (f)` is a regular local ring of dimension `ht Q - #σ`. This ring
is the localization of `S` at `q`. Finally `ht Q + dim R ⧸ Q = #ι` by the dimension formula for
finitely generated domains over a field, and `R ⧸ Q ≅ S ⧸ q`.

This supports the comparison of Hartshorne's definition of a smooth morphism (III.10, p. 268)
with the standard smooth predicate: for a morphism smooth of relative dimension `n` in the
standard smooth sense, every irreducible component of every fibre has dimension `n`.

## Main results

* `Hartshorne.SubmersivePresentation.linearIndependent_D_relation`
* `Hartshorne.SubmersivePresentation.isRegularLocalRing_localization`
* `Hartshorne.SubmersivePresentation.ringKrullDim_localization_add_ringKrullDim_quotient`
-/

namespace Hartshorne

open IsLocalRing Ideal Module KaehlerDifferential TensorProduct MvPolynomial

universe u

/-- If `x + m = n` in `WithBot ℕ∞` with `m, n` natural numbers, then `m ≤ n` and `x = n - m`. -/
theorem withBot_eq_sub_of_add_eq {x : WithBot ℕ∞} {m n : ℕ} (h : x + m = n) :
    m ≤ n ∧ x = ((n - m : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + (m : WithBot ℕ∞) = ((⊤ + m : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this, top_add] at h
      exact ENat.natCast_ne_top n (WithBot.coe_injective h).symm
    | coe y =>
      have h' : ((y + m : ℕ) : WithBot ℕ∞) = n := by exact_mod_cast h
      have h'' : y + m = n := by exact_mod_cast h'
      refine ⟨by omega, ?_⟩
      have : y = n - m := by omega
      subst this
      rfl

namespace SubmersivePresentation

variable {K S : Type u} [Field K] [CommRing S] [Algebra K S] {ι σ : Type} [Finite ι] [Finite σ]
variable (P : Algebra.SubmersivePresentation K S ι σ) (q : Ideal S) [q.IsPrime]

omit [Finite ι] in
/-- The differentials of the relations of a submersive presentation are linearly independent in
`κ(Q) ⊗_R Ω_{R/K}`, where `Q` is the preimage in the polynomial ring `R` of a prime of `S`. -/
theorem linearIndependent_D_relation :
    LinearIndependent (q.comap (algebraMap P.Ring S)).ResidueField
      (fun j => (1 : (q.comap (algebraMap P.Ring S)).ResidueField) ⊗ₜ[P.Ring]
        D K P.Ring (P.relation j)) := by
  classical
  have := Fintype.ofFinite σ
  set Q := q.comap (algebraMap P.Ring S)
  set κ := Q.ResidueField
  let b := mvPolynomialBasis K ι
  let l : Ω[P.Ring⁄K] →ₗ[P.Ring] (σ → κ) :=
    LinearMap.pi fun i => (Algebra.linearMap P.Ring κ) ∘ₗ b.coord (P.map i)
  let φ : κ ⊗[P.Ring] Ω[P.Ring⁄K] →ₗ[κ] (σ → κ) := l.liftBaseChange κ
  let M : Matrix σ σ κ := P.jacobiMatrix.map (algebraMap P.Ring κ)
  have hM : M.det ≠ 0 := by
    change (P.jacobiMatrix.map (algebraMap P.Ring κ)).det ≠ 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Ne, Ideal.algebraMap_residueField_eq_zero]
    intro hmem
    have hunit : IsUnit (algebraMap P.Ring S P.jacobiMatrix.det) := by
      rw [← P.jacobian_eq_jacobiMatrix_det]
      exact P.jacobian_isUnit
    exact (Ideal.IsPrime.ne_top (inferInstance : q.IsPrime))
      (Ideal.eq_top_of_isUnit_mem q (show _ ∈ q from hmem) hunit)
  have hcols := Matrix.linearIndependent_cols_of_det_ne_zero hM
  have heq : (⇑φ ∘ fun j => (1 : κ) ⊗ₜ[P.Ring] D K P.Ring (P.relation j)) = M.col := by
    ext j i
    simp [φ, l, M, b, LinearMap.liftBaseChange_tmul, P.jacobiMatrix_apply]
  apply LinearIndependent.of_comp φ
  rw [heq]
  exact hcols

omit [Finite ι] in
/-- The localization of `S` at `q` is the quotient of `R_Q` by the relations; in particular the
two rings have the same dimension, and `S_q` is regular when the quotient is. -/
theorem localization_quotient_transfer :
    ringKrullDim (Localization.AtPrime (q.comap (algebraMap P.Ring S)) ⧸
        span (Set.range fun j => algebraMap P.Ring
          (Localization.AtPrime (q.comap (algebraMap P.Ring S))) (P.relation j))) =
      ringKrullDim (Localization.AtPrime q) ∧
    (IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap P.Ring S)) ⧸
        span (Set.range fun j => algebraMap P.Ring
          (Localization.AtPrime (q.comap (algebraMap P.Ring S))) (P.relation j))) →
      IsRegularLocalRing (Localization.AtPrime q)) := by
  set Q := q.comap (algebraMap P.Ring S)
  set RQ := Localization.AtPrime Q
  set I := RingHom.ker (algebraMap P.Ring S)
  have hspan : span (Set.range fun j => algebraMap P.Ring RQ (P.relation j)) =
      I.map (algebraMap P.Ring RQ) := by
    have hI : I = span (Set.range P.relation) := P.span_range_relation_eq_ker.symm
    rw [hI, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan]
  have hf := P.algebraMap_surjective
  let e : P.Ring ⧸ I ≃+* S := RingHom.quotientKerEquivOfSurjective hf
  have H : (Algebra.algebraMapSubmonoid (P.Ring ⧸ I) Q.primeCompl).map e.toMonoidHom =
      q.primeCompl := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := hf x
      exact ⟨Ideal.Quotient.mk I y, ⟨y, hx, rfl⟩, rfl⟩
  let e' := IsLocalization.ringEquivOfRingEquiv (RQ ⧸ I.map (algebraMap P.Ring RQ))
    (Localization.AtPrime q) e H
  refine ⟨ringKrullDim_eq_of_ringEquiv e', fun h => ?_⟩
  exact IsRegularLocalRing.of_ringEquiv (R := RQ ⧸ I.map (algebraMap P.Ring RQ)) e'

omit [Finite ι] [q.IsPrime] in
/-- The relations lie in the preimage of every ideal of `S`. -/
theorem relation_mem_comap (j : σ) : P.relation j ∈ q.comap (algebraMap P.Ring S) := by
  have h0 : algebraMap P.Ring S (P.relation j) = 0 := P.relation_mem_ker j
  rw [Ideal.mem_comap, h0]
  exact q.zero_mem

/-- For a submersive presentation of `S` over a field and a prime `q` of `S`,
`dim S_q + #σ = ht Q`, where `Q` is the preimage of `q` in the polynomial ring. -/
theorem ringKrullDim_localization_add_card :
    ringKrullDim (Localization.AtPrime q) + Nat.card σ =
      (q.comap (algebraMap P.Ring S)).height := by
  have := Fintype.ofFinite σ
  rw [← (localization_quotient_transfer P q).1, Nat.card_eq_fintype_card]
  exact ringKrullDim_localization_quotient_add_card_of_linearIndependent_D _ _
    (relation_mem_comap P q) (linearIndependent_D_relation P q)

include P in
/-- The local rings of a standard smooth algebra over a field are regular. -/
theorem isRegularLocalRing_localization : IsRegularLocalRing (Localization.AtPrime q) := by
  have := Fintype.ofFinite σ
  exact (localization_quotient_transfer P q).2
    (isRegularLocalRing_localization_quotient_of_linearIndependent_D
      (q.comap (algebraMap P.Ring S)) P.relation (relation_mem_comap P q)
      (linearIndependent_D_relation P q))

/-- For a submersive presentation of `S` over a field, of dimension `n = #ι - #σ`, and a prime
`q` of `S`, `dim S_q + dim S ⧸ q = n`. -/
theorem ringKrullDim_localization_add_ringKrullDim_quotient :
    ringKrullDim (Localization.AtPrime q) + ringKrullDim (S ⧸ q) = P.dimension := by
  set Q := q.comap (algebraMap P.Ring S)
  have hf := P.algebraMap_surjective
  -- `R ⧸ Q ≅ S ⧸ q`.
  have hquot : ringKrullDim (S ⧸ q) = ringKrullDim (P.Ring ⧸ Q) := by
    have hker : RingHom.ker ((Ideal.Quotient.mk q).comp (algebraMap P.Ring S)) = Q := by
      ext x
      simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem, Q, Ideal.mem_comap]
    exact ringKrullDim_eq_of_ringEquiv
      ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective
        (Ideal.Quotient.mk_surjective.comp hf))).symm
  -- `ht Q + dim R ⧸ Q = #ι`.
  have hRdim : ringKrullDim P.Ring = Nat.card ι := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  have hQfin : Q.height ≠ ⊤ := by
    intro htop
    have := Ideal.height_le_ringKrullDim_of_ne_top (IsPrime.ne_top (inferInstance : Q.IsPrime))
    rw [htop, hRdim] at this
    exact absurd (top_le_iff.mp this).symm
      (fun h => ENat.natCast_ne_top _ (WithBot.coe_injective h).symm)
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hQfin
  have hformula := height_add_ringKrullDim_quotient_eq K P.Ring Q h hh.symm
  rw [hRdim] at hformula
  have hloc := ringKrullDim_localization_add_card P q
  rw [← hh] at hloc
  rw [hquot]
  obtain ⟨-, h1⟩ := withBot_eq_sub_of_add_eq hloc
  rw [add_comm] at hformula
  obtain ⟨-, h2⟩ := withBot_eq_sub_of_add_eq hformula
  have hσh : Nat.card σ ≤ h := (withBot_eq_sub_of_add_eq hloc).1
  have hhι : h ≤ Nat.card ι := (withBot_eq_sub_of_add_eq hformula).1
  rw [h1, h2, ← Nat.cast_add]
  change ((h - Nat.card σ + (Nat.card ι - h) : ℕ) : WithBot ℕ∞) =
    ((Nat.card ι - Nat.card σ : ℕ) : WithBot ℕ∞)
  congr 1
  omega

end SubmersivePresentation

end Hartshorne
