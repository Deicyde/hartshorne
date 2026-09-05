/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The graded localisation at a prime is a localisation of a chart

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(b) and (c).

Let `A` be an `ℕ`-graded ring, `f ∈ A₁`, and `𝔭` a homogeneous prime not
containing `f`. Then

`A_(𝔭) = (A_(f))_𝔮`,

where `𝔮` is the prime of `A_(f)` lying under the maximal ideal of `A_(𝔭)`.

This is the step that turns the affine answers of Theorem 3.4 into the graded
ones Hartshorne states. He passes over it: having identified `𝒪_P` with a
localisation of `A(Yᵢ)`, he writes the answer as a localisation of `S(Y)` with
no comment, and the two are the same only because inverting `xᵢ` first does not
change what localising at `𝔭` produces, `xᵢ` being invertible there already.

Mathlib has homogeneous localisation at a prime and away from an element, and
the map between them for nested submonoids, but not this comparison.

## Where the hypotheses are used

`f ∈ A₁` rather than `f ∈ A_d` is not cosmetic. A general `d` forces the degrees
to be divisible by `d` before a fraction can be written with a power of `f` as
denominator, and the statement becomes false as stated. Degree one is the case
Theorem 3.4 needs, `f` being a coordinate.

Homogeneity of `𝔭` is used exactly once, in the third localisation axiom: an
equality in `A_(𝔭)` produces some `s ∉ 𝔭` annihilating a homogeneous element,
and what is needed is a *homogeneous* such `s`. One graded component of `s` is
outside `𝔭` because `𝔭` is homogeneous, and it annihilates the element because
the product is homogeneous of a single degree.

## Main definitions

* `Hartshorne.awayToAtPrime`, `Hartshorne.awayPrime`

## Main results

* `Hartshorne.isLocalization_awayPrime`
-/

namespace Hartshorne

open HomogeneousLocalization

variable {A : Type*} [CommRing A] {ι : Type*} [SetLike ι A] [AddSubgroupClass ι A]
  {𝒜 : ℕ → ι} [GradedRing 𝒜] {f : A} (hf : f ∈ 𝒜 1)
  (𝔭 : Ideal A) [𝔭.IsPrime]

section

variable (hfp : f ∉ 𝔭)

include hfp in
theorem powers_le_primeCompl : Submonoid.powers f ≤ 𝔭.primeCompl :=
  Submonoid.powers_le.2 hfp

/-- The comparison map `A_(f) → A_(𝔭)`, available because `f` is invertible at
`𝔭`. -/
noncomputable abbrev awayToAtPrime : Away 𝒜 f →+* AtPrime 𝒜 𝔭 :=
  mapId 𝒜 (powers_le_primeCompl 𝔭 hfp)

/-- The prime of `A_(f)` lying under the maximal ideal of `A_(𝔭)`.

Taking it as a comap rather than describing it by numerators avoids having to
prove primality: a comap of a prime is prime. -/
noncomputable def awayPrime : Ideal (Away 𝒜 f) :=
  (IsLocalRing.maximalIdeal (AtPrime 𝒜 𝔭)).comap (awayToAtPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp)

instance : (awayPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp).IsPrime :=
  Ideal.IsPrime.comap _

theorem notMem_awayPrime_iff {z : Away 𝒜 f} :
    z ∉ awayPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp ↔ IsUnit (awayToAtPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp z) :=
  IsLocalRing.notMem_maximalIdeal

/-- A class whose numerator avoids `𝔭` is a unit in `A_(𝔭)`: the swapped
fraction is its inverse, and swapping is legitimate exactly because the new
denominator avoids `𝔭`. -/
theorem isUnit_mk_of_num_notMem {q : NumDenSameDeg 𝒜 𝔭.primeCompl}
    (h : (q.num : A) ∉ 𝔭) : IsUnit (mk q : AtPrime 𝒜 𝔭) := by
  refine .of_mul_eq_one (mk ⟨q.deg, q.den, q.num, h⟩) ?_
  rw [← mk_mul, ext_iff_val, val_mk, val_one]
  simp [mul_comm (q.den : A)]

omit [𝔭.IsPrime] hfp in
/-- A nonzero graded component outside `𝔭`, for an element outside `𝔭`. If every
component were inside, so would be their sum. -/
theorem exists_decompose_notMem (hp : Ideal.IsHomogeneous 𝒜 𝔭) {c : A} (hc : c ∉ 𝔭) :
    ∃ j, (DirectSum.decompose 𝒜 c j : A) ∉ 𝔭 := by
  by_contra hall
  push Not at hall
  exact hc (hp.mem_iff.2 hall)

omit [𝔭.IsPrime] hfp in
/-- A homogeneous element annihilated by `c` is annihilated by each graded
component of `c`, because the product sits in a single degree. -/
theorem decompose_mul_eq_zero {c w : A} {j d : ℕ} (hw : w ∈ 𝒜 d) (h : c * w = 0) :
    (DirectSum.decompose 𝒜 c j : A) * w = 0 := by
  rw [← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (i := j) hw, h]
  simp

include hf in
theorem awayToAtPrime_mk (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • 1)) :
    awayToAtPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp (Away.mk 𝒜 hf n x hx)
      = mk ⟨n • 1, ⟨x, hx⟩, ⟨f ^ n, SetLike.pow_mem_graded n hf⟩,
        powers_le_primeCompl 𝔭 hfp ⟨n, rfl⟩⟩ := rfl

include hf in
/-- **`A_(𝔭)` is the localisation of `A_(f)` at `𝔮`.**

The three axioms in turn. A denominator outside `𝔮` maps to a unit because
`A_(𝔭)` is local and `𝔮` is by definition what lies under its maximal ideal.
Every element of `A_(𝔭)` is `a/b` with `a`, `b` of the same degree and `b ∉ 𝔭`,
and dividing both by the same power of `f` puts numerator and denominator into
`A_(f)`; this is the step that wants `f` in degree one. The last axiom is where
homogeneity of `𝔭` is used. -/
theorem isLocalization_awayPrime (hp : Ideal.IsHomogeneous 𝒜 𝔭) :
    letI := (awayToAtPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp).toAlgebra
    IsLocalization.AtPrime (AtPrime 𝒜 𝔭) (awayPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp) := by
  let _ := (awayToAtPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp).toAlgebra
  show IsLocalization (awayPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp).primeCompl (AtPrime 𝒜 𝔭)
  rw [isLocalization_iff]
  refine ⟨fun s => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · rw [RingHom.algebraMap_toAlgebra]
    exact (notMem_awayPrime_iff 𝔭 hfp).1 s.2
  · obtain ⟨q, rfl⟩ := mk_surjective z
    have hnum : (q.num : A) ∈ 𝒜 (q.deg • 1) := by simp
    have hden : (q.den : A) ∈ 𝒜 (q.deg • 1) := by simp
    have hs : Away.mk 𝒜 hf q.deg (q.den : A) hden
        ∈ (awayPrime (𝒜 := 𝒜) (f := f) 𝔭 hfp).primeCompl := by
      refine (notMem_awayPrime_iff 𝔭 hfp).2 ?_
      rw [awayToAtPrime_mk hf 𝔭 hfp]
      exact isUnit_mk_of_num_notMem 𝔭 q.den_mem
    refine ⟨⟨Away.mk 𝒜 hf q.deg (q.num : A) hnum, ⟨_, hs⟩⟩, ?_⟩
    rw [RingHom.algebraMap_toAlgebra,
      awayToAtPrime_mk hf 𝔭 hfp, awayToAtPrime_mk hf 𝔭 hfp, ← mk_mul, ext_iff_val,
      val_mk, val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp; ring⟩
  · obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf x
    obtain ⟨m, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hf y
    rw [RingHom.algebraMap_toAlgebra,
      awayToAtPrime_mk hf 𝔭 hfp, awayToAtPrime_mk hf 𝔭 hfp, ext_iff_val, val_mk, val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hxy
    obtain ⟨⟨c, hc⟩, hce⟩ := hxy
    simp only at hce
    -- `w` is homogeneous, so a single graded component of `c` already kills it.
    have hw : a * f ^ m - b * f ^ n ∈ 𝒜 (n • 1 + m • 1) := by
      refine sub_mem ?_ ?_
      · exact SetLike.mul_mem_graded ha (by simpa using SetLike.pow_mem_graded m hf)
      · rw [add_comm (n • 1) (m • 1)]
        exact SetLike.mul_mem_graded hb (by simpa using SetLike.pow_mem_graded n hf)
    have hcw : c * (a * f ^ m - b * f ^ n) = 0 := by
      rw [mul_sub, sub_eq_zero]
      linear_combination hce
    obtain ⟨j, hj⟩ := exists_decompose_notMem 𝔭 hp hc
    have hdec : (DirectSum.decompose 𝒜 c j : A) * (a * f ^ m - b * f ^ n) = 0 :=
      decompose_mul_eq_zero hw hcw
    have hjmem : (DirectSum.decompose 𝒜 c j : A) ∈ 𝒜 (j • 1) := by
      simp
    refine ⟨⟨Away.mk 𝒜 hf j (DirectSum.decompose 𝒜 c j : A) hjmem, ?_⟩, ?_⟩
    · refine (notMem_awayPrime_iff 𝔭 hfp).2 ?_
      rw [awayToAtPrime_mk hf 𝔭 hfp]
      exact isUnit_mk_of_num_notMem 𝔭 hj
    · rw [ext_iff_val, val_mul, val_mul, Away.val_mk, Away.val_mk, Away.val_mk,
        Localization.mk_mul, Localization.mk_mul, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
      linear_combination (f ^ j : A) * hdec

end

end Hartshorne
