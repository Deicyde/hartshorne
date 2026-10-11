/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Clopen

/-!
# Connected spectra, idempotents, and products

Hartshorne, *Algebraic Geometry*, Exercise II.2.19.

We use separation-based disconnectedness, expressed as failure of preconnectedness.  This makes
the empty spectrum of the zero ring not disconnected, exactly as required for the equivalence with
nonzero orthogonal idempotents and nontrivial product factors.
-/

open TopologicalSpace

namespace Hartshorne

universe u

/-- `Spec A` admits a separation into two nonempty open subsets.  We use `IsPreconnected`, rather
than Mathlib's nonempty-sensitive `IsConnected`, so that the empty spectrum is not disconnected. -/
def IsSpectrumDisconnected (A : Type u) [CommRing A] : Prop :=
  ¬ IsPreconnected (Set.univ : Set (PrimeSpectrum A))

/-- The empty spectrum of a subsingleton ring has no separation. -/
@[simp]
theorem not_isSpectrumDisconnected_of_subsingleton
    (A : Type u) [CommRing A] [Subsingleton A] :
    ¬ IsSpectrumDisconnected A := by
  intro h
  apply h
  have huniv : (Set.univ : Set (PrimeSpectrum A)) = ∅ := by
    ext x
    exact isEmptyElim x
  rw [huniv]
  exact isPreconnected_empty

/-- A decomposition of `1` into two nonzero orthogonal idempotents. -/
def HasNontrivialOrthogonalIdempotents (A : Type u) [CommRing A] : Prop :=
  ∃ e₁ e₂ : A, e₁ ≠ 0 ∧ e₂ ≠ 0 ∧
    IsIdempotentElem e₁ ∧ IsIdempotentElem e₂ ∧ e₁ * e₂ = 0 ∧ e₁ + e₂ = 1

/-- A decomposition as a product of two nonzero commutative rings.  `Nontrivial`, rather than
mere type inhabitation, records that both factors are nonzero rings. -/
def HasNontrivialProductDecomposition (A : Type u) [CommRing A] : Prop :=
  ∃ A₁ A₂ : CommRingCat.{u}, Nontrivial A₁ ∧ Nontrivial A₂ ∧
    Nonempty (A ≃+* (A₁ × A₂))

private theorem basicOpen_nonempty_of_isIdempotentElem_ne_zero
    {A : Type u} [CommRing A] {e : A} (he : IsIdempotentElem e) (hne : e ≠ 0) :
    (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  have hbot : PrimeSpectrum.basicOpen e = ⊥ := by
    apply SetLike.coe_injective
    simpa using h
  exact hne (he.eq_zero_of_isNilpotent ((PrimeSpectrum.basicOpen_eq_bot_iff e).mp hbot))

/-- Separation-based disconnectedness of `Spec A` is equivalent to a nontrivial orthogonal
idempotent decomposition. -/
theorem isSpectrumDisconnected_iff_orthogonalIdempotents
    (A : Type u) [CommRing A] :
    IsSpectrumDisconnected A ↔ HasNontrivialOrthogonalIdempotents A := by
  constructor
  · intro h
    obtain ⟨s, t, hs, -, hsne, htne, hst, -⟩ :=
      isClopen_univ.not_isPreconnected_iff.mp h
    have hscompl : sᶜ.Nonempty := by
      obtain ⟨x, hxt⟩ := htne
      exact ⟨x, fun hxs ↦ Set.disjoint_left.1 hst hxs hxt⟩
    obtain ⟨e₁, e₂, hmul, hadd, hs_eq, hscompl_eq⟩ :=
      PrimeSpectrum.exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen hs
    have he₁ : e₁ ≠ 0 := by
      intro hzero
      subst e₁
      rw [PrimeSpectrum.basicOpen_zero] at hs_eq
      exact hsne.ne_empty hs_eq
    have he₂ : e₂ ≠ 0 := by
      intro hzero
      subst e₂
      rw [PrimeSpectrum.basicOpen_zero] at hscompl_eq
      exact hscompl.ne_empty hscompl_eq
    exact ⟨e₁, e₂, he₁, he₂, (IsIdempotentElem.of_mul_add hmul hadd).1,
      (IsIdempotentElem.of_mul_add hmul hadd).2, hmul, hadd⟩
  · rintro ⟨e₁, e₂, he₁, he₂, idem₁, idem₂, hmul, hadd⟩
    apply isClopen_univ.not_isPreconnected_iff.mpr
    let s : Set (PrimeSpectrum A) := PrimeSpectrum.basicOpen e₁
    let t : Set (PrimeSpectrum A) := PrimeSpectrum.basicOpen e₂
    have hs : IsClopen s :=
      PrimeSpectrum.isClopen_iff.mpr ⟨e₁, idem₁, rfl⟩
    have ht : IsClopen t :=
      PrimeSpectrum.isClopen_iff.mpr ⟨e₂, idem₂, rfl⟩
    have hst : t = sᶜ := by
      dsimp [s, t]
      rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_mul_add e₁ e₂ hmul hadd]
      exact PrimeSpectrum.basicOpen_eq_zeroLocus_compl e₂
    refine ⟨s, t, hs, ht,
      basicOpen_nonempty_of_isIdempotentElem_ne_zero idem₁ he₁,
      basicOpen_nonempty_of_isIdempotentElem_ne_zero idem₂ he₂, ?_, ?_⟩
    · rw [hst]
      exact disjoint_compl_right
    · rw [hst, Set.union_compl_self]

private theorem quotient_span_nontrivial_of_complement_ne_zero
    {A : Type u} [CommRing A] {e f : A}
    (he : IsIdempotentElem e) (hf : f ≠ 0) (hadd : e + f = 1) :
    Nontrivial (A ⧸ Ideal.span {e}) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro htop
  have hu : IsUnit e := Ideal.span_singleton_eq_top.mp htop
  have heq : e = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp he
  apply hf
  exact add_left_cancel (by simpa only [add_zero] using hadd.trans heq.symm)

/-- A nontrivial orthogonal idempotent decomposition is equivalent to a product decomposition
with two nonzero commutative-ring factors. -/
theorem orthogonalIdempotents_iff_productDecomposition
    (A : Type u) [CommRing A] :
    HasNontrivialOrthogonalIdempotents A ↔ HasNontrivialProductDecomposition A := by
  constructor
  · rintro ⟨e₁, e₂, he₁, he₂, idem₁, idem₂, hmul, hadd⟩
    have hq₁ : Nontrivial (A ⧸ Ideal.span {e₁}) :=
      quotient_span_nontrivial_of_complement_ne_zero idem₁ he₂ hadd
    have hq₂ : Nontrivial (A ⧸ Ideal.span {e₂}) :=
      quotient_span_nontrivial_of_complement_ne_zero idem₂ he₁ (by simpa [add_comm] using hadd)
    refine ⟨CommRingCat.of (A ⧸ Ideal.span {e₁}),
      CommRingCat.of (A ⧸ Ideal.span {e₂}), hq₁, hq₂, ?_⟩
    exact ⟨(AlgEquiv.prodQuotientOfIsIdempotentElem
      (R := A) idem₁ idem₂ hadd hmul).toRingEquiv⟩
  · rintro ⟨A₁, A₂, hA₁, hA₂, ⟨e⟩⟩
    let _ : Nontrivial A₁ := hA₁
    let _ : Nontrivial A₂ := hA₂
    let e₁ : A := e.symm (1, 0)
    let e₂ : A := e.symm (0, 1)
    have he₁ : e₁ ≠ 0 := by
      intro h
      have := congrArg e h
      simp [e₁] at this
    have he₂ : e₂ ≠ 0 := by
      intro h
      have := congrArg e h
      simp [e₂] at this
    have idem₁ : IsIdempotentElem e₁ := by
      rw [IsIdempotentElem]
      apply e.injective
      simp [e₁]
    have idem₂ : IsIdempotentElem e₂ := by
      rw [IsIdempotentElem]
      apply e.injective
      simp [e₂]
    refine ⟨e₁, e₂, he₁, he₂, idem₁, idem₂, ?_, ?_⟩
    · apply e.injective
      simp [e₁, e₂]
    · apply e.injective
      simp [e₁, e₂]

/-- **Hartshorne II.2, Exercise 2.19.** A prime spectrum admits a separation exactly when the
ring has nonzero complementary orthogonal idempotents, equivalently when it is a product of two
nonzero rings.  The statement includes the zero ring. -/
theorem disconnectedSpectrum_idempotents_products_tfae
    (A : Type u) [CommRing A] :
    List.TFAE
      [IsSpectrumDisconnected A,
       HasNontrivialOrthogonalIdempotents A,
       HasNontrivialProductDecomposition A] := by
  tfae_have 1 → 2 := (isSpectrumDisconnected_iff_orthogonalIdempotents A).mp
  tfae_have 2 → 1 := (isSpectrumDisconnected_iff_orthogonalIdempotents A).mpr
  tfae_have 2 → 3 := (orthogonalIdempotents_iff_productDecomposition A).mp
  tfae_have 3 → 2 := (orthogonalIdempotents_iff_productDecomposition A).mpr
  tfae_finish

/-- For a nonzero ring, separation-based disconnectedness agrees with failure of Mathlib's
nonempty-sensitive connectedness predicate. -/
theorem isSpectrumDisconnected_iff_not_isConnected
    (A : Type u) [CommRing A] [Nontrivial A] :
    IsSpectrumDisconnected A ↔
      ¬ IsConnected (Set.univ : Set (PrimeSpectrum A)) := by
  simp [IsSpectrumDisconnected, IsConnected]

end Hartshorne
