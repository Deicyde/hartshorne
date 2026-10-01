/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.GradedPrimeFiltration
import Mathlib.RingTheory.Support

/-!
# Supports of graded prime filtrations

Hartshorne, *Algebraic Geometry*, Proposition I.7.4(a) (p. 50).
-/

namespace Hartshorne

noncomputable section

variable {R A M : Type*}
  [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (𝓐 : ℤ → Submodule R A) [GradedAlgebra 𝓐]
  (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝓐 ℳ]

/-- A specified prime occurring in one step of a graded prime filtration. -/
def IsGradedPrimeFiltrationFactor
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) (p : PrimeSpectrum A) : Prop :=
  ∃ h : N₁ ≤ N₂, ∃ hp : p.1.IsHomogeneous 𝓐, ∃ l : ℤ,
    Nonempty <| GradedLinearEquiv A
      (gradedModuleTwist
        (gradedQuotientPiece 𝓐 𝓐 (homogeneousIdealSubmodule 𝓐 p.1 hp)) l)
      (gradedFactorPiece 𝓐 ℳ N₁ N₂ h)

/-- Type-valued data carried by one graded prime-filtration step.  Unlike the
proposition-valued step relation, this record can be selected once and reused
by later constructions. -/
structure GradedPrimeFiltrationFactorData
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) where
  le : N₁ ≤ N₂
  prime : PrimeSpectrum A
  homogeneous : prime.1.IsHomogeneous 𝓐
  twist : ℤ
  equiv : GradedLinearEquiv A
    (gradedModuleTwist
      (gradedQuotientPiece 𝓐 𝓐
        (homogeneousIdealSubmodule 𝓐 prime.1 homogeneous)) twist)
    (gradedFactorPiece 𝓐 ℳ N₁ N₂ le)

theorem nonempty_gradedPrimeFiltrationFactorData_iff
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) :
    Nonempty (GradedPrimeFiltrationFactorData 𝓐 ℳ N₁ N₂) ↔
      IsGradedPrimeFiltrationStep 𝓐 ℳ N₁ N₂ := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.le, d.prime, d.homogeneous, d.twist, ⟨d.equiv⟩⟩
  · rintro ⟨h, p, hp, l, ⟨e⟩⟩
    exact ⟨⟨h, p, hp, l, e⟩⟩

/-- A stable noncomputable choice of all data in one filtration step. -/
noncomputable def gradedPrimeFiltrationFactorDataOfStep
    {N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ}
    (h : IsGradedPrimeFiltrationStep 𝓐 ℳ N₁ N₂) :
    GradedPrimeFiltrationFactorData 𝓐 ℳ N₁ N₂ :=
  Classical.choice <|
    (nonempty_gradedPrimeFiltrationFactorData_iff 𝓐 ℳ N₁ N₂).2 h

/-- The predicate that a prime occurs among the factors of a specified
graded prime filtration. -/
def IsGradedPrimeFiltrationFactorOf
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (p : PrimeSpectrum A) : Prop :=
  ∃ i : Fin s.length,
    IsGradedPrimeFiltrationFactor 𝓐 ℳ
      (s (Fin.castSucc i)) (s i.succ) p

/-- The selected factor data at index `i` of a graded prime filtration. -/
noncomputable def gradedPrimeFiltrationFactorDataAt
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (i : Fin s.length) :
    GradedPrimeFiltrationFactorData 𝓐 ℳ
      (s (Fin.castSucc i)) (s i.succ) :=
  gradedPrimeFiltrationFactorDataOfStep 𝓐 ℳ (s.step i)

/-- The canonically selected prime attached to the `i`-th filtration
factor. -/
noncomputable def gradedPrimeFiltrationFactorPrime
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (i : Fin s.length) : PrimeSpectrum A :=
  (gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i).prime

theorem gradedPrimeFiltrationFactorPrime_spec
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (i : Fin s.length) :
    IsGradedPrimeFiltrationFactor 𝓐 ℳ
      (s (Fin.castSucc i)) (s i.succ)
      (gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i) := by
  let d := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
  exact ⟨d.le, d.homogeneous, d.twist, ⟨d.equiv⟩⟩

theorem isGradedPrimeFiltrationStep_iff_exists_factor
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) :
    IsGradedPrimeFiltrationStep 𝓐 ℳ N₁ N₂ ↔
      ∃ p : PrimeSpectrum A,
        IsGradedPrimeFiltrationFactor 𝓐 ℳ N₁ N₂ p := by
  constructor
  · rintro ⟨h, p, hp, l, e⟩
    exact ⟨p, h, hp, l, e⟩
  · rintro ⟨p, h, hp, l, e⟩
    exact ⟨h, p, hp, l, e⟩

/-- The annihilator of a filtration factor is its recorded prime. -/
theorem annihilator_gradedFactorPiece_eq
    {N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ} {p : PrimeSpectrum A}
    (h : N₁ ≤ N₂)
    (hp : IsGradedPrimeFiltrationFactor 𝓐 ℳ N₁ N₂ p) :
    Module.annihilator A
        (N₂ ⧸ (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule) =
      p.1 := by
  obtain ⟨h', hph, l, ⟨e⟩⟩ := hp
  change Module.annihilator A
      (N₂ ⧸ (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h').toSubmodule) = p.1
  rw [← e.toLinearEquiv.annihilator_eq]
  exact Ideal.annihilator_quotient

/-- The product of the annihilator of a submodule and the annihilator of the
corresponding quotient annihilates the middle module. -/
theorem annihilator_mul_factor_le
    {N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ} (h : N₁ ≤ N₂) :
    Module.annihilator A N₁ *
        Module.annihilator A
          (N₂ ⧸ (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule) ≤
      Module.annihilator A N₂ := by
  rw [Ideal.mul_le]
  intro a ha b hb
  rw [Module.mem_annihilator] at ha hb ⊢
  intro y
  have hbq := hb (Submodule.Quotient.mk y)
  rw [← Submodule.Quotient.mk_smul] at hbq
  have hby : b • y ∈ (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule :=
    (Submodule.Quotient.mk_eq_zero _).mp hbq
  have ha0 := ha (⟨b • (y : M), hby⟩ : N₁)
  apply Subtype.ext
  change (a * b) • (y : M) = 0
  rw [mul_smul]
  exact congrArg (fun z : N₁ => (z : M)) ha0

/-- Across one prime-filtration step, containment of the middle
annihilator in a prime is equivalent to containment for the preceding term
or containment of one of the recorded factor primes. -/
theorem annihilator_le_iff_of_gradedPrimeFiltrationStep
    {N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ} (P : PrimeSpectrum A)
    (hstep : IsGradedPrimeFiltrationStep 𝓐 ℳ N₁ N₂) :
    Module.annihilator A N₂ ≤ P.1 ↔
      Module.annihilator A N₁ ≤ P.1 ∨
        ∃ q : PrimeSpectrum A,
          IsGradedPrimeFiltrationFactor 𝓐 ℳ N₁ N₂ q ∧ q.1 ≤ P.1 := by
  obtain ⟨q₀, hq₀⟩ :=
    (isGradedPrimeFiltrationStep_iff_exists_factor 𝓐 ℳ N₁ N₂).mp hstep
  obtain ⟨h₀, hp₀, l₀, e₀⟩ := hq₀
  have hq₀' : IsGradedPrimeFiltrationFactor 𝓐 ℳ N₁ N₂ q₀ :=
    ⟨h₀, hp₀, l₀, e₀⟩
  constructor
  · intro hN₂
    have hprod : Module.annihilator A N₁ * q₀.1 ≤ P.1 := by
      rw [← annihilator_gradedFactorPiece_eq 𝓐 ℳ h₀ hq₀']
      exact (annihilator_mul_factor_le 𝓐 ℳ h₀).trans hN₂
    rcases P.2.mul_le.mp hprod with hN₁ | hq
    · exact Or.inl hN₁
    · exact Or.inr ⟨q₀, hq₀', hq⟩
  · rintro (hN₁ | ⟨q, hq, hqP⟩)
    · exact (Submodule.annihilator_mono h₀).trans hN₁
    · obtain ⟨h, hp, l, e⟩ := hq
      have hquot : Module.annihilator A N₂ ≤
          Module.annihilator A
            (N₂ ⧸ (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule) :=
        LinearMap.annihilator_le_of_surjective
          (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule.mkQ
          (Submodule.mkQ_surjective _)
      rw [annihilator_gradedFactorPiece_eq 𝓐 ℳ h ⟨h, hp, l, e⟩] at hquot
      exact hquot.trans hqP

private theorem annihilator_le_iff_before
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (P : PrimeSpectrum A) :
    ∀ (n : ℕ) (hn : n ≤ s.length),
      Module.annihilator A
          (s ⟨n, Nat.lt_succ_of_le hn⟩) ≤ P.1 ↔
        Module.annihilator A s.head ≤ P.1 ∨
          ∃ i : Fin s.length, i.1 < n ∧
            ∃ q : PrimeSpectrum A,
              IsGradedPrimeFiltrationFactor 𝓐 ℳ
                  (s (Fin.castSucc i)) (s i.succ) q ∧
                q.1 ≤ P.1 := by
  intro n hn
  induction n with
  | zero =>
      constructor
      · exact fun h ↦ Or.inl h
      · rintro (h | ⟨i, hi, _⟩)
        · exact h
        · omega
  | succ n ih =>
      have hnlt : n < s.length := Nat.lt_of_succ_le hn
      let i : Fin s.length := ⟨n, hnlt⟩
      have hnle : n ≤ s.length := Nat.le_trans (Nat.le_succ n) hn
      have hstep := annihilator_le_iff_of_gradedPrimeFiltrationStep 𝓐 ℳ P (s.step i)
      constructor
      · intro hcur
        rcases hstep.mp hcur with hprev | ⟨q, hq, hqP⟩
        · rcases (ih hnle).mp hprev with hhead | ⟨j, hj, q, hq, hqP⟩
          · exact Or.inl hhead
          · exact Or.inr ⟨j, hj.trans (Nat.lt_succ_self n), q, hq, hqP⟩
        · exact Or.inr ⟨i, Nat.lt_succ_self n, q, hq, hqP⟩
      · rintro (hhead | ⟨j, hj, q, hq, hqP⟩)
        · apply hstep.mpr
          exact Or.inl ((ih hnle).mpr (Or.inl hhead))
        · by_cases hjn : j.1 < n
          · apply hstep.mpr
            exact Or.inl ((ih hnle).mpr (Or.inr ⟨j, hjn, q, hq, hqP⟩))
          · have hjval : j.1 = n := by omega
            have hji : j = i := by
              apply Fin.ext
              simpa [i] using hjval
            subst j
            exact hstep.mpr (Or.inr ⟨q, hq, hqP⟩)

/-- The annihilator of the filtered module is contained in a prime `P`
exactly when one of the recorded homogeneous factor primes is contained in
`P`.  This is slightly stronger than the source, which only applies the
statement to homogeneous `P`. -/
theorem gradedPrimeFiltration_annihilator_le_iff
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (P : PrimeSpectrum A) :
    Module.annihilator A M ≤ P.1 ↔
      ∃ q : PrimeSpectrum A,
        IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s q ∧ q.1 ≤ P.1 := by
  have hhead : Module.annihilator A s.head = ⊤ := by
    rw [hshead]
    change (⊥ : Submodule A M).annihilator = ⊤
    exact Submodule.annihilator_bot
  have hlast : Module.annihilator A s.last = Module.annihilator A M := by
    rw [hslast]
    change (⊤ : Submodule A M).annihilator = Module.annihilator A M
    exact Submodule.annihilator_top
  have h := annihilator_le_iff_before 𝓐 ℳ s P s.length le_rfl
  rw [show s ⟨s.length, Nat.lt_succ_self s.length⟩ = s.last from rfl,
    hlast, hhead] at h
  constructor
  · intro hAnn
    rcases h.mp hAnn with htop | ⟨i, hi, q, hq, hqP⟩
    · exact (P.2.ne_top (top_unique htop)).elim
    · exact ⟨q, ⟨i, hq⟩, hqP⟩
  · rintro ⟨q, ⟨i, hq⟩, hqP⟩
    apply h.mpr
    exact Or.inr ⟨i, i.2, q, hq, hqP⟩

/-- A prime occurs as a filtration factor exactly when it equals the stable
chosen prime at some filtration index. -/
theorem isGradedPrimeFiltrationFactorOf_iff_exists_factorPrime_eq
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (p : PrimeSpectrum A) :
    IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s p ↔
      ∃ i : Fin s.length,
        gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i = p := by
  constructor
  · rintro ⟨i, hp⟩
    have hchosen := gradedPrimeFiltrationFactorPrime_spec 𝓐 ℳ s i
    let h := hp.choose
    have hpann := annihilator_gradedFactorPiece_eq 𝓐 ℳ h hp
    have hchosenAnn := annihilator_gradedFactorPiece_eq 𝓐 ℳ h hchosen
    refine ⟨i, ?_⟩
    apply PrimeSpectrum.ext
    exact hchosenAnn.symm.trans hpann
  · rintro ⟨i, rfl⟩
    exact ⟨i, gradedPrimeFiltrationFactorPrime_spec 𝓐 ℳ s i⟩

/-- The set of prime ideals occurring in a finite graded prime filtration is
finite. -/
theorem finite_isGradedPrimeFiltrationFactorOf
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2}) :
    {p : PrimeSpectrum A |
      IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s p}.Finite := by
  have hrange :
      {p : PrimeSpectrum A |
        IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s p} =
        Set.range (gradedPrimeFiltrationFactorPrime 𝓐 ℳ s) := by
    ext p
    rw [Set.mem_ofPred_eq, Set.mem_range,
      isGradedPrimeFiltrationFactorOf_iff_exists_factorPrime_eq]
  rw [hrange]
  exact Set.finite_range _

/-- The minimal factor primes of a graded prime filtration are exactly the
prime ideals minimal over the annihilator of the filtered module. -/
theorem gradedPrimeFiltration_minimal_factor_iff
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (P : PrimeSpectrum A) :
    Minimal (IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s) P ↔
      (Module.annihilator A M).IsMinimalPrime P.1 := by
  constructor
  · intro hmin
    have hAnnP : Module.annihilator A M ≤ P.1 :=
      (gradedPrimeFiltration_annihilator_le_iff 𝓐 ℳ s hshead hslast P).2
        ⟨P, hmin.prop, le_rfl⟩
    refine ⟨⟨P.2, hAnnP⟩, ?_⟩
    intro J hJ hJP
    let Q : PrimeSpectrum A := ⟨J, hJ.1⟩
    obtain ⟨q, hq, hqJ⟩ :=
      (gradedPrimeFiltration_annihilator_le_iff 𝓐 ℳ s hshead hslast Q).1 hJ.2
    have hqP : q ≤ P := hqJ.trans hJP
    exact (hmin.2 hq hqP).trans hqJ
  · intro hmin
    obtain ⟨q, hq, hqP⟩ :=
      (gradedPrimeFiltration_annihilator_le_iff 𝓐 ℳ s hshead hslast P).1 hmin.le
    have hAnnq : Module.annihilator A M ≤ q.1 :=
      (gradedPrimeFiltration_annihilator_le_iff 𝓐 ℳ s hshead hslast q).2
        ⟨q, hq, le_rfl⟩
    have hPq : P ≤ q := hmin.2 ⟨q.2, hAnnq⟩ hqP
    have hpq : q = P := le_antisymm hqP hPq
    subst q
    refine ⟨hq, ?_⟩
    intro Q hQ hQP
    have hAnnQ : Module.annihilator A M ≤ Q.1 :=
      (gradedPrimeFiltration_annihilator_le_iff 𝓐 ℳ s hshead hslast Q).2
        ⟨Q, hQ, le_rfl⟩
    exact hmin.2 ⟨Q.2, hAnnQ⟩ hQP

end


end Hartshorne
