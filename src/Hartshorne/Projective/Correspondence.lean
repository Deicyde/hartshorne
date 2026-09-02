/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Irrelevant
import Hartshorne.Projective.Variety

/-!
# Algebraic sets and homogeneous radical ideals

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.4 (p. 11), with Exercise 2.2.

`Y ↦ J(Y)` and `𝔞 ↦ Z(𝔞)` are mutually inverse, inclusion-reversing bijections
between the algebraic sets of `ℙⁿ` and the homogeneous radical ideals other than
the irrelevant ideal `S₊`.

The exclusion of `S₊` is the only genuine difference from the affine case.
`S₊` is a proper homogeneous radical ideal whose zero set is empty, and the
empty set already corresponds to `S`. Exercise 2.2 says these are the only such
ideals, because `S₊` is maximal.

## Main results

* `Hartshorne.homogeneousVanishingIdeal_projZeroSet` : `J(Z(𝔞)) = √𝔞` when
  `Z(𝔞)` is nonempty.
* `Hartshorne.isIrreducible_iff_isPrime_homogeneousVanishingIdeal` : Exercise
  2.4's second half.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- Every member of `J(Y)` vanishes on `Y`, not just the homogeneous
generators. -/
theorem eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal {Y : Set (ProjectiveSpace k σ)}
    {f : MvPolynomial σ k} (hf : f ∈ homogeneousVanishingIdeal Y)
    {P : ProjectiveSpace k σ} (hP : P ∈ Y) : eval P.rep f = 0 := by
  refine Submodule.span_induction (p := fun g _ => eval P.rep g = 0) ?_ ?_ ?_ ?_ hf
  · exact fun g hg => hg.2 P hP
  · simp
  · intro g h _ _ hg hh; rw [map_add, hg, hh, add_zero]
  · intro a g _ hg; rw [smul_eq_mul, map_mul, hg, mul_zero]

/-- The irrelevant ideal is maximal: it is the ideal of a point of affine
space. -/
theorem irrelevantIdeal_isMaximal : (irrelevantIdeal k σ).IsMaximal := by
  rw [← vanishingIdeal_singleton_zero]
  infer_instance

section AlgClosed

variable [IsAlgClosed k] [Finite σ]

/-- **Exercise 2.4**, the key step: `J(Z(𝔞)) = √𝔞` for a homogeneous ideal with
nonempty zero set.

Nonemptiness is what kills the degree-zero part: a nonzero constant is
homogeneous and vanishes nowhere, so it cannot lie in `J` of a nonempty set. -/
theorem homogeneousVanishingIdeal_projZeroSet {I : Ideal (MvPolynomial σ k)}
    (hI : IsHomogeneousIdeal I) (hne : (projZeroSet (I : Set (MvPolynomial σ k))).Nonempty) :
    homogeneousVanishingIdeal (projZeroSet (I : Set (MvPolynomial σ k))) = I.radical := by
  refine le_antisymm (Ideal.span_le.2 fun f hf => ?_) ?_
  · obtain ⟨n, hn⟩ := hf.1
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · -- Degree zero: `f` is a constant, and it vanishes somewhere.
      obtain ⟨P, hP⟩ := hne
      have hdeg0 : f.totalDegree = 0 :=
        (totalDegree_zero_iff_isHomogeneous (σ := σ) (p := f)).2 hn
      have hC : f = C (coeff 0 f) :=
        (totalDegree_eq_zero_iff_eq_C (p := f)).1 hdeg0
      have : coeff 0 f = 0 := by
        have := hf.2 P hP
        rw [HomogeneousVanish, hC] at this
        simpa using this
      rw [hC, this, map_zero]
      exact Ideal.zero_mem _
    · obtain ⟨q, hq, hmem⟩ :=
        exists_pow_mem_of_forall_homogeneousVanish hI hpos hn (fun P hP => hf.2 P hP)
      exact ⟨q, hmem⟩
  · -- Conversely a homogeneous element of `√𝔞` vanishes on `Z(𝔞)`.
    obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists
      (𝒜 := homogeneousSubmodule σ k) (I := I.radical)).1 hI.radical
    rw [hS, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    refine Ideal.subset_span ⟨isHomogeneousElem_iff.1 (g : _).2, fun P hP => ?_⟩
    obtain ⟨q, hq⟩ : (g : MvPolynomial σ k) ∈ I.radical := by
      rw [hS]; exact Ideal.subset_span ⟨g, hg, rfl⟩
    have : (eval P.rep (g : MvPolynomial σ k)) ^ q = 0 := by
      rw [← map_pow]; exact hP _ hq
    exact pow_eq_zero_iff'.1 this |>.1

/-- `J(Y)` is radical for an algebraic set `Y`. -/
theorem isRadical_homogeneousVanishingIdeal {Y : Set (ProjectiveSpace k σ)}
    (hY : IsProjAlgebraicSet Y) (hne : Y.Nonempty) :
    (homogeneousVanishingIdeal Y).IsRadical := by
  obtain ⟨T, hT, rfl⟩ := hY
  have halg : IsProjAlgebraicSet (projZeroSet T) := ⟨T, hT, rfl⟩
  have hspan : projZeroSet ((Ideal.span T : Ideal (MvPolynomial σ k))
      : Set (MvPolynomial σ k)) = projZeroSet T := projZeroSet_span T
  have hIhom : IsHomogeneousIdeal (Ideal.span T : Ideal (MvPolynomial σ k)) :=
    Ideal.homogeneous_span _ _ fun f hf => isHomogeneousElem_iff.2 (hT f hf)
  rw [← hspan] at hne ⊢
  rw [homogeneousVanishingIdeal_projZeroSet hIhom hne]
  exact Ideal.radical_isRadical _

/-- **Exercise 2.4**, second half: an algebraic set is irreducible exactly when
its homogeneous ideal is prime.

The forward direction uses the homogeneous prime test, which is what makes the
graded background node earn its keep: primeness need only be checked on
homogeneous elements, and those are the ones cutting out closed sets. -/
theorem isIrreducible_iff_isPrime_homogeneousVanishingIdeal
    {Y : Set (ProjectiveSpace k σ)} (hY : IsProjAlgebraicSet Y) :
    IsIrreducible Y ↔ (homogeneousVanishingIdeal Y).IsPrime := by
  constructor
  · rintro ⟨hne, hpre⟩
    refine (IsHomogeneousIdeal.isPrime_iff
      (isHomogeneousIdeal_homogeneousVanishingIdeal Y)).2 ⟨?_, ?_⟩
    · intro htop
      obtain ⟨P, hP⟩ := hne
      have h1 : (1 : MvPolynomial σ k) ∈ homogeneousVanishingIdeal Y :=
        (Ideal.eq_top_iff_one _).1 htop
      have := eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal h1 hP
      simp at this
    · intro f g hf hg hfg
      have hfhom : IsHomogeneousSet ({f} : Set (MvPolynomial σ k)) := by
        rintro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hf
      have hghom : IsHomogeneousSet ({g} : Set (MvPolynomial σ k)) := by
        rintro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hg
      have hcov : Y ⊆ projZeroSet {f} ∪ projZeroSet {g} := by
        intro P hP
        have hz := eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal hfg hP
        rw [map_mul] at hz
        rcases mul_eq_zero.1 hz with h | h
        · refine Or.inl fun x hx => ?_
          rw [Set.mem_singleton_iff] at hx; subst hx; exact h
        · refine Or.inr fun x hx => ?_
          rw [Set.mem_singleton_iff] at hx; subst hx; exact h
      rcases isPreirreducible_iff_isClosed_union_isClosed.1 hpre _ _
        (isClosed_projZeroSet_of_isHomogeneousSet hfhom)
        (isClosed_projZeroSet_of_isHomogeneousSet hghom) hcov with h | h
      · exact Or.inl (Ideal.subset_span ⟨hf, fun P hP => h hP f rfl⟩)
      · exact Or.inr (Ideal.subset_span ⟨hg, fun P hP => h hP g rfl⟩)
  · intro hp
    refine ⟨?_, ?_⟩
    · rw [Set.nonempty_iff_ne_empty]
      intro hempty
      refine hp.ne_top ?_
      rw [hempty]
      refine (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨⟨0, isHomogeneous_one σ k⟩, ?_⟩)
      simp
    · rw [isPreirreducible_iff_isClosed_union_isClosed]
      intro z₁ z₂ hz₁ hz₂ hcov
      by_contra hcon
      rw [not_or, Set.not_subset, Set.not_subset] at hcon
      obtain ⟨⟨P, hPY, hPz₁⟩, ⟨Q, hQY, hQz₂⟩⟩ := hcon
      obtain ⟨f, hf, hfP⟩ : ∃ f ∈ homogeneousVanishingSet z₁, ¬ HomogeneousVanish f P := by
        by_contra hc
        push Not at hc
        exact hPz₁ ((isClosed_iff_isProjAlgebraicSet.1 hz₁).projZeroSet_homogeneousVanishingSet
          ▸ hc)
      obtain ⟨g, hg, hgQ⟩ : ∃ g ∈ homogeneousVanishingSet z₂, ¬ HomogeneousVanish g Q := by
        by_contra hc
        push Not at hc
        exact hQz₂ ((isClosed_iff_isProjAlgebraicSet.1 hz₂).projZeroSet_homogeneousVanishingSet
          ▸ hc)
      have hfg : f * g ∈ homogeneousVanishingIdeal Y := by
        refine Ideal.subset_span ⟨?_, fun R hR => ?_⟩
        · obtain ⟨m, hm⟩ := hf.1
          obtain ⟨n, hn⟩ := hg.1
          exact ⟨m + n, hm.mul hn⟩
        · show eval R.rep (f * g) = 0
          rw [map_mul]
          rcases hcov hR with h | h
          · rw [hf.2 R h, zero_mul]
          · rw [hg.2 R h, mul_zero]
      rcases hp.2 hfg with h | h
      · exact hfP (eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal h hPY)
      · exact hgQ (eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal h hQY)

end AlgClosed

end Hartshorne
