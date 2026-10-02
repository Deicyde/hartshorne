/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.HypersurfaceHilbertPolynomial
import Hartshorne.Intersection.HypersurfaceSectionComponentsEquidimensional
import Hartshorne.Intersection.ProjectiveDegreePositive
import Hartshorne.Intersection.ProjectiveIntersectionMultiplicity
import Hartshorne.Intersection.TopDimensionalPrimeFiltrationLeadingTerm

/-!
# Bézout for a projective variety and a hypersurface

Hartshorne, *Algebraic Geometry*, Theorem I.7.7 (p. 53).
-/

namespace Hartshorne

open DirectSum MvPolynomial Polynomial Set TopologicalSpace
open scoped Polynomial

noncomputable section

universe u

/-- The finite set of irreducible components of a projective intersection. -/
noncomputable def projectiveIntersectionComponents
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    (Y H : Set (ProjectiveSpace k σ)) :
    Finset (irreducibleComponents ↥(Y ∩ H)) := by
  classical
  letI : Fintype (irreducibleComponents ↥(Y ∩ H)) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.fintype
  exact Finset.univ

@[simp]
theorem mem_projectiveIntersectionComponents
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    (Y H : Set (ProjectiveSpace k σ))
    (Z : irreducibleComponents ↥(Y ∩ H)) :
    Z ∈ projectiveIntersectionComponents Y H := by
  classical
  unfold projectiveIntersectionComponents
  simp

/-- **Hartshorne I.7.7, minimal-prime form.** The sum of the intersection
multiplicity times the degree over the top-dimensional minimal primes of a
proper hypersurface section is the product of the two degrees. -/
private theorem projective_hypersurface_bezout_minimalPrimes
    {k : Type u} [Field k] [IsAlgClosed k] {n d r : Nat}
    (hd : 0 < d) (hr0 : 0 < r)
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) (hY : IsProjVariety Y)
    (hYdim : projDim Y = (r : WithBot ℕ∞))
    (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f)
    (hproper : ¬Y ⊆ projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k)))
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            (quotGrading
              (integerHomogeneousSubmodule k (Fin (n + 1)))
              (integerProjVanishingIdeal Y ⊔
                integerProjVanishingIdeal
                  (projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))))) ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            (quotGrading
              (integerHomogeneousSubmodule k (Fin (n + 1)))
              (integerProjVanishingIdeal Y ⊔
                integerProjVanishingIdeal
                  (projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))))) |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1)))
          (quotGrading
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            (integerProjVanishingIdeal Y ⊔
              integerProjVanishingIdeal
                (projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k)))))
          q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤) :
    let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
    let 𝒮 := integerHomogeneousSubmodule k (Fin (n + 1))
    let I := integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H
    let ℳ := quotGrading 𝒮 I
    ∑ P ∈ topDimensionalMinimalAnnihilatorPrimes (r := r - 1) ℳ s,
        (ENat.toNat
            (gradedMultiplicity (MvPolynomial (Fin (n + 1)) k)
              (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) P) : ℚ) *
          projectiveDegree
            (projZeroSet (P.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
      projectiveDegree Y * projectiveDegree H := by
  classical
  dsimp only
  let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  let 𝒮 := integerHomogeneousSubmodule k (Fin (n + 1))
  let I := integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H
  let ℳ := quotGrading 𝒮 I
  let PM := gradedHilbertPolynomial
    (k := k) (n := n) (M := MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) ℳ
  have hn : 0 < n := by
    have hle : projDim Y ≤
        projDim (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) :=
      (Topology.IsEmbedding.inclusion
        (Set.subset_univ Y)).isInducing.topologicalKrullDim_le
    rw [hYdim, projDim_univ_fin] at hle
    have hrn : r ≤ n := by exact_mod_cast hle
    omega
  have hsection := hypersurfaceSection_hilbertPolynomial_and_leadingCoeff
    hd hr0 Y hY hYdim f hf hfirr hproper
  have hPMdeg : PM.natDegree = r - 1 := by
    simpa [PM, ℳ, I, 𝒮, H] using hsection.2.1
  have hPMlc : PM.leadingCoeff =
      (d : ℚ) * projectiveDegree Y * (((r - 1).factorial : Nat) : ℚ)⁻¹ := by
    simpa [PM, ℳ, I, 𝒮, H] using hsection.2.2
  have hYdeg : 0 < projectiveDegree Y :=
    projectiveDegree_pos hY.isProjAlgebraicSet hY.1.nonempty
  have hPMlc0 : PM.leadingCoeff ≠ 0 := by
    rw [hPMlc]
    positivity
  have hPM0 : PM ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hPMlc0
  have hsupportDim : projDim (projZeroSet
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
        (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) :
          Set (MvPolynomial (Fin (n + 1)) k))) =
        ((r - 1 : Nat) : WithBot ℕ∞) := by
    have hdegree := gradedHilbertPolynomial_degree
      (k := k) (n := n) (M := MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) ℳ
    rw [show gradedHilbertPolynomial
      (k := k) (n := n) (M := MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) ℳ =
        PM from rfl, hilbertPolynomialDegree, if_neg hPM0, hPMdeg] at hdegree
    exact hdegree.symm
  have hcoeff := gradedHilbertPolynomial_coeff_eq_sum_minimalPrimes
    ℳ s hshead hslast hsupportDim
  have hcoefflc : PM.coeff (r - 1) = PM.leadingCoeff := by
    rw [← hPMdeg, Polynomial.coeff_natDegree]
  have hsum :
      ∑ P ∈ topDimensionalMinimalAnnihilatorPrimes (r := r - 1) ℳ s,
          (ENat.toNat
              (gradedMultiplicity (MvPolynomial (Fin (n + 1)) k)
                (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) P) : ℚ) *
            projectiveDegree
              (projZeroSet (P.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
        (d : ℚ) * projectiveDegree Y := by
    change PM.coeff (r - 1) = _ at hcoeff
    rw [hcoefflc, hPMlc] at hcoeff
    have hfac : (((r - 1).factorial : Nat) : ℚ) ≠ 0 := by positivity
    field_simp [hfac] at hcoeff ⊢
    linarith
  have hHdeg := (hypersurface_hilbertPolynomial_and_degree
    (k := k) hn hd f hf hfirr).2
  rw [hHdeg]
  rw [hsum]
  ring

/-- **Hartshorne I.7.7 (Bézout for a variety and a hypersurface).** If `Y` is
a positive-dimensional projective variety and the irreducible positive-degree
hypersurface `H = Z(f)` does not contain `Y`, then the sum, over the
irreducible components `Z` of `Y ∩ H`, of the intersection multiplicity along
`Z` times the projective degree of `Z` is `deg(Y) * deg(H)`. -/
theorem projective_hypersurface_bezout
    {k : Type u} [Field k] [IsAlgClosed k] {n d r : Nat}
    (hd : 0 < d) (hr0 : 0 < r)
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) (hY : IsProjVariety Y)
    (hYdim : projDim Y = (r : WithBot ℕ∞))
    (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f)
    (hproper : ¬Y ⊆ projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))) :
    let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
    ∑ Z ∈ projectiveIntersectionComponents Y H,
        (projectiveIntersectionMultiplicity hY
            (show IsProjAlgebraicSet H by
              refine ⟨{f}, ?_, rfl⟩
              intro g hg
              rw [Set.mem_singleton_iff] at hg
              subst g
              exact ⟨d, hf⟩) Z : ℚ) *
          projectiveDegree (projectiveComponentCarrier Z.1) =
      projectiveDegree Y * projectiveDegree H := by
  classical
  dsimp only
  let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  let 𝒮 := integerHomogeneousSubmodule k (Fin (n + 1))
  let I := integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H
  let ℳ := quotGrading 𝒮 I
  have hHalg : IsProjAlgebraicSet H := by
    refine ⟨{f}, ?_, rfl⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    exact ⟨d, hf⟩
  have hn : 0 < n := by
    have hle : projDim Y ≤
        projDim (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) :=
      (Topology.IsEmbedding.inclusion
        (Set.subset_univ Y)).isInducing.topologicalKrullDim_le
    rw [hYdim, projDim_univ_fin] at hle
    have hrn : r ≤ n := by exact_mod_cast hle
    omega
  obtain ⟨s, hshead, hslast⟩ := exists_gradedPrimeFiltration 𝒮 ℳ
  let T := topDimensionalMinimalAnnihilatorPrimes (r := r - 1) ℳ s
  have hreindex :
      (∑ Z ∈ projectiveIntersectionComponents Y H,
          (projectiveIntersectionMultiplicity hY hHalg Z : ℚ) *
            projectiveDegree (projectiveComponentCarrier Z.1)) =
        ∑ P ∈ T,
          (ENat.toNat
              (gradedMultiplicity (MvPolynomial (Fin (n + 1)) k)
                (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) P) : ℚ) *
            projectiveDegree
              (projZeroSet (P.1 : Set (MvPolynomial (Fin (n + 1)) k))) := by
    let e := projectiveIntersectionComponentPrimeEquivMinimalPrimes hY hHalg
    apply Finset.sum_bij
        (fun Z _ ↦ projectiveIntersectionComponentPrime hY hHalg Z)
    · intro Z hZ
      apply (mem_topDimensionalMinimalAnnihilatorPrimes_iff
        ℳ s hshead hslast _).2
      constructor
      · exact projectiveIntersectionComponentPrime_isMinimalPrime_annihilator
          hY hHalg Z
      · rw [projectiveIntersectionComponentPrime_projZeroSet hY hHalg Z]
        exact projectiveHypersurfaceSectionComponent_projDim_eq
          hn hr0 hd hY hYdim f hf hfirr hproper Z
    · intro Z₁ hZ₁ Z₂ hZ₂ hprime
      apply e.injective
      apply Subtype.ext
      simpa [e] using hprime
    · intro P hPT
      have hmem := (mem_topDimensionalMinimalAnnihilatorPrimes_iff
        ℳ s hshead hslast P).1 (by simpa [T] using hPT)
      have hPmin : (projectiveIntersectionIdeal Y H).IsMinimalPrime P.1 := by
        have h := hmem.1
        rw [Ideal.annihilator_quotient] at h
        change (projectiveIntersectionIdeal Y H).IsMinimalPrime P.1 at h
        exact h
      have hPhom : IsHomogeneousIdeal P.1 := by
        let J : Ideal (MvPolynomial (Fin (n + 1)) k) :=
          projectiveIntersectionIdeal Y H
        have hJhomNat : IsHomogeneousIdeal J :=
          (isHomogeneousIdeal_homogeneousVanishingIdeal Y).sup
            (isHomogeneousIdeal_homogeneousVanishingIdeal H)
        have hJhom : J.IsHomogeneous 𝒮 :=
          (ideal_isHomogeneous_integer_iff k (Fin (n + 1)) J).2 hJhomNat
        let Qh : Ideal (MvPolynomial (Fin (n + 1)) k) :=
          (P.1.homogeneousCore 𝒮).toIdeal
        have hQhprime : Qh.IsPrime := P.2.homogeneousCore
        have hQhhom : Qh.IsHomogeneous 𝒮 :=
          HomogeneousIdeal.isHomogeneous (P.1.homogeneousCore 𝒮)
        have hJQh : J ≤ Qh :=
          hJhom.toIdeal_homogeneousCore_eq_self.symm.trans_le
            (Ideal.homogeneousCore_mono 𝒮 hPmin.le)
        have hQhP : Qh ≤ P.1 := Ideal.toIdeal_homogeneousCore_le 𝒮 P.1
        have hPQh : P.1 ≤ Qh := hPmin.2 ⟨hQhprime, hJQh⟩ hQhP
        have hPQheq : P.1 = Qh := le_antisymm hPQh hQhP
        apply (ideal_isHomogeneous_integer_iff k (Fin (n + 1)) P.1).1
        rw [hPQheq]
        exact hQhhom
      have hPne :
          (projZeroSet (P.1 : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
        by_contra hne
        have hempty :
            projZeroSet (P.1 : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hne
        have hdim := hmem.2
        have hbot :
            projDim (∅ : Set (ProjectiveSpace k (Fin (n + 1)))) = ⊥ := by
          unfold projDim topologicalKrullDim
          let _ : IsEmpty
              (IrreducibleCloseds
                (↥(∅ : Set (ProjectiveSpace k (Fin (n + 1)))))) :=
            ⟨fun Z ↦ Z.2.1.nonempty.elim fun x ↦ x.2⟩
          exact Order.krullDim_eq_bot
        rw [hempty, hbot] at hdim
        simp at hdim
      let P' : ↥(projectiveIntersectionMinimalPrimes Y H) :=
        ⟨P, hPhom, hPmin, hPne⟩
      obtain ⟨Z, hZ⟩ := e.surjective P'
      refine ⟨Z, mem_projectiveIntersectionComponents Y H Z, ?_⟩
      have hval := congrArg Subtype.val hZ
      simpa [e, P'] using hval
    · intro Z hZ
      simp only [projectiveIntersectionMultiplicity]
      rw [projectiveIntersectionComponentPrime_projZeroSet hY hHalg Z]
      rw [show I.toIdeal = projectiveIntersectionIdeal Y H from rfl]
  have hprime := projective_hypersurface_bezout_minimalPrimes
    hd hr0 Y hY hYdim f hf hfirr hproper s hshead hslast
  change (∑ P ∈ T,
      (ENat.toNat
          (gradedMultiplicity (MvPolynomial (Fin (n + 1)) k)
            (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) P) : ℚ) *
        projectiveDegree
          (projZeroSet (P.1 : Set (MvPolynomial (Fin (n + 1)) k)))) =
    projectiveDegree Y * projectiveDegree H at hprime
  exact hreindex.trans hprime

end

end Hartshorne
