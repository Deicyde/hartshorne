/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ProjectiveHypersurfaceBezout
import Hartshorne.Intersection.ProjectiveProperClosedDimensionDrop
import Hartshorne.Intersection.ProjectiveZeroDimensionalVarietyPoint
import Hartshorne.Scheme.ProjectiveIntersectionDegree
import Hartshorne.Scheme.ProjectiveLocalIntersectionMultiplicity

/-!
# The degree of an ambient hypersurface section

Hartshorne, *Algebraic Geometry*, Exercise II.6.2(c) (p. 146).

Let `k` be algebraically closed, `ι : X ⟶ ℙⁿ_k` a closed immersion of a scheme satisfying `(*)`,
`𝔭` the homogeneous prime of the image of the generic point, and `V` a prime divisor of `ℙⁿ_k`
with equation `f`, not containing `X`. The prime divisors of `X` on `V` correspond to the
irreducible components of the classical intersection `Z(𝔭) ∩ Z(f)`, and the coefficient of `V · X`
along each is the intersection multiplicity of Theorem I.7.7. Bézout's theorem then gives
`deg (V · X) = deg V · deg X`, provided `dim X ≥ 1`, i.e. `X` is not a single point; for a point
not on `V` the left side is `0` while the right side is `deg f ≥ 1`.

## Main results

* `Hartshorne.closedImmersionComponentEquiv`: prime divisors of `X` on `V` and components of
  `Z(𝔭) ∩ Z(f)`.
* `Hartshorne.projectiveIntersectionDivisor_apply_eq_projectiveIntersectionMultiplicity`: the
  coefficients of `V · X` are the local intersection multiplicities.
* `Hartshorne.weilDivisorProjectiveDegree_projectiveIntersectionDivisor`:
  `deg (V · X) = deg V · deg X`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) k

local notation "S" => MvPolynomial (Fin (n + 1)) k

/-- A homogeneous prime has a nonempty projective zero set exactly when it is relevant. -/
theorem projZeroSet_nonempty_iff_not_irrelevant_le [IsAlgClosed k] {Q : Ideal S} [Q.IsPrime]
    (hQ : IsHomogeneousIdeal Q) :
    (projZeroSet (Q : Set S)).Nonempty ↔ ¬(HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Q := by
  rw [Set.nonempty_iff_ne_empty, ne_eq, projZeroSet_eq_empty_iff hQ,
    (Ideal.IsPrime.isRadical ‹_›).radical]
  constructor
  · intro h hirr
    apply h
    rw [irrelevantIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hirr (X_mem_irrelevant_projectiveSpace i)
  · intro h hirr
    apply h
    intro a ha
    have ha0 : homogeneousComponent 0 a = 0 := by
      rw [← decomposition.decompose'_apply]
      exact ha
    have hc : eval 0 a = 0 := by
      have := congr(MvPolynomial.coeff 0 $ha0)
      rw [coeff_homogeneousComponent] at this
      simpa [MvPolynomial.eval_zero, constantCoeff_eq] using this
    have := sub_C_eval_zero_mem_irrelevantIdeal a
    rw [hc, map_zero, sub_zero] at this
    exact hirr this

/-- The zero set of the homogeneous prime of a point of `ℙⁿ_k` is a projective variety whose
homogeneous ideal is that prime. -/
theorem isProjVariety_projZeroSet_asHomogeneousIdeal [IsAlgClosed k] (q : Proj 𝒜) :
    IsProjVariety (projZeroSet (q.asHomogeneousIdeal.toIdeal : Set S)) ∧
      homogeneousVanishingIdeal (projZeroSet (q.asHomogeneousIdeal.toIdeal : Set S)) =
        q.asHomogeneousIdeal.toIdeal := by
  have := q.isPrime
  have hhom : IsHomogeneousIdeal q.asHomogeneousIdeal.toIdeal := q.asHomogeneousIdeal.isHomogeneous
  have hne : (projZeroSet (q.asHomogeneousIdeal.toIdeal : Set S)).Nonempty :=
    (projZeroSet_nonempty_iff_not_irrelevant_le hhom).mpr q.not_irrelevant_le
  have hJ : homogeneousVanishingIdeal (projZeroSet (q.asHomogeneousIdeal.toIdeal : Set S)) =
      q.asHomogeneousIdeal.toIdeal := by
    rw [homogeneousVanishingIdeal_projZeroSet hhom hne, (Ideal.IsPrime.isRadical q.isPrime).radical]
  have halg := isProjAlgebraicSet_projZeroSet_of_isHomogeneous _ hhom
  refine ⟨⟨(isIrreducible_iff_isPrime_homogeneousVanishingIdeal halg).mpr (by rw [hJ]; exact q.isPrime),
    isClosed_iff_isProjAlgebraicSet.mpr halg⟩, hJ⟩

/-- A closed immersion into `ℙⁿ_k` is injective on homogeneous primes. -/
theorem closedImmersion_eq_of_asHomogeneousIdeal_eq {X : Scheme.{u}} (ι : X ⟶ Proj 𝒜)
    [IsClosedImmersion ι] {x y : X}
    (h : (ι.base x).asHomogeneousIdeal.toIdeal = (ι.base y).asHomogeneousIdeal.toIdeal) :
    x = y :=
  ι.isClosedEmbedding.injective (ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective h))

/-- The classical projective variety `Z(𝔭) ⊆ ℙⁿ` underlying an integral closed subscheme, where
`𝔭` is the homogeneous prime of the image of the generic point. -/
def closedImmersionProjZeroSet {X : Scheme.{u}} [IsIntegral X] (ι : X ⟶ Proj 𝒜) :
    Set (ProjectiveSpace k (Fin (n + 1))) :=
  projZeroSet ((ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal : Set S)

/-- The classical hypersurface `Z(f) ⊆ ℙⁿ` cut out by the equation of a prime divisor. -/
def primeDivisorProjZeroSet (V : (Proj 𝒜).PrimeDivisor) : Set (ProjectiveSpace k (Fin (n + 1))) :=
  projZeroSet ({projectivePrimeDivisorEquation V} : Set S)

/-- The hypersurface `Z(f)` is a projective algebraic set. -/
theorem isProjAlgebraicSet_primeDivisorProjZeroSet (V : (Proj 𝒜).PrimeDivisor) :
    IsProjAlgebraicSet (primeDivisorProjZeroSet V) := by
  refine ⟨{projectivePrimeDivisorEquation V}, ?_, rfl⟩
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst g
  exact ⟨_, projectivePrimeDivisorEquation_isHomogeneous V⟩

/-- The hypersurface `Z(f)` is the zero set of the homogeneous prime of `V`. -/
theorem primeDivisorProjZeroSet_eq (V : (Proj 𝒜).PrimeDivisor) :
    primeDivisorProjZeroSet V = projZeroSet (V.1.asHomogeneousIdeal.toIdeal : Set S) := by
  rw [primeDivisorProjZeroSet, span_projectivePrimeDivisorEquation, projZeroSet_span]

/-- The ideal of the scheme-theoretic intersection `Z(𝔭) ∩ Z(f)` is `𝔭 + (f)`. -/
theorem projectiveIntersectionIdeal_closedImmersion [IsAlgClosed k] {X : Scheme.{u}}
    [IsIntegral X] (ι : X ⟶ Proj 𝒜) (V : (Proj 𝒜).PrimeDivisor) :
    projectiveIntersectionIdeal (closedImmersionProjZeroSet ι) (primeDivisorProjZeroSet V) =
      (ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal ⊔
        Ideal.span {projectivePrimeDivisorEquation V} := by
  rw [projectiveIntersectionIdeal, closedImmersionProjZeroSet, primeDivisorProjZeroSet_eq,
    (isProjVariety_projZeroSet_asHomogeneousIdeal _).2,
    (isProjVariety_projZeroSet_asHomogeneousIdeal _).2, span_projectivePrimeDivisorEquation]

/-- The prime divisor of `X` with `f ∈ 𝔓ₓ`, viewed as a relevant minimal prime of `𝔭 + (f)`. -/
def closedImmersionMinimalPrime [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
    (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (V : (Proj 𝒜).PrimeDivisor)
    (hfX : projectivePrimeDivisorEquation V ∉ (ι.base (genericPoint X)).asHomogeneousIdeal)
    (P : {P : X.PrimeDivisor //
      projectivePrimeDivisorEquation V ∈ (ι.base P.1).asHomogeneousIdeal}) :
    projectiveIntersectionMinimalPrimes (closedImmersionProjZeroSet ι)
      (primeDivisorProjZeroSet V) :=
  ⟨⟨(ι.base P.1.1).asHomogeneousIdeal.toIdeal, (ι.base P.1.1).isPrime⟩,
    (ι.base P.1.1).asHomogeneousIdeal.isHomogeneous,
    by
      rw [projectiveIntersectionIdeal_closedImmersion]
      exact (coheight_eq_one_and_mem_iff_mem_minimalPrimes ι
        (projectivePrimeDivisorEquation_isHomogeneous V) hfX P.1.1).mp ⟨P.1.2, P.2⟩,
    (isProjVariety_projZeroSet_asHomogeneousIdeal _).1.1.nonempty⟩

/-- Prime divisors of `X` on `V` are exactly the relevant minimal primes of `𝔭 + (f)`. -/
theorem closedImmersionMinimalPrime_bijective [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
    (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (V : (Proj 𝒜).PrimeDivisor)
    (hfX : projectivePrimeDivisorEquation V ∉ (ι.base (genericPoint X)).asHomogeneousIdeal) :
    Function.Bijective (closedImmersionMinimalPrime ι V hfX) := by
  constructor
  · intro P P' h
    have h' := congrArg (fun Q ↦ (Q.1.1 : Ideal S)) h
    exact Subtype.ext (Subtype.ext (closedImmersion_eq_of_asHomogeneousIdeal_eq ι h'))
  · rintro ⟨Q, hQh, hQmin, hQne⟩
    have := Q.2
    rw [projectiveIntersectionIdeal_closedImmersion] at hQmin
    obtain ⟨x, hx⟩ := exists_closedImmersion_eq_of_mem_minimalPrimes ι
      (projectivePrimeDivisorEquation_isHomogeneous V) hQmin
      ((projZeroSet_nonempty_iff_not_irrelevant_le hQh).mp hQne)
    rw [← hx] at hQmin
    obtain ⟨hx1, hfx⟩ := (coheight_eq_one_and_mem_iff_mem_minimalPrimes ι
      (projectivePrimeDivisorEquation_isHomogeneous V) hfX x).mpr hQmin
    exact ⟨⟨⟨x, hx1⟩, hfx⟩, Subtype.ext (PrimeSpectrum.ext hx)⟩

/-- **Components of `Z(𝔭) ∩ Z(f)` and prime divisors of `X` on `V`.** The prime divisors `Y` of
`X` lying on `V` correspond to the irreducible components of the classical intersection
`Z(𝔭) ∩ Z(f)`, a prime divisor going to the zero set of its homogeneous prime. -/
def closedImmersionComponentEquiv [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
    (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (V : (Proj 𝒜).PrimeDivisor)
    (hfX : projectivePrimeDivisorEquation V ∉ (ι.base (genericPoint X)).asHomogeneousIdeal) :
    {P : X.PrimeDivisor // projectivePrimeDivisorEquation V ∈ (ι.base P.1).asHomogeneousIdeal} ≃
      irreducibleComponents ↥(closedImmersionProjZeroSet ι ∩ primeDivisorProjZeroSet V) :=
  (Equiv.ofBijective _ (closedImmersionMinimalPrime_bijective ι V hfX)).trans
    (projectiveIntersectionComponentPrimeEquivMinimalPrimes
      (isProjVariety_projZeroSet_asHomogeneousIdeal _).1
      (isProjAlgebraicSet_primeDivisorProjZeroSet V)).symm

/-- The homogeneous prime of the component attached to a prime divisor `Y` of `X` is the prime of
the image of the generic point of `Y`. -/
theorem projectiveIntersectionComponentPrime_closedImmersionComponentEquiv [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι]
    (V : (Proj 𝒜).PrimeDivisor)
    (hfX : projectivePrimeDivisorEquation V ∉ (ι.base (genericPoint X)).asHomogeneousIdeal)
    (P : {P : X.PrimeDivisor //
      projectivePrimeDivisorEquation V ∈ (ι.base P.1).asHomogeneousIdeal}) :
    (projectiveIntersectionComponentPrime (isProjVariety_projZeroSet_asHomogeneousIdeal _).1
      (isProjAlgebraicSet_primeDivisorProjZeroSet V)
      (closedImmersionComponentEquiv ι V hfX P)).1 =
        (ι.base P.1.1).asHomogeneousIdeal.toIdeal := by
  have h1 : projectiveIntersectionComponentPrimeEquivMinimalPrimes
      (isProjVariety_projZeroSet_asHomogeneousIdeal _).1
      (isProjAlgebraicSet_primeDivisorProjZeroSet V) (closedImmersionComponentEquiv ι V hfX P) =
        closedImmersionMinimalPrime ι V hfX P :=
    Equiv.apply_symm_apply _ _
  have h2 := projectiveIntersectionComponentPrimeEquivMinimalPrimes_apply
    (isProjVariety_projZeroSet_asHomogeneousIdeal _).1
    (isProjAlgebraicSet_primeDivisorProjZeroSet V) (closedImmersionComponentEquiv ι V hfX P)
  rw [h1] at h2
  exact (congrArg PrimeSpectrum.asIdeal h2).symm

/-- If the prime divisor `V` does not contain `X`, its equation is not in the prime `𝔭` of the
generic point of `X`. -/
theorem projectivePrimeDivisorEquation_notMem_of_not_subset {X : Scheme.{u}} [IsIntegral X]
    (ι : X ⟶ Proj 𝒜) (V : (Proj 𝒜).PrimeDivisor)
    (hXV : ¬Set.range ι ⊆ closure ({V.1} : Set (Proj 𝒜))) :
    projectivePrimeDivisorEquation V ∉ (ι.base (genericPoint X)).asHomogeneousIdeal := by
  intro h
  apply hXV
  rintro _ ⟨z, rfl⟩
  rw [mem_closure_projectivePrimeDivisor_iff]
  exact (projectiveSpace_specializes_iff_le _ _).mp ((genericPoint_specializes z).map ι.continuous) h

/-- **Hartshorne II, Exercise 6.2(c), local part.** Along a prime divisor `Y` of `X` contained in
`V`, the coefficient of `V · X` is the intersection multiplicity `i(Z(𝔭), Z(f); Z)` of
Theorem I.7.7 at the corresponding component `Z` of `Z(𝔭) ∩ Z(f)`. -/
theorem projectiveIntersectionDivisor_apply_eq_projectiveIntersectionMultiplicity
    [IsAlgClosed k] {X : Scheme.{u}} (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι]
    (hX : X.SatisfiesConditionStar) (V : (Proj 𝒜).PrimeDivisor)
    (hXV : ¬Set.range ι ⊆ closure ({V.1} : Set (Proj 𝒜)))
    (P : {P : X.PrimeDivisor //
      projectivePrimeDivisorEquation V ∈ (ι.base P.1).asHomogeneousIdeal}) :
    let _ : IsIntegral X := hX.isIntegral
    (projectiveIntersectionDivisor ι hX V).1 P.1.1 =
      projectiveIntersectionMultiplicity (isProjVariety_projZeroSet_asHomogeneousIdeal _).1
        (isProjAlgebraicSet_primeDivisorProjZeroSet V)
        (closedImmersionComponentEquiv ι V
          (projectivePrimeDivisorEquation_notMem_of_not_subset ι V hXV) P) := by
  intro _
  obtain ⟨m, hc, hl⟩ := projectiveIntersectionDivisor_apply_eq_length ι hX V hXV P.1.1 P.1.2
  have hp : projectiveIntersectionComponentPrime (isProjVariety_projZeroSet_asHomogeneousIdeal _).1
      (isProjAlgebraicSet_primeDivisorProjZeroSet V)
      (closedImmersionComponentEquiv ι V
        (projectivePrimeDivisorEquation_notMem_of_not_subset ι V hXV) P) =
        ⟨(ι.base P.1.1).asHomogeneousIdeal.toIdeal, (ι.base P.1.1).isPrime⟩ :=
    PrimeSpectrum.ext (projectiveIntersectionComponentPrime_closedImmersionComponentEquiv ι V _ P)
  rw [hc]
  unfold projectiveIntersectionMultiplicity
  rw [hp, show projZeroSet ((ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal : Set S) =
    closedImmersionProjZeroSet ι from rfl, projectiveIntersectionIdeal_closedImmersion]
  change (m : ℤ) = ((Module.length _ _).toNat : ℤ)
  rw [hl, ENat.toNat_natCast]

/-- **Hartshorne II, Exercise 6.2(c), with `dim X ≥ 1`.** Let `k` be algebraically closed, let
`ι : X ⟶ ℙⁿ_k` be a closed immersion of a scheme satisfying `(*)` with more than one point (that
is, `dim X ≥ 1`), and let `V` be a prime divisor of `ℙⁿ_k` not containing `X`. Then
`deg (V · X) = deg V · deg X`, where `deg X` is the degree of the closure of the image of the
generic point. -/
theorem weilDivisorProjectiveDegree_projectiveIntersectionDivisor [IsAlgClosed k]
    {X : Scheme.{u}} (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (hX : X.SatisfiesConditionStar)
    (hdim : Nontrivial X) (V : (Proj 𝒜).PrimeDivisor)
    (hXV : ¬Set.range ι ⊆ closure ({V.1} : Set (Proj 𝒜))) :
    let _ : IsIntegral X := hX.isIntegral
    weilDivisorProjectiveDegree ι (projectiveIntersectionDivisor ι hX V) =
      projectiveSpectrumPointDegree V.1 * projectiveSpectrumPointDegree (ι.base (genericPoint X)) := by
  intro _
  classical
  set f := projectivePrimeDivisorEquation V
  set d := projectivePrimeDivisorEquationDegree V
  have hf : f.IsHomogeneous d := projectivePrimeDivisorEquation_isHomogeneous V
  set 𝔭 := (ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal
  have hfX := projectivePrimeDivisorEquation_notMem_of_not_subset ι V hXV
  set Y := closedImmersionProjZeroSet ι
  set H := primeDivisorProjZeroSet V
  have hYv : IsProjVariety Y ∧ homogeneousVanishingIdeal Y = 𝔭 :=
    isProjVariety_projZeroSet_asHomogeneousIdeal (ι.base (genericPoint X))
  have hH : IsProjAlgebraicSet H := isProjAlgebraicSet_primeDivisorProjZeroSet V
  set e := closedImmersionComponentEquiv ι V hfX
  let _ : Fintype (irreducibleComponents ↥(Y ∩ H)) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.fintype
  let _ : Fintype {P : X.PrimeDivisor // f ∈ (ι.base P.1).asHomogeneousIdeal} :=
    Fintype.ofEquiv _ e.symm
  -- the dimension of `Z(𝔭)` is a positive integer
  obtain ⟨r, hr⟩ := exists_projDim_eq_nat_of_isProjVariety hYv.1
  have hr0 : 0 < r := by
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    obtain ⟨P₀, hP₀⟩ := hYv.1.eq_singleton_of_projDim_eq_zero (by exact_mod_cast hr)
    obtain ⟨x, hx⟩ : ∃ x : X, x ≠ genericPoint X := by
      obtain ⟨a, b, hab⟩ := hdim
      by_cases ha : a = genericPoint X
      · exact ⟨b, fun hb ↦ hab (ha.trans hb.symm)⟩
      · exact ⟨a, ha⟩
    have hxv := isProjVariety_projZeroSet_asHomogeneousIdeal (ι.base x)
    have hsub : projZeroSet ((ι.base x).asHomogeneousIdeal.toIdeal : Set S) ⊆ Y :=
      projZeroSet_anti_mono ((closedImmersion_specializes_iff ι _ _).mp
        (genericPoint_specializes x))
    have heq : projZeroSet ((ι.base x).asHomogeneousIdeal.toIdeal : Set S) = Y := by
      rw [hP₀] at hsub ⊢
      exact (Set.Nonempty.subset_singleton_iff hxv.1.1.nonempty).mp hsub
    apply hx
    apply closedImmersion_eq_of_asHomogeneousIdeal_eq ι
    rw [← hxv.2, heq, hYv.2]
  have hproper : ¬Y ⊆ projZeroSet ({f} : Set S) := by
    intro h
    apply hfX
    have : f ∈ homogeneousVanishingIdeal Y :=
      Ideal.subset_span ⟨⟨d, hf⟩, fun P hP ↦ h hP f (Set.mem_singleton f)⟩
    rw [hYv.2] at this
    exact this
  have hbez : ∑ Z ∈ projectiveIntersectionComponents Y H,
      (projectiveIntersectionMultiplicity hYv.1 hH Z : ℚ) *
        projectiveDegree (projectiveComponentCarrier Z.1) =
      projectiveDegree Y * projectiveDegree H :=
    projective_hypersurface_bezout (projectivePrimeDivisorEquationDegree_pos V) hr0 Y
      hYv.1 hr f hf (projectivePrimeDivisorEquation_prime V).irreducible hproper
  rw [Finset.eq_univ_of_forall (mem_projectiveIntersectionComponents Y H)] at hbez
  -- rewrite the degree of `V · X` as a sum over the components
  have hzero : ∀ P : X.PrimeDivisor, f ∉ (ι.base P.1).asHomogeneousIdeal →
      (projectiveIntersectionDivisor ι hX V).1 P.1 * primeDivisorProjectiveDegree ι P = 0 := by
    intro P hP
    rw [projectiveIntersectionDivisor_apply_eq_zero_of_notMem ι hX V P.1
      (fun h ↦ hP ((mem_closure_projectivePrimeDivisor_iff V _).mp h)), zero_mul]
  have hsum : weilDivisorProjectiveDegree ι (projectiveIntersectionDivisor ι hX V) =
      ∑ Z : irreducibleComponents ↥(Y ∩ H),
        (projectiveIntersectionDivisor ι hX V).1 (e.symm Z).1.1 *
          primeDivisorProjectiveDegree ι (e.symm Z).1 := by
    rw [weilDivisorProjectiveDegree_apply]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.map
      (Function.Embedding.subtype fun P : X.PrimeDivisor ↦
        f ∈ (ι.base P.1).asHomogeneousIdeal)), Finset.sum_map]
    swap
    · intro P hP
      rw [Finset.coe_map, Finset.coe_univ, Set.image_univ, Function.Embedding.coe_subtype,
        Subtype.range_coe_subtype]
      by_contra hn
      exact hP (hzero P hn)
    exact Fintype.sum_equiv e _ _ fun P ↦ by rw [Equiv.symm_apply_apply]; rfl
  -- compare with Bézout term by term, in `ℚ`
  have hR : ((projectiveSpectrumPointDegree V.1 *
      projectiveSpectrumPointDegree (ι.base (genericPoint X)) : ℤ) : ℚ) =
      projectiveDegree Y * projectiveDegree H := by
    have h1 : (projectiveSpectrumPointDegree V.1 : ℚ) = projectiveDegree H :=
      (projectiveSpectrumPointDegree_cast V.1).trans
        (congrArg projectiveDegree (primeDivisorProjZeroSet_eq V).symm)
    have h2 : (projectiveSpectrumPointDegree (ι.base (genericPoint X)) : ℚ) = projectiveDegree Y :=
      projectiveSpectrumPointDegree_cast _
    rw [Int.cast_mul]
    exact (congrArg₂ (· * ·) h1 h2).trans (mul_comm _ _)
  apply Int.cast_injective (α := ℚ)
  rw [hR, ← hbez, hsum, Int.cast_sum]
  refine Finset.sum_congr rfl fun Z _ ↦ ?_
  have hmult := projectiveIntersectionDivisor_apply_eq_projectiveIntersectionMultiplicity ι hX V
    hXV (e.symm Z)
  have hprime := projectiveIntersectionComponentPrime_closedImmersionComponentEquiv ι V hfX
    (e.symm Z)
  dsimp only at hmult
  rw [Equiv.apply_symm_apply] at hmult hprime
  have hdeg : (projectiveSpectrumPointDegree (ι.base (e.symm Z).1.1) : ℚ) =
      projectiveDegree (projectiveComponentCarrier Z.1) :=
    (projectiveSpectrumPointDegree_cast _).trans
      ((congrArg (fun I : Ideal S ↦ projectiveDegree (projZeroSet (I : Set S))) hprime.symm).trans
        (congrArg projectiveDegree (projectiveIntersectionComponentPrime_projZeroSet _ _ Z)))
  rw [Int.cast_mul, hmult, Int.cast_natCast, primeDivisorProjectiveDegree]
  exact congrArg₂ (· * ·) rfl hdeg

end Hartshorne
