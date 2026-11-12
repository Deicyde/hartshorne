/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.NormalizationPushforwardDivisor
import Hartshorne.Intersection.ProjectiveSubvarietyOrder
import Hartshorne.Intersection.ProjectiveLinearSubspaceCycle
import Hartshorne.Intersection.RationalEquivalencePrincipal
import Hartshorne.Scheme.ProjectiveIntersectionDegreeFormula
import Hartshorne.Scheme.ProjectiveSpaceClassGroup

/-!
# The degree of cycles on projective space is invariant under rational equivalence

Let `k` be algebraically closed. The degree `deg (∑ nᵢ [Yᵢ]) = ∑ nᵢ deg Yᵢ` of cycles on `ℙⁿ_k`
vanishes on rational equivalence (`cycleProjectiveDegree_eq_zero_of_mem_rationalEquivalenceSubgroup`)
and hence descends to the Chow groups (`chowGroupProjectiveDegree`).

For an integral closed subvariety `i : V ⟶ ℙⁿ_k` with homogeneous prime `𝔭` and a nonzero rational
function `g = F / G` on `V` (forms of the same degree `d`, not in `𝔭`), the coefficient of
`ν_* div(g)` at `i(y)` is `ord_y(g) = μ_y(F) - μ_y(G)`, where `μ_y(F)` is the multiplicity of
`S / (𝔭 + F)` at the homogeneous prime of `y`. Bézout's theorem for `V` and each irreducible
factor of `F` gives `∑_y μ_y(F) deg Y = d deg V`, and the same for `G`.
-/

universe u

open AlgebraicGeometry CategoryTheory MvPolynomial Order

namespace Hartshorne

open ProjectiveSubvarietyOrder

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) k

local notation "S" => MvPolynomial (Fin (n + 1)) k

section Multiplicity

private theorem X_pow_mem (j : Fin (n + 1)) (e : ℕ) : (X j : S) ^ e ∈ 𝒜 e :=
  (mem_homogeneousSubmodule e _).mpr (isHomogeneous_pow_of_isHomogeneous_one (isHomogeneous_X k j) e)

/-- The multiplicity `μ_y(F)` of `S / (𝔭 + F)` at the homogeneous prime of `y`, `𝔭` the prime
of `V`. -/
private noncomputable def hypersurfaceMult {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i]
    (F : S) (y : V) : ℕ :=
  (gradedMultiplicity S (S ⧸ ((i (genericPoint V)).asHomogeneousIdeal.toIdeal ⊔ Ideal.span {F}))
    ⟨(i y).asHomogeneousIdeal.toIdeal, (i y).isPrime⟩).toNat

/-- The multiplicity of `A / I` at a prime not containing `I` is zero. -/
private theorem gradedMultiplicity_quotient_eq_zero {A : Type u} [CommRing A] {I : Ideal A}
    {𝔮 : PrimeSpectrum A} {s : A} (hsI : s ∈ I) (hs : s ∉ 𝔮.asIdeal) :
    gradedMultiplicity A (A ⧸ I) 𝔮 = 0 := by
  unfold gradedMultiplicity
  rw [(localizedQuotientEquivMap 𝔮.asIdeal I).length_eq, Module.length_eq_zero_iff,
    Ideal.Quotient.subsingleton_iff]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsI)
    (IsLocalization.map_units _ (⟨s, hs⟩ : 𝔮.asIdeal.primeCompl))

private theorem hypersurfaceMult_eq_zero {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i]
    {F : S} {y : V}
    (hF : F ∉ (i y).asHomogeneousIdeal) : hypersurfaceMult i F y = 0 := by
  rw [hypersurfaceMult, gradedMultiplicity_quotient_eq_zero
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self F)) hF]
  rfl

private theorem functionFieldQuot_ne_zero {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i]
    {d : ℕ} {F G : S} (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
    (hGv : G ∉ (i (genericPoint V)).asHomogeneousIdeal)
    (hFv : F ∉ (i (genericPoint V)).asHomogeneousIdeal) :
    functionFieldQuot i hF hG hGv ≠ 0 := fun h ↦
  hFv ((stalkMap_stalkQuot_eq_zero_iff i (genericPoint V) hF hG hGv).mp h)

/-- Multiplicities are additive: `μ_y(F₁ F₂) = μ_y(F₁) + μ_y(F₂)` at codimension-one points. -/
private theorem hypersurfaceMult_mul {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i] [IsLocallyNoetherian V]
    {y : V} (hy : coheight y = 1) {e₁ e₂ : ℕ} {F₁ F₂ : S}
    (hF₁ : F₁ ∈ 𝒜 e₁) (hF₂ : F₂ ∈ 𝒜 e₂) (hF₁v : F₁ ∉ (i (genericPoint V)).asHomogeneousIdeal)
    (hF₂v : F₂ ∉ (i (genericPoint V)).asHomogeneousIdeal) :
    hypersurfaceMult i (F₁ * F₂) y = hypersurfaceMult i F₁ y + hypersurfaceMult i F₂ y := by
  obtain ⟨j, hj⟩ := exists_X_notMem_projectiveSpace (i y)
  have hL : (X j : S) ∈ 𝒜 1 := (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X k j)
  have hF₁₂v : F₁ * F₂ ∉ (i (genericPoint V)).asHomogeneousIdeal := fun h ↦
    ((i (genericPoint V)).isPrime.mem_or_mem h).elim hF₁v hF₂v
  have h₁ := ord_functionFieldQuot_pow i hy hL hj hF₁ hF₁v (X_pow_mem (k := k) j e₁)
  have h₂ := ord_functionFieldQuot_pow i hy hL hj hF₂ hF₂v (X_pow_mem (k := k) j e₂)
  have h₁₂ := ord_functionFieldQuot_pow i hy hL hj (SetLike.mul_mem_graded hF₁ hF₂) hF₁₂v
    (X_pow_mem (k := k) j (e₁ + e₂))
  have hprod := functionFieldQuot_mul i hF₁ (X_pow_mem (k := k) j e₁)
    (pow_notMem_genericPoint i hj e₁) hF₂ (X_pow_mem (k := k) j e₂)
    (pow_notMem_genericPoint i hj e₂)
  rw [functionFieldQuot_eq_of_mul_eq i (SetLike.mul_mem_graded hF₁ hF₂)
    (SetLike.mul_mem_graded (X_pow_mem (k := k) j e₁) (X_pow_mem (k := k) j e₂)) _
    (SetLike.mul_mem_graded hF₁ hF₂) (X_pow_mem (k := k) j (e₁ + e₂))
    (pow_notMem_genericPoint i hj (e₁ + e₂)) (by ring)] at hprod
  rw [← hprod, Scheme.ord_mul (functionFieldQuot_ne_zero i _ _ _ hF₁v)
    (functionFieldQuot_ne_zero i _ _ _ hF₂v), h₁, h₂] at h₁₂
  rw [hypersurfaceMult, hypersurfaceMult, hypersurfaceMult]
  exact_mod_cast h₁₂.symm

/-- The order of `F / G` at a codimension-one point is `μ_y(F) - μ_y(G)`. -/
private theorem ord_functionFieldQuot_eq_sub {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i] [IsLocallyNoetherian V]
    {y : V} (hy : coheight y = 1) {d : ℕ} {F G : S}
    (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d) (hGv : G ∉ (i (genericPoint V)).asHomogeneousIdeal)
    (hFv : F ∉ (i (genericPoint V)).asHomogeneousIdeal) :
    V.ord (functionFieldQuot i hF hG hGv) y =
      (hypersurfaceMult i F y : ℤ) - hypersurfaceMult i G y := by
  obtain ⟨j, hj⟩ := exists_X_notMem_projectiveSpace (i y)
  have hL : (X j : S) ∈ 𝒜 1 := (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X k j)
  have hLd := X_pow_mem (k := k) j d
  have hq : functionFieldQuot i hF hG hGv =
      functionFieldQuot i hF hLd (pow_notMem_genericPoint i hj d) /
        functionFieldQuot i hG hLd (pow_notMem_genericPoint i hj d) := by
    rw [eq_div_iff (functionFieldQuot_ne_zero i _ _ _ hGv), functionFieldQuot_mul]
    exact functionFieldQuot_eq_of_mul_eq i _ _ _ _ _ _ (by ring)
  rw [hq, Scheme.ord_div (functionFieldQuot_ne_zero i _ _ _ hFv)
    (functionFieldQuot_ne_zero i _ _ _ hGv), ord_functionFieldQuot_pow i hy hL hj hF hFv hLd,
    ord_functionFieldQuot_pow i hy hL hj hG hGv hLd]
  rfl

/-- Every rational function on `V` is a quotient `F / G` of forms of the same degree. -/
private theorem exists_eq_functionFieldQuot {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i]
    (g : V.functionField) :
    ∃ (d : ℕ) (F G : S) (hF : F ∈ 𝒜 d) (hG : G ∈ 𝒜 d)
      (hGv : G ∉ (i (genericPoint V)).asHomogeneousIdeal), g = functionFieldQuot i hF hG hGv := by
  obtain ⟨s, rfl⟩ := i.stalkMap_surjective (genericPoint V) g
  obtain ⟨f, hf⟩ := HomogeneousLocalization.mk_surjective ((Proj.stalkIso 𝒜 _).hom s)
  refine ⟨f.deg, f.num, f.den, f.num.2, f.den.2, f.den_mem, ?_⟩
  change i.stalkMap _ s = i.stalkMap _ ((Proj.stalkIso 𝒜 _).inv (HomogeneousLocalization.mk f))
  rw [hf, Iso.hom_inv_id_apply]

/-- Finitely many codimension-one points of `V` lie on the hypersurface `F = 0`. -/
private theorem finite_coheight_eq_one_mem {V : Scheme.{u}} [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i]
    {e : ℕ} {F : S} (hF : F.IsHomogeneous e)
    (hFv : F ∉ (i (genericPoint V)).asHomogeneousIdeal) :
    {y : V | coheight y = 1 ∧ F ∈ (i y).asHomogeneousIdeal}.Finite := by
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing S
    ((i (genericPoint V)).asHomogeneousIdeal.toIdeal ⊔ Ideal.span {F})
  refine Set.Finite.of_finite_image (hfin.subset ?_) fun y _ y' _ h ↦
    closedImmersion_eq_of_asHomogeneousIdeal_eq i h
  rintro _ ⟨y, hy, rfl⟩
  exact (coheight_eq_one_and_mem_iff_mem_minimalPrimes i hF hFv y).mp hy

end Multiplicity

section Bezout

/-- An irreducible form of positive degree on `ℙⁿ`, `n ≥ 1`, cuts out a hypersurface whose
homogeneous ideal is generated by the form. -/
private theorem homogeneousVanishingIdeal_projZeroSet_irreducible [IsAlgClosed k] (hn : 0 < n)
    {e : ℕ} {F : S} (hF : F.IsHomogeneous e) (hirr : Irreducible F) :
    homogeneousVanishingIdeal (projZeroSet ({F} : Set S)) = Ideal.span {F} := by
  have hhom : IsHomogeneousIdeal (Ideal.span ({F} : Set S)) :=
    Ideal.homogeneous_span _ _ fun g hg ↦ by
      rw [Set.mem_singleton_iff.mp hg]
      exact isHomogeneousElem_iff.mpr ⟨e, hF⟩
  have hprime : (Ideal.span ({F} : Set S)).IsPrime :=
    (Ideal.span_singleton_prime hirr.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  have hne : (projZeroSet ((Ideal.span ({F} : Set S)) : Set S)).Nonempty := by
    rw [projZeroSet_nonempty_iff_not_irrelevant_le hhom]
    intro hle
    have hX : ∀ j : Fin (n + 1), F ∣ X j := fun j ↦
      Ideal.mem_span_singleton.mp (hle (X_mem_irrelevant_projectiveSpace j))
    have h0 := hirr.associated_of_dvd (irreducible_of_isHomogeneous_one
      (isHomogeneous_X k (0 : Fin (n + 1))) (X_ne_zero 0)) (hX 0)
    have h01 : (X (0 : Fin (n + 1)) : S) ∣ X ⟨1, by omega⟩ := h0.symm.dvd.trans (hX _)
    rw [X_dvd_X] at h01
    exact absurd (congrArg Fin.val h01) (by simp)
  rw [← projZeroSet_span, homogeneousVanishingIdeal_projZeroSet hhom hne, hprime.radical]

/-- **Bézout for an integral subvariety and an irreducible hypersurface.** Let `V` be an integral
closed subvariety of `ℙⁿ_k`, `n ≥ 1`, of positive dimension, and `F` an irreducible form of
degree `e ≥ 1` not vanishing on `V`. Then `∑_Y μ_Y(F) deg Y = e deg V`, the sum running over the
codimension-one points of `V`. -/
private theorem finsum_hypersurfaceMult_irreducible [IsAlgClosed k] (hn : 0 < n) {V : Scheme.{u}}
    [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i] (hdim : Nontrivial V) {e : ℕ} {F : S}
    (hF : F.IsHomogeneous e) (he : 0 < e) (hirr : Irreducible F)
    (hFv : F ∉ (i (genericPoint V)).asHomogeneousIdeal) :
    ∑ᶠ y : V, (if coheight y = 1 then (hypersurfaceMult i F y : ℤ) else 0) *
        projectiveSpectrumPointDegree (i y) =
      e * projectiveSpectrumPointDegree (i (genericPoint V)) := by
  classical
  set 𝔭 := (i (genericPoint V)).asHomogeneousIdeal.toIdeal
  set Y := closedImmersionProjZeroSet i
  set H := projZeroSet ({F} : Set S)
  have hYv : IsProjVariety Y ∧ homogeneousVanishingIdeal Y = 𝔭 :=
    isProjVariety_projZeroSet_asHomogeneousIdeal (i (genericPoint V))
  have hH : IsProjAlgebraicSet H := by
    refine ⟨{F}, ?_, rfl⟩
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact ⟨e, hF⟩
  have hIH := homogeneousVanishingIdeal_projZeroSet_irreducible hn hF hirr
  have hIdeal : projectiveIntersectionIdeal Y H = 𝔭 ⊔ Ideal.span {F} := by
    rw [projectiveIntersectionIdeal, hYv.2, hIH]
  -- codimension-one points of `V` on `Z(F)` and components of `Y ∩ H`
  let P : V → Prop := fun y ↦ coheight y = 1 ∧ F ∈ (i y).asHomogeneousIdeal
  let m : {y : V // P y} → projectiveIntersectionMinimalPrimes Y H := fun y ↦
    ⟨⟨(i y.1).asHomogeneousIdeal.toIdeal, (i y.1).isPrime⟩,
      (i y.1).asHomogeneousIdeal.isHomogeneous,
      by
        rw [hIdeal]
        exact (coheight_eq_one_and_mem_iff_mem_minimalPrimes i hF hFv y.1).mp y.2,
      (isProjVariety_projZeroSet_asHomogeneousIdeal _).1.1.nonempty⟩
  have hm : Function.Bijective m := by
    constructor
    · intro y y' h
      exact Subtype.ext (closedImmersion_eq_of_asHomogeneousIdeal_eq i
        (congrArg (fun Q ↦ (Q.1.1 : Ideal S)) h))
    · rintro ⟨Q, hQh, hQmin, hQne⟩
      have := Q.2
      rw [hIdeal] at hQmin
      obtain ⟨x, hx⟩ := exists_closedImmersion_eq_of_mem_minimalPrimes i hF hQmin
        ((projZeroSet_nonempty_iff_not_irrelevant_le hQh).mp hQne)
      rw [← hx] at hQmin
      exact ⟨⟨x, (coheight_eq_one_and_mem_iff_mem_minimalPrimes i hF hFv x).mpr hQmin⟩,
        Subtype.ext (PrimeSpectrum.ext hx)⟩
  let eqv : {y : V // P y} ≃ irreducibleComponents ↥(Y ∩ H) :=
    (Equiv.ofBijective m hm).trans
      (projectiveIntersectionComponentPrimeEquivMinimalPrimes hYv.1 hH).symm
  have hprime : ∀ y, (projectiveIntersectionComponentPrime hYv.1 hH (eqv y)).1 =
      (i y.1).asHomogeneousIdeal.toIdeal := by
    intro y
    have h1 : projectiveIntersectionComponentPrimeEquivMinimalPrimes hYv.1 hH (eqv y) = m y :=
      Equiv.apply_symm_apply _ _
    have h2 := projectiveIntersectionComponentPrimeEquivMinimalPrimes_apply hYv.1 hH (eqv y)
    rw [h1] at h2
    exact (congrArg PrimeSpectrum.asIdeal h2).symm
  let _ : Fintype (irreducibleComponents ↥(Y ∩ H)) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.fintype
  let _ : Fintype {y : V // P y} := Fintype.ofEquiv _ eqv.symm
  -- the dimension of `Y` is a positive integer
  obtain ⟨r, hr⟩ := exists_projDim_eq_nat_of_isProjVariety hYv.1
  have hr0 : 0 < r := by
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    obtain ⟨P₀, hP₀⟩ := hYv.1.eq_singleton_of_projDim_eq_zero (by exact_mod_cast hr)
    obtain ⟨x, hx⟩ : ∃ x : V, x ≠ genericPoint V := by
      obtain ⟨a, b, hab⟩ := hdim
      by_cases ha : a = genericPoint V
      · exact ⟨b, fun hb ↦ hab (ha.trans hb.symm)⟩
      · exact ⟨a, ha⟩
    have hxv := isProjVariety_projZeroSet_asHomogeneousIdeal (i.base x)
    have hsub : projZeroSet ((i.base x).asHomogeneousIdeal.toIdeal : Set S) ⊆ Y :=
      projZeroSet_anti_mono ((closedImmersion_specializes_iff i _ _).mp
        (genericPoint_specializes x))
    have heq : projZeroSet ((i.base x).asHomogeneousIdeal.toIdeal : Set S) = Y := by
      rw [hP₀] at hsub ⊢
      exact (Set.Nonempty.subset_singleton_iff hxv.1.1.nonempty).mp hsub
    apply hx
    apply closedImmersion_eq_of_asHomogeneousIdeal_eq i
    rw [← hxv.2, heq, hYv.2]
  have hproper : ¬Y ⊆ projZeroSet ({F} : Set S) := by
    intro h
    apply hFv
    have : F ∈ homogeneousVanishingIdeal Y :=
      Ideal.subset_span ⟨⟨e, hF⟩, fun P hP ↦ h hP F (Set.mem_singleton F)⟩
    rw [hYv.2] at this
    exact this
  have hbez := projective_hypersurface_bezout he hr0 Y hYv.1 hr F hF hirr hproper
  dsimp only at hbez
  rw [Finset.eq_univ_of_forall (mem_projectiveIntersectionComponents Y H)] at hbez
  -- the sum as a sum over the components
  have hsum : ∑ᶠ y : V, (if coheight y = 1 then (hypersurfaceMult i F y : ℤ) else 0) *
      projectiveSpectrumPointDegree (i y) =
      ∑ Z : irreducibleComponents ↥(Y ∩ H), (hypersurfaceMult i F (eqv.symm Z).1 : ℤ) *
        projectiveSpectrumPointDegree (i (eqv.symm Z).1) := by
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.map (Function.Embedding.subtype P)),
      Finset.sum_map]
    swap
    · intro y hy
      rw [Finset.coe_map, Finset.coe_univ, Set.image_univ, Function.Embedding.coe_subtype,
        Subtype.range_coe_subtype]
      by_contra hn'
      apply hy
      dsimp only
      by_cases h1 : coheight y = 1
      · rw [if_pos h1, hypersurfaceMult_eq_zero i (fun h ↦ hn' ⟨h1, h⟩), Nat.cast_zero, zero_mul]
      · rw [if_neg h1, zero_mul]
    refine Fintype.sum_equiv eqv _ _ fun y ↦ ?_
    rw [Equiv.symm_apply_apply, Function.Embedding.coe_subtype, if_pos y.2.1]
  -- compare with Bézout term by term, in `ℚ`
  have hR : ((e * projectiveSpectrumPointDegree (i (genericPoint V)) : ℤ) : ℚ) =
      projectiveDegree Y * projectiveDegree H := by
    have h1 : projectiveDegree H = e :=
      (hypersurface_hilbertPolynomial_and_degree hn he F hF hirr).2
    have h2 : (projectiveSpectrumPointDegree (i (genericPoint V)) : ℚ) = projectiveDegree Y :=
      projectiveSpectrumPointDegree_cast _
    rw [Int.cast_mul, h1, h2]
    push_cast
    ring
  apply Int.cast_injective (α := ℚ)
  rw [hR, ← hbez, hsum, Int.cast_sum]
  refine Finset.sum_congr rfl fun Z _ ↦ ?_
  have hp := hprime (eqv.symm Z)
  rw [Equiv.apply_symm_apply] at hp
  have hdeg : (projectiveSpectrumPointDegree (i (eqv.symm Z).1) : ℚ) =
      projectiveDegree (projectiveComponentCarrier Z.1) :=
    (projectiveSpectrumPointDegree_cast _).trans
      ((congrArg (fun I : Ideal S ↦ projectiveDegree (projZeroSet (I : Set S))) hp.symm).trans
        (congrArg projectiveDegree (projectiveIntersectionComponentPrime_projZeroSet _ _ Z)))
  have hmult : (hypersurfaceMult i F (eqv.symm Z).1 : ℤ) =
      projectiveIntersectionMultiplicity hYv.1 hH Z := by
    have hp' : projectiveIntersectionComponentPrime hYv.1 hH Z =
        ⟨(i (eqv.symm Z).1).asHomogeneousIdeal.toIdeal, (i (eqv.symm Z).1).isPrime⟩ :=
      PrimeSpectrum.ext hp
    unfold projectiveIntersectionMultiplicity hypersurfaceMult
    rw [hp', hIdeal]
  rw [Int.cast_mul, hmult, Int.cast_natCast, hdeg]

/-- The terms `[codim Y = 1] μ_Y(F) deg Y` have finite support. -/
private theorem finite_support_hypersurfaceMult {V : Scheme.{u}} [IsIntegral V]
    (i : V ⟶ Proj 𝒜) [IsClosedImmersion i] [IsAlgClosed k] {e : ℕ} {F : S}
    (hF : F.IsHomogeneous e) (hFv : F ∉ (i (genericPoint V)).asHomogeneousIdeal) :
    (Function.support fun y : V ↦ (if coheight y = 1 then (hypersurfaceMult i F y : ℤ) else 0) *
      projectiveSpectrumPointDegree (i y)).Finite := by
  refine (finite_coheight_eq_one_mem i hF hFv).subset fun y hy ↦ ?_
  have hy' := left_ne_zero_of_mul hy
  by_cases h1 : coheight y = 1
  · refine ⟨h1, by_contra fun h ↦ hy' ?_⟩
    rw [if_pos h1, hypersurfaceMult_eq_zero i h, Nat.cast_zero]
  · exact absurd (if_neg h1) hy'

/-- **Bézout for an integral subvariety and a hypersurface.** For a nonzero form `F` of degree `e`
not vanishing on `V` (positive-dimensional, in `ℙⁿ_k` with `n ≥ 1`),
`∑_Y μ_Y(F) deg Y = e deg V`: factor `F` into irreducible forms. -/
private theorem finsum_hypersurfaceMult [IsAlgClosed k] (hn : 0 < n) {V : Scheme.{u}}
    [IsIntegral V] (i : V ⟶ Proj 𝒜) [IsClosedImmersion i] [IsLocallyNoetherian V]
    (hdim : Nontrivial V) {e : ℕ} {F : S} (hF : F.IsHomogeneous e) (hF0 : F ≠ 0)
    (hFv : F ∉ (i (genericPoint V)).asHomogeneousIdeal) :
    ∑ᶠ y : V, (if coheight y = 1 then (hypersurfaceMult i F y : ℤ) else 0) *
        projectiveSpectrumPointDegree (i y) =
      e * projectiveSpectrumPointDegree (i (genericPoint V)) := by
  induction F using UniqueFactorizationMonoid.induction_on_prime generalizing e with
  | h₁ => exact absurd rfl hF0
  | h₂ x hx =>
    obtain ⟨c, hc, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := x)).mp hx
    have he : 0 = e := (isHomogeneous_C _ c).inj_right hF hF0
    subst he
    rw [Nat.cast_zero, zero_mul]
    refine finsum_eq_zero_of_forall_eq_zero fun y ↦ ?_
    have hy : C c ∉ (i y).asHomogeneousIdeal := fun h ↦
      (i y).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hc.map C))
    rw [hypersurfaceMult_eq_zero i hy, Nat.cast_zero, ite_self, zero_mul]
  | h₃ a p ha0 hp ih =>
    obtain ⟨j, hj⟩ := exists_isHomogeneous_of_prime_dvd hF hF0 hp (dvd_mul_right p a)
    have hpa : (a * p).IsHomogeneous e := by rwa [mul_comm]
    have ha : a.IsHomogeneous (e - j) := isHomogeneous_of_mul_isHomogeneous hj hp.ne_zero hpa
    have hje : j ≤ e := le_of_mul_isHomogeneous hj hpa (by rwa [mul_comm])
    have hpv : p ∉ (i (genericPoint V)).asHomogeneousIdeal := fun h ↦
      hFv (Ideal.mul_mem_right a _ h)
    have hav : a ∉ (i (genericPoint V)).asHomogeneousIdeal := fun h ↦
      hFv (Ideal.mul_mem_left _ p h)
    have hj0 : 0 < j := by
      rw [Nat.pos_iff_ne_zero]
      rintro rfl
      have hc := totalDegree_eq_zero_iff_eq_C.mp (hj.totalDegree hp.ne_zero)
      apply hp.not_unit
      rw [hc]
      refine (isUnit_iff_ne_zero.mpr fun h0 ↦ hp.ne_zero ?_).map C
      rw [hc, h0, map_zero]
    have hsplit : ∀ y : V, (if coheight y = 1 then (hypersurfaceMult i (p * a) y : ℤ) else 0) *
        projectiveSpectrumPointDegree (i y) =
        (if coheight y = 1 then (hypersurfaceMult i p y : ℤ) else 0) *
          projectiveSpectrumPointDegree (i y) +
        (if coheight y = 1 then (hypersurfaceMult i a y : ℤ) else 0) *
          projectiveSpectrumPointDegree (i y) := by
      intro y
      by_cases h1 : coheight y = 1
      · rw [if_pos h1, if_pos h1, if_pos h1,
          hypersurfaceMult_mul i h1 ((mem_homogeneousSubmodule j p).mpr hj)
            ((mem_homogeneousSubmodule (e - j) a).mpr ha) hpv hav]
        push_cast
        ring
      · rw [if_neg h1, if_neg h1, if_neg h1]
        ring
    rw [finsum_congr hsplit, finsum_add_distrib (finite_support_hypersurfaceMult i hj hpv)
      (finite_support_hypersurfaceMult i ha hav),
      finsum_hypersurfaceMult_irreducible hn i hdim hj hj0 hp.irreducible hpv, ih ha ha0 hav]
    push_cast [Nat.cast_sub hje]
    ring

end Bezout

end Hartshorne
