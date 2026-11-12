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

end Hartshorne
