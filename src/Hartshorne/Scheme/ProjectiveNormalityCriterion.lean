/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSectionRingIntegralClosure
import Hartshorne.Scheme.ProjectiveIdealSaturation
import Hartshorne.Scheme.ProjTwistLocalization

/-!
# The projective-normality criterion

Hartshorne, *Algebraic Geometry*, II, Exercise 5.14(d) (p. 126).

Let `k` be algebraically closed, `S = k[x₀, …, xᵣ]`, and let `X ⊆ ℙʳ_k = Proj S` be a closed
subscheme with ideal sheaf `ℐ`. Its homogeneous coordinate ring is `S(X) = S/I` with
`I = Γ_*(ℐ) ∩ S` (`ProjectiveClosedSubscheme.gammaStarIdeal`), and `X = Proj (S/I)`
(Corollary 5.16). `X` is projectively normal (`IsProjectivelyNormal`) if `S(X)` is an integrally
closed domain. For `X` connected (the standing hypothesis of Exercise 5.14):

* `isProjectivelyNormal_iff`: `X` is projectively normal iff `X` is normal and every restriction
  map `Γ(ℙʳ_k, 𝒪(n)) → Γ(X, 𝒪_X(n))`, `n ≥ 0` (`restrictTwist`), is surjective.
* `isDomain_and_isIntegrallyClosed_iff`: the same for any saturated homogeneous ideal `I`.

The restriction map is the map on global sections of the morphism
`𝒪_{ℙʳ}(n) ⟶ ι_* 𝒪_X(n)` induced by the graded quotient map `S → S/I`
(`ProjTwistMap.twistHom`), where `ι : X = Proj (S/I) ⟶ ℙʳ_k`.

## Proof

Following the book, as a corollary of Exercise 5.14(a)
(`ProjectiveSectionRing.projectiveSectionRing_isIntegralClosure`): for connected normal `X`, `S/I`
is a domain and `S' = ⨁_{n ≥ 0} Γ(X, 𝒪_X(n))` is its integral closure, embedded in the fraction
field `K` of `S/I` by values at the generic point. Every global section of `𝒪_{ℙʳ}(n)` is a form
`b ∈ S_n` (Proposition 5.13), whose restriction to `X` has value `b̄ ∈ S/I`
(`sectionValue_restrictTwist_polySection`).

* `(⇐)`: if the restriction maps are surjective, every element of `S'` lies in `S/I ⊆ K`, so `S/I`
  equals its integral closure (`isIntegrallyClosed_of_surjective`).
* `(⇒)`: if `S/I` is an integrally closed domain, `X` is normal: the coordinate ring
  `(S/I)_(xᵢ)` of each chart `D₊(xᵢ)` is integrally closed
  (`isIntegrallyClosed_away_of_isIntegrallyClosed`) and the local rings are its localizations
  (`isNormal_of_isIntegrallyClosed`). Then `S' = S/I` by (a), so a section of `𝒪_X(n)` is some
  `s ∈ S/I`, which may be taken homogeneous of degree `n` (`algebraMap_decompose_eq`), and it is
  the restriction of a lift of `s` to `S_n` (`surjective_of_isIntegrallyClosed`).
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open GradedGlobalSections MonoidalCategory ProjGradedModuleSheaf

namespace ProjectiveNormality

open MvPolynomial ProjectiveSectionRing ProjTruncation

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {r : ℕ}

local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k

variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) k))

local notation "𝒬" => gradedQuotient 𝒮 I

/-- The graded quotient map `S → S/I` induces `Proj (S/I) ⟶ Proj S`. -/
theorem irrelevant_le_map_gradedQuotientMk : (HomogeneousIdeal.irrelevant 𝒬) ≤
    (HomogeneousIdeal.irrelevant 𝒮).map (gradedQuotientMk 𝒮 I) :=
  irrelevant_le_map_of_surjective (gradedQuotientMk_surjective 𝒮 I)

/-- **The restriction map** `Γ(ℙʳ_k, 𝒪(n)) → Γ(X, 𝒪_X(n))` for the closed subscheme
`X = Proj (S/I) ⊆ ℙʳ_k = Proj S`: global sections of `𝒪_{ℙʳ}(n) ⟶ ι_* 𝒪_X(n)`. -/
def restrictTwist (n : ℤ) :
    (projTwistingSheaf 𝒮 n).val.obj (op ⊤) →+ (projTwistingSheaf 𝒬 n).val.obj (op ⊤) :=
  ((ProjTwistMap.twistHom (gradedQuotientMk 𝒮 I) (irrelevant_le_map_gradedQuotientMk I) n).val.app
    (op ⊤)).hom.toAddMonoidHom

theorem globalValue_restrictTwist (n : ℤ) (u : (projTwistingSheaf 𝒮 n).val.obj (op ⊤))
    (y : Proj 𝒬) :
    globalValue 𝒬 (gradedTwist 𝒬 n) (restrictTwist I n u) y =
      ProjTwistMap.twistFiber (gradedQuotientMk 𝒮 I) n
        (ProjTwistMap.primeCompl_le_comap _ (irrelevant_le_map_gradedQuotientMk I) y)
        (globalValue 𝒮 (gradedTwist 𝒮 n) u
          (ProjectiveSpectrum.comap (gradedQuotientMk 𝒮 I) (irrelevant_le_map_gradedQuotientMk I) y)) :=
  rfl


open ProjectiveSpaceSectionRing in
/-- The global section `b / 1` of `𝒪_{ℙʳ}(n)` of a form `b ∈ S_n`. -/
abbrev polySection (n : ℕ) (b : MvPolynomial (Fin (r + 1)) k) :
    (projTwistingSheaf 𝒮 n).val.obj (op ⊤) :=
  ProjectiveSpaceSectionRing.unitorGlobal (n : ℤ) (sectionRingMap k r b n)

omit I in
open ProjectiveSpaceSectionRing in
/-- Every global section of `𝒪_{ℙʳ}(n)` is `b / 1` for a form `b ∈ S_n` (Proposition 5.13). -/
theorem exists_polySection_eq (n : ℕ) (u : (projTwistingSheaf 𝒮 n).val.obj (op ⊤)) :
    ∃ b ∈ 𝒮 n, polySection n b = u := by
  obtain ⟨z, rfl⟩ := (ProjectiveSpaceSectionRing.unitorGlobal_bijective (R := k) (r := r) n).2 u
  obtain ⟨b, hb, hbz⟩ := ProjectiveClosedSubscheme.exists_mem_sectionRingMap_eq n z
  exact ⟨b, hb, by rw [polySection, hbz]⟩

open ProjectiveSpaceSectionRing in
/-- The restriction of `b / 1` to `X = Proj (S/I)` is `b̄ / 1` at every point. -/
theorem val_globalValue_restrictTwist_polySection (n : ℕ) {b : MvPolynomial (Fin (r + 1)) k}
    (hb : b ∈ 𝒮 n) (y : Proj 𝒬) :
    (globalValue 𝒬 (gradedTwist 𝒬 n) (restrictTwist I n (polySection n b)) y).val =
      LocalizedModule.mk (Ideal.Quotient.mk I.toIdeal b) 1 := by
  rw [globalValue_restrictTwist, ProjTwistMap.val_twistFiber]
  have e : (globalValue 𝒮 (gradedTwist 𝒮 n) (polySection n b)
      (ProjectiveSpectrum.comap (gradedQuotientMk 𝒮 I) (irrelevant_le_map_gradedQuotientMk I) y)).val =
      twistValue n (sectionRingMap k r b n)
        (ProjectiveSpectrum.comap (gradedQuotientMk 𝒮 I) (irrelevant_le_map_gradedQuotientMk I) y) := rfl
  rw [e, twistValue_sectionRingMap, degreePart_of_mem hb, if_pos rfl, ProjTwistMap.locMap_mk]
  congr 1

/-! ### Homogeneous components in the fraction field -/

section HomFrac

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] [IsDomain A]

theorem isHomFrac_algebraMap {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    IsHomFrac (𝒜 := 𝒜) n (algebraMap A (FractionRing A) a) :=
  ⟨0, a, 1, by rwa [zero_add], SetLike.GradedOne.one_mem, one_ne_zero, by rw [map_one, div_one]⟩

/-- If `s ∈ A` is, in the fraction field, a homogeneous fraction of degree `n`, then it equals
its degree-`n` component. -/
theorem algebraMap_decompose_eq {n : ℕ} {s : A} {v : FractionRing A}
    (hv : IsHomFrac (𝒜 := 𝒜) n v) (hs : algebraMap A (FractionRing A) s = v) :
    algebraMap A (FractionRing A) (DirectSum.decompose 𝒜 s n : A) = v := by
  classical
  let F := insert n (DirectSum.decompose 𝒜 s).support
  let z : ℕ → FractionRing A := fun e =>
    algebraMap A (FractionRing A) (DirectSum.decompose 𝒜 s e : A) - if e = n then v else 0
  have hz : ∀ e ∈ F, IsHomFrac (𝒜 := 𝒜) e (z e) := by
    intro e _
    by_cases he : e = n
    · subst he
      simp only [z]
      exact (isHomFrac_algebraMap (DirectSum.decompose 𝒜 s e).2).sub hv
    · simp only [z, if_neg he, sub_zero]
      exact isHomFrac_algebraMap (DirectSum.decompose 𝒜 s e).2
  have hsum : ∑ e ∈ F, z e = 0 := by
    simp only [z, Finset.sum_sub_distrib, Finset.sum_ite_eq', ← map_sum]
    rw [← Finset.sum_subset (Finset.subset_insert n _), DirectSum.sum_support_decompose, hs,
      if_pos (Finset.mem_insert_self _ _), sub_self]
    intro e _ he
    rw [DFinsupp.notMem_support_iff.1 he, ZeroMemClass.coe_zero]
  have h0 := eq_zero_of_sum_isHomFrac_eq_zero F z hz hsum n (Finset.mem_insert_self n _)
  simp only [z] at h0
  exact sub_eq_zero.1 h0

private theorem isDomain_away' {f : A} (hf : f ≠ 0) : IsDomain (Away 𝒜 f) :=
  (awayToFraction_injective (𝒜 := 𝒜) hf).isDomain (awayToFraction hf)

/-- **The degree-zero localization of an integrally closed graded domain is integrally closed**:
for `f ∈ A₁` nonzero, `A_(f)` is integrally closed. An element of the fraction field of `A_(f)`
integral over `A_(f)` is integral over `A_f`, hence lies in `A_f`; being of degree zero it lies
in `A_(f)`. -/
theorem isIntegrallyClosed_away_of_isIntegrallyClosed [IsIntegrallyClosed A] {f : A} (f_deg : f ∈ 𝒜 1) (hf : f ≠ 0) :
    IsIntegrallyClosed (Away 𝒜 f) := by
  classical
  have := isDomain_away' (𝒜 := 𝒜) hf
  let K := FractionRing A
  let L := FractionRing (Away 𝒜 f)
  let ψ : Away 𝒜 f →+* K := awayToFraction hf
  have hψ : Function.Injective ψ := awayToFraction_injective hf
  let Φ : L →+* K := IsFractionRing.lift hψ
  have hΦ : ∀ c, Φ (algebraMap (Away 𝒜 f) L c) = ψ c := IsFractionRing.lift_algebraMap hψ
  let T := Localization.Away f
  have hM := powers_le_nonZeroDivisors hf
  let ι : T →ₐ[A] K := Localization.mapToFractionRing K (Submonoid.powers f) T hM
  let : Algebra T K := ι.toRingHom.toAlgebra
  have : IsScalarTower A T K := IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  have : IsFractionRing T K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) T K
  have : IsIntegrallyClosed T := isIntegrallyClosed_of_isLocalization T (Submonoid.powers f) hM
  rw [isIntegrallyClosed_iff L]
  intro z hz
  obtain ⟨p, hpm, hp⟩ := hz
  have hcomp : (algebraMap T K).comp (algebraMap (Away 𝒜 f) T) =
      Φ.comp (algebraMap (Away 𝒜 f) L) := by
    ext c
    exact (hΦ c).symm
  have hw : IsIntegral T (Φ z) := by
    refine ⟨p.map (algebraMap (Away 𝒜 f) T), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).1 inferInstance hw
  obtain ⟨⟨num, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) y
  obtain ⟨m, hm⟩ := s.2
  have hfm0 : algebraMap A K (f ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 (pow_ne_zero m hf)
  -- `f^m · Φ z = num` in `K`
  have hnum : algebraMap A K num = algebraMap A K (f ^ m) * Φ z := by
    have h1 := congrArg ι (IsLocalization.mk'_spec T num s)
    rw [map_mul, ι.commutes, ι.commutes] at h1
    change algebraMap T K _ * _ = _ at h1
    rw [hy, ← hm] at h1
    rw [← h1, mul_comm]
  -- `Φ z` is a homogeneous fraction of degree zero, so `f^m Φ z` has degree `m`
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Away 𝒜 f) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨ca, rfl⟩ := HomogeneousLocalization.mk_surjective a
  obtain ⟨cb, rfl⟩ := HomogeneousLocalization.mk_surjective b
  have hcb : (cb.num : A) ≠ 0 := by
    intro h0
    apply hb0
    apply hψ
    rw [map_zero]
    change awayToFraction hf _ = 0
    rw [awayToFraction_mk, h0, map_zero, zero_div]
  have hΦz : Φ (algebraMap (Away 𝒜 f) L (HomogeneousLocalization.mk ca) /
      algebraMap (Away 𝒜 f) L (HomogeneousLocalization.mk cb)) =
      algebraMap A K (ca.num * cb.den) / algebraMap A K (ca.den * cb.num) := by
    rw [map_div₀, hΦ, hΦ]
    change awayToFraction hf _ / awayToFraction hf _ = _
    rw [awayToFraction_mk, awayToFraction_mk]
    rw [map_mul, map_mul, div_div_div_eq]
  have hhom : IsHomFrac (𝒜 := 𝒜) m (algebraMap A K (f ^ m) * Φ (algebraMap (Away 𝒜 f) L
      (HomogeneousLocalization.mk ca) / algebraMap (Away 𝒜 f) L (HomogeneousLocalization.mk cb))) := by
    rw [hΦz]
    refine ⟨ca.deg + cb.deg, f ^ m * (ca.num * cb.den), ca.den * cb.num, ?_,
      SetLike.mul_mem_graded ca.den.2 cb.num.2, mul_ne_zero (den_ne_zero hf ca) hcb, ?_⟩
    · have := SetLike.mul_mem_graded (pow_mem_graded_one 𝒜 f_deg m)
        (SetLike.mul_mem_graded ca.num.2 cb.den.2)
      rwa [show m + (ca.deg + cb.deg) = ca.deg + cb.deg + m by omega] at this
    · rw [map_mul (algebraMap A K) (f ^ m), mul_div_assoc]
  have hdec := algebraMap_decompose_eq hhom hnum
  refine ⟨HomogeneousLocalization.mk ⟨m, DirectSum.decompose 𝒜 num m,
    ⟨f ^ m, pow_mem_graded_one 𝒜 f_deg m⟩, ⟨m, rfl⟩⟩, ?_⟩
  apply Φ.injective
  rw [hΦ]
  change awayToFraction hf _ = _
  rw [awayToFraction_mk]
  change algebraMap A K (DirectSum.decompose 𝒜 num m : A) / algebraMap A K (f ^ m) = _
  rw [hdec, mul_div_cancel_left₀ _ hfm0]

omit [IsDomain A] in
private theorem exists_unitorGlobal_eq (n : ℤ) (t : (projTwistingSheaf 𝒜 n).val.obj (op ⊤)) :
    ∃ t', ProjectiveSectionRing.unitorGlobal n t' = t :=
  (ProjectiveSectionRing.unitorGlobal_bijective n).2 t

end HomFrac

/-! ### The criterion -/

local notation "S" => MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal

/-- **If `S/I` is an integrally closed domain, then `X = Proj (S/I)` is normal**: the coordinate
ring `(S/I)_(xᵢ)` of each chart `D₊(xᵢ)` is integrally closed, and the local rings of `X` are its
localizations. -/
theorem isNormal_of_isIntegrallyClosed [IsDomain S] [IsIntegrallyClosed S] :
    Hartshorne.IsNormal (Proj 𝒬) := by
  have key : ∀ x : Proj 𝒬, IsDomain ((Proj 𝒬).presheaf.stalk x) ∧
      IsIntegrallyClosed ((Proj 𝒬).presheaf.stalk x) := by
    intro x
    obtain ⟨i, hi⟩ := exists_coord_notMem I x
    have hi0 : coord I i ≠ 0 := fun h => hi (h ▸ zero_mem _)
    have hU := Proj.isAffineOpen_basicOpen 𝒬 (coord I i) (coord_mem I i) one_pos
    have hx : x ∈ Proj.basicOpen 𝒬 (coord I i) := (Proj.mem_basicOpen 𝒬 _ _).2 hi
    have := isIntegrallyClosed_away_of_isIntegrallyClosed (coord_mem I i) hi0
    have := isDomain_away' (𝒜 := 𝒬) hi0
    let e := (Proj.basicOpenIsoAway 𝒬 (coord I i) (coord_mem I i) one_pos).commRingCatIsoToRingEquiv
    have : IsDomain Γ(Proj 𝒬, Proj.basicOpen 𝒬 (coord I i)) := e.symm.injective.isDomain e.symm
    have : IsIntegrallyClosed Γ(Proj 𝒬, Proj.basicOpen 𝒬 (coord I i)) :=
      IsIntegrallyClosed.of_equiv e
    let _ : Algebra Γ(Proj 𝒬, Proj.basicOpen 𝒬 (coord I i)) ((Proj 𝒬).presheaf.stalk x) :=
      ((Proj 𝒬).presheaf.germ _ x hx).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hx⟩
    have hle := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl_le_nonZeroDivisors
    exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors _ hle,
      isIntegrallyClosed_of_isLocalization _ _ hle⟩
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

theorem not_irrelevant_le_bot [Nonempty (Proj 𝒬)] :
    ¬HomogeneousIdeal.irrelevant 𝒬 ≤ ⊥ := by
  obtain ⟨x⟩ := ‹Nonempty (Proj 𝒬)›
  obtain ⟨i, hi⟩ := exists_coord_ne_zero I x
  exact not_irrelevant_le_bot_of_mem_one (coord_mem I i) hi

section Domain

variable [IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ I.toIdeal)]

/-- The restriction of `b / 1`, `b ∈ S_n`, has value `b̄ ∈ S/I` in the fraction field. -/
theorem sectionValue_restrictTwist_polySection (n : ℕ) {b : MvPolynomial (Fin (r + 1)) k}
    (hb : b ∈ 𝒮 n) (y : Proj 𝒬) :
    sectionValue (𝒜 := 𝒬) (n : ℤ) (restrictTwist I n (polySection n b)) y =
      algebraMap S (FractionRing S) (Ideal.Quotient.mk I.toIdeal b) := by
  unfold sectionValue
  rw [val_globalValue_restrictTwist_polySection I n hb y, toFraction_mk]
  simp

/-- Global sections of `𝒪_X(n)` with the same value in the fraction field are equal. -/
theorem eq_of_sectionValue_eq (h : ¬HomogeneousIdeal.irrelevant 𝒬 ≤ ⊥) {n : ℤ}
    {g g' : (projTwistingSheaf 𝒬 n).val.obj (op ⊤)}
    (hg : sectionValue (𝒜 := 𝒬) n g (genericPoint h) = sectionValue n g' (genericPoint h)) :
    g = g' := by
  apply globalValue_injective 𝒬 (gradedTwist 𝒬 n)
  funext x
  apply HomogeneousLocalizedModule.ext
  apply toFraction_injective x
  exact ((sectionValue_eq_genericPoint h n g x).trans hg).trans
    (sectionValue_eq_genericPoint h n g' x).symm

theorem exists_algebraMap_eq_sectionToFraction (h : ¬HomogeneousIdeal.irrelevant 𝒬 ≤ ⊥)
    (hsurj : ∀ n : ℕ, Function.Surjective (restrictTwist I n)) (n : ℕ)
    (t : twistGlobal (𝟙_ (Proj 𝒬).Modules) (n : ℤ)) :
    ∃ s : S, algebraMap S (FractionRing S) s = sectionToFraction 𝒬 n t := by
  obtain ⟨u, hu⟩ := hsurj n (ProjectiveSectionRing.unitorGlobal (𝒜 := 𝒬) (n : ℤ) t)
  obtain ⟨b, hb, rfl⟩ := exists_polySection_eq n u
  refine ⟨Ideal.Quotient.mk I.toIdeal b, ?_⟩
  rw [sectionToFraction_apply h _ t (genericPoint h), ← hu,
    sectionValue_restrictTwist_polySection I n hb]

/-- If every restriction map is surjective, every element of `S'` comes from `S/I`. -/
theorem sectionRingToFraction_mem_range (h : ¬HomogeneousIdeal.irrelevant 𝒬 ≤ ⊥)
    (hsurj : ∀ n : ℕ, Function.Surjective (restrictTwist I n))
    (y : DirectSum ℕ fun n => twistGlobal (𝟙_ (Proj 𝒬).Modules) (n : ℤ)) :
    sectionRingToFraction 𝒬 y ∈ (algebraMap S (FractionRing S)).range := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | of n t =>
    rw [sectionRingToFraction_of]
    exact exists_algebraMap_eq_sectionToFraction I h hsurj n t
  | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'

/-- **`(⇐)`**: if `S'` is the integral closure of `S/I` and every restriction map is
surjective, then `S/I` is integrally closed. -/
theorem isIntegrallyClosed_of_surjective [Nonempty (Proj 𝒬)]
    (hrange : Set.range (sectionRingToFraction 𝒬) =
      (integralClosure S (FractionRing S) : Set (FractionRing S)))
    (hsurj : ∀ n : ℕ, Function.Surjective (restrictTwist I n)) : IsIntegrallyClosed S := by
  have h := not_irrelevant_le_bot I
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro z hz
  have hz' : z ∈ Set.range (sectionRingToFraction 𝒬) := by
    rw [hrange]
    exact hz
  obtain ⟨y, rfl⟩ := hz'
  exact sectionRingToFraction_mem_range I h hsurj y

/-- **`(⇒)`**: if `S/I` is integrally closed and `S'` is its integral closure, every
restriction map is surjective. -/
theorem surjective_of_isIntegrallyClosed [IsIntegrallyClosed S] [Nonempty (Proj 𝒬)]
    (hrange : Set.range (sectionRingToFraction 𝒬) =
      (integralClosure S (FractionRing S) : Set (FractionRing S))) (n : ℕ) :
    Function.Surjective (restrictTwist I n) := by
  have h := not_irrelevant_le_bot I
  intro t
  have ht := exists_unitorGlobal_eq _ t
  obtain ⟨t', ht'⟩ := ht
  have hmem : sectionToFraction 𝒬 n t' ∈ integralClosure S (FractionRing S) := by
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨DirectSum.of _ n t', sectionRingToFraction_of 𝒬 n t'⟩
  have hs := IsIntegrallyClosed.isIntegral_iff.1 ((mem_integralClosure_iff _ _).1 hmem)
  obtain ⟨s, hs⟩ := hs
  have hdec := algebraMap_decompose_eq (isHomFrac_sectionToFraction h n t') hs
  have hb := mem_gradedQuotient_iff.1 (DirectSum.decompose 𝒬 s n).2
  obtain ⟨b, hb, hbs⟩ := hb
  refine ⟨polySection n b, (eq_of_sectionValue_eq I h ?_).trans ht'⟩
  rw [sectionValue_restrictTwist_polySection I n hb, hbs, hdec,
    sectionToFraction_apply h _ t' (genericPoint h)]

end Domain

/-- **Hartshorne II, Exercise 5.14(d), for a saturated homogeneous ideal.** Let `k` be
algebraically closed, `S = k[x₀, …, xᵣ]`, and let `I ⊆ S` be a saturated homogeneous ideal
(hypothesis `hsat`) such that the closed subscheme `X = Proj (S/I) ⊆ ℙʳ_k` is connected. Then the
homogeneous coordinate ring `S/I` is an integrally closed domain if and only if `X` is normal
and, for every `n ≥ 0`, the restriction map `Γ(ℙʳ_k, 𝒪(n)) → Γ(X, 𝒪_X(n))` is surjective. -/
theorem isDomain_and_isIntegrallyClosed_iff [IsAlgClosed k]
    (hsat : ∀ s : MvPolynomial (Fin (r + 1)) k, (∀ i, ∃ n : ℕ, X i ^ n * s ∈ I.toIdeal) →
      s ∈ I.toIdeal)
    [ConnectedSpace (Proj 𝒬)] :
    (IsDomain S ∧ IsIntegrallyClosed S) ↔
      Hartshorne.IsNormal (Proj 𝒬) ∧ ∀ n : ℕ, Function.Surjective (restrictTwist I n) := by
  constructor
  · rintro ⟨hd, hic⟩
    have hN : Hartshorne.IsNormal (Proj 𝒬) := isNormal_of_isIntegrallyClosed I
    have h := (projectiveSectionRing_isIntegralClosure I hsat).2
    exact ⟨hN, surjective_of_isIntegrallyClosed I h.2.2⟩
  · rintro ⟨hN, hsurj⟩
    obtain ⟨hd, h⟩ := projectiveSectionRing_isIntegralClosure I hsat
    exact ⟨hd, isIntegrallyClosed_of_surjective I h.2.2 hsurj⟩

omit I

/-- **Projectively normal closed subschemes** (Hartshorne II, Exercise 5.14; I, Exercise 3.18).
Let `ℐ` be the ideal sheaf of a closed subscheme `X ⊆ ℙʳ_k = Proj S`, `S = k[x₀, …, xᵣ]`. The
homogeneous coordinate ring of `X` is `S(X) = S/I` with `I = Γ_*(ℐ)` (Corollary 5.16), and `X` is
projectively normal (for the given embedding) if `S(X)` is an integrally closed domain. -/
def IsProjectivelyNormal (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮)) : Prop :=
  IsDomain (MvPolynomial (Fin (r + 1)) k ⧸ (ProjectiveClosedSubscheme.gammaStarIdeal k r ℐ).toIdeal) ∧
    IsIntegrallyClosed
      (MvPolynomial (Fin (r + 1)) k ⧸ (ProjectiveClosedSubscheme.gammaStarIdeal k r ℐ).toIdeal)

/-- **Hartshorne II, Exercise 5.14(d).** Let `k` be algebraically closed and let `X ⊆ ℙʳ_k` be a
connected closed subscheme with ideal sheaf `ℐ`, realized as `X = Proj (S/I)` for its
homogeneous ideal `I = Γ_*(ℐ)` (Corollary 5.16; `I` is saturated by Exercise 5.10). Then `X` is
projectively normal if and only if `X` is normal and, for every `n ≥ 0`, the restriction map
`Γ(ℙʳ_k, 𝒪(n)) → Γ(X, 𝒪_X(n))` is surjective. Connectedness is the standing hypothesis of
Hartshorne's Exercise 5.14. -/
theorem isProjectivelyNormal_iff [IsAlgClosed k] (ℐ : QuasicoherentIdealSubsheaf (Proj 𝒮))
    [ConnectedSpace (Proj (gradedQuotient 𝒮 (ProjectiveClosedSubscheme.gammaStarIdeal k r ℐ)))] :
    IsProjectivelyNormal ℐ ↔
      Hartshorne.IsNormal (Proj (gradedQuotient 𝒮 (ProjectiveClosedSubscheme.gammaStarIdeal k r ℐ))) ∧
        ∀ n : ℕ, Function.Surjective
          (restrictTwist (ProjectiveClosedSubscheme.gammaStarIdeal k r ℐ) n) := by
  refine isDomain_and_isIntegrallyClosed_iff _ fun s hs => ?_
  rw [← ProjectiveClosedSubscheme.saturation_gammaStarIdeal ℐ]
  exact ProjectiveClosedSubscheme.mem_saturation.2 hs

end ProjectiveNormality

end Hartshorne
