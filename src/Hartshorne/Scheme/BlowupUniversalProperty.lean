/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BlowupExceptionalIdeal
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Hartshorne.Scheme.LocallyFreeRinged
import Hartshorne.Scheme.AffineGlobalSectionsExact

/-!
# The universal property of a blowing-up

Hartshorne, *Algebraic Geometry*, II, Proposition 7.14 (pp. 164–165) and Exercise 7.1 (p. 169);
see also Stacks Project, tag 0806.

## Exercise 7.1

Let `(X, 𝒪_X)` be a ringed space and `φ : L ⟶ M` a surjective morphism (an epimorphism) of
invertible `𝒪_X`-modules. Then `φ` is an isomorphism. Near a point choose generators `l` of `L`
and `m` of `M` over a common open `W`, and write `φ(l) = c m`. Since `φ` is surjective, `m` lifts
locally, say `m = φ(a l) = a c m` near the point, so `a c = 1` there and `c` is a unit nearby; on
that neighbourhood `φ` is, in the coordinates `l` and `m`, multiplication by the unit `c`, hence
bijective on sections. A morphism bijective on sections near every point is an isomorphism.
Hartshorne states the exercise for locally ringed spaces; the argument needs only a ringed space.

* `Hartshorne.Ringed.isIso_of_epi_of_isInvertible`: the ringed-space statement.
* `Hartshorne.isIso_of_epi_of_isInvertible`: the case of a scheme.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

set_option hygiene false in
/-- Sections of the structure sheaf over an open. -/
local notation3 "𝒪(" U ")" => R.obj.obj (Opposite.op U)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

private lemma toSheaf_preservesColimit' {K : Type} [SmallCategory K] (D : K ⥤ 𝓜) :
    PreservesColimit D (SheafOfModules.toSheaf (ringCatSheafOf R) : 𝓜 ⥤ _) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)
  let D₀ : K ⥤ PresheafOfModules.{u} (ringCatSheafOf R).obj := D ⋙ SheafOfModules.forget _
  let D' : K ⥤ 𝓜 := D₀ ⋙ PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)
  let e : D ≅ D' := Functor.isoWhiskerLeft D (asIso adj.counit).symm
  have hc₀ := colimit.isColimit D₀
  have : PreservesColimitsOfSize.{0, 0}
      (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)) :=
    adj.leftAdjoint_preservesColimits
  have h2 : PreservesColimit D₀
      (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj) ⋙
        SheafOfModules.toSheaf (ringCatSheafOf R)) :=
    preservesColimit_of_natIso D₀
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 (ringCatSheafOf R).obj)).symm
  have : PreservesColimit D' (SheafOfModules.toSheaf (ringCatSheafOf R) : 𝓜 ⥤ _) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)) hc₀)
      (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj) ⋙
        SheafOfModules.toSheaf (ringCatSheafOf R)) hc₀)
  exact preservesColimit_of_iso_diagram _ e.symm

/-- An epimorphism of `𝒪_X`-modules is locally surjective on sections. -/
private lemma exists_local_lift {F G : 𝓜} (g : F ⟶ G) [Epi g] {U : Opens X}
    (t : Γ(G, U)) {x : X} (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∃ s : Γ(F, V), sectionsMap g V s = G.val.presheaf.map (homOfLE hVU).op t := by
  have : Epi ((SheafOfModules.toSheaf (ringCatSheafOf R)).map g) :=
    @preserves_epi_of_preservesColimit _ _ _ _
      (SheafOfModules.toSheaf (ringCatSheafOf R) : 𝓜 ⥤ _) _ _ g (toSheaf_preservesColimit' _) ‹_›
  have h := (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((SheafOfModules.toSheaf (ringCatSheafOf R)).map g)).mpr this
  obtain ⟨V, hVU, ⟨s, hs⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp h U t x hx
  exact ⟨V, hVU, hxV, s, hs⟩

/-- Restriction of a section of a module sheaf to a smaller open. -/
private abbrev res (A : 𝓜) {U V : Opens X} (h : V ≤ U) (s : Γ(A, U)) : Γ(A, V) :=
  A.val.presheaf.map (homOfLE h).op s

private lemma res_res (A : 𝓜) {U V W : Opens X} (h : V ≤ U) (h' : W ≤ V) (s : Γ(A, U)) :
    res A h' (res A h s) = res A (h'.trans h) s := by
  rw [res, res, res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma res_refl (A : 𝓜) {U : Opens X} (s : Γ(A, U)) : res A (le_refl U) s = s := by
  rw [res, show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma res_smul (A : 𝓜) {U V : Opens X} (h : V ≤ U) (r : 𝒪(U)) (s : Γ(A, U)) :
    res A h (r • s) = R.obj.map (homOfLE h).op r • res A h s :=
  A.val.map_smul (homOfLE h).op r s

private lemma sectionsMap_smul {A B : 𝓜} (φ : A ⟶ B) (U : Opens X) (r : 𝒪(U)) (x : Γ(A, U)) :
    sectionsMap φ U (r • x) = r • sectionsMap φ U x :=
  (φ.val.app (op U)).hom.map_smul r x

private lemma sectionsMap_res {A B : 𝓜} (φ : A ⟶ B) {U V : Opens X} (h : V ≤ U) (x : Γ(A, U)) :
    sectionsMap φ V (res A h x) = res B h (sectionsMap φ U x) := by
  have := ConcreteCategory.congr_hom ((modulesMapPresheaf φ).naturality (homOfLE h).op) x
  simp only [ConcreteCategory.comp_apply] at this
  show (modulesMapPresheaf φ).app (op V) (res A h x) =
    res B h ((modulesMapPresheaf φ).app (op U) x)
  exact this

/-- `s` generates `A` freely over `U`: on every smaller open `V`, `r ↦ r s|_V` is bijective. -/
private def IsGenerator (A : 𝓜) (U : Opens X) (s : Γ(A, U)) : Prop :=
  ∀ (V : Opens X) (h : V ≤ U), Function.Bijective (fun r : 𝒪(V) => r • res A h s)

private lemma IsGenerator.restrict {A : 𝓜} {U : Opens X} {s : Γ(A, U)} (hs : IsGenerator A U s)
    {W : Opens X} (hW : W ≤ U) : IsGenerator A W (res A hW s) := by
  intro V h
  have := hs V (h.trans hW)
  simpa only [res_res] using this

/-- An invertible module has local generators. -/
private lemma exists_isGenerator {A : 𝓜} (hA : IsInvertible A) (x : X) :
    ∃ (U : Opens X) (s : Γ(A, U)), x ∈ U ∧ IsGenerator A U s := by
  classical
  obtain ⟨U, hxU, ⟨α⟩⟩ := hA x
  let e : ULift.{u} (Fin 1) → Γ(A, U) := fun i =>
    (show Γ(A, U) from α.inv.val.app (op (Over.mk (𝟙 U))) (freeVec U i))
  have hF : IsLocalFrame A U e := isLocalFrame_of_over_iso α
  refine ⟨U, e default, hxU, fun V h => ?_⟩
  have key : (fun r : 𝒪(V) => r • res A h (e default)) =
      localFrameMap A e h ∘ (Equiv.funUnique (ULift.{u} (Fin 1)) 𝒪(V)).symm := by
    funext r
    rw [Function.comp_apply, localFrameMap_apply, Fintype.sum_unique]
    rfl
  rw [key]
  exact (hF V h).comp (Equiv.bijective _)

/-- **Hartshorne II, Exercise 7.1.** On a ringed space, a surjective morphism (an epimorphism)
of invertible `𝒪_X`-modules is an isomorphism. Hartshorne states this for locally ringed
spaces. -/
theorem isIso_of_epi_of_isInvertible {L M : 𝓜} (hL : IsInvertible L) (hM : IsInvertible M)
    (φ : L ⟶ M) [Epi φ] : IsIso φ := by
  refine modules_isIso_of_locally_bijective φ fun x => ?_
  obtain ⟨U, l, hxU, hl⟩ := exists_isGenerator hL x
  obtain ⟨U', m, hxU', hm⟩ := exists_isGenerator hM x
  let W := U ⊓ U'
  have hl' := hl.restrict (inf_le_left : W ≤ U)
  have hm' := hm.restrict (inf_le_right : W ≤ U')
  set l' := res L (inf_le_left : W ≤ U) l
  set m' := res M (inf_le_right : W ≤ U') m
  -- `φ(l') = c m'`
  obtain ⟨c, hc⟩ := (hm' W le_rfl).2 (sectionsMap φ W l')
  simp only [res_refl] at hc
  -- `m'` lifts near `x`
  obtain ⟨V, hVW, hxV, s, hs⟩ := exists_local_lift φ m' (show x ∈ W from ⟨hxU, hxU'⟩)
  obtain ⟨a, rfl⟩ := (hl' V hVW).2 s
  have hφ : ∀ {V' : Opens X} (h : V' ≤ W) (r : 𝒪(V')),
      sectionsMap φ V' (r • res L h l') = (r * R.obj.map (homOfLE h).op c) • res M h m' := by
    intro V' h r
    rw [sectionsMap_smul, sectionsMap_res, ← hc, res_smul, mul_smul]
  have hunit : IsUnit (R.obj.map (homOfLE hVW).op c) := by
    have h1 := hφ hVW a
    simp only at hs
    rw [hs] at h1
    have h2 : (1 : 𝒪(V)) • res M hVW m' = (a * R.obj.map (homOfLE hVW).op c) • res M hVW m' := by
      rw [one_smul]; exact h1
    exact IsUnit.of_mul_eq_one_right _ ((hm' V hVW).1 h2).symm
  refine ⟨V, hxV, fun V' hV' => ?_⟩
  have hcomp : (sectionsMap φ V' ∘ fun r : 𝒪(V') => r • res L (hV'.trans hVW) l') =
      (fun r : 𝒪(V') => r • res M (hV'.trans hVW) m') ∘
        (fun r => r * R.obj.map (homOfLE (hV'.trans hVW)).op c) := by
    funext r
    exact hφ _ r
  have hu' : IsUnit (R.obj.map (homOfLE (hV'.trans hVW)).op c) := by
    have := hunit.map (R.obj.map (homOfLE hV').op).hom
    rwa [← CommRingCat.comp_apply, ← Functor.map_comp] at this
  have hmul : Function.Bijective (fun r : 𝒪(V') => r * R.obj.map (homOfLE (hV'.trans hVW)).op c) :=
    (hu'.unit.mulRight).bijective
  rw [← Function.Bijective.of_comp_iff _ (hl' V' (hV'.trans hVW)), hcomp]
  exact (hm' V' (hV'.trans hVW)).comp hmul

end Ringed

/-- **Hartshorne II, Exercise 7.1**, for a scheme: a surjective morphism (an epimorphism) of
invertible `𝒪_X`-modules is an isomorphism. -/
theorem isIso_of_epi_of_isInvertible {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules}
    (hL : L.IsInvertible) (hM : M.IsInvertible) (φ : L ⟶ M) [Epi φ] : IsIso φ :=
  @Ringed.isIso_of_epi_of_isInvertible _ X.sheaf L M
    ((AlgebraicGeometry.Scheme.Modules.isInvertible_iff_ringed L).1 hL)
    ((AlgebraicGeometry.Scheme.Modules.isInvertible_iff_ringed M).1 hM) φ ‹Epi φ›


section InvertibleIdeal

open AlgebraicGeometry

attribute [local instance] isQuasicoherent_closedImmersionIdealSheaf

/-- An ideal sheaf whose sheaf of ideals is invertible is locally generated by one
non-zero-divisor. -/
theorem isLocallyPrincipalNonZeroDivisor_of_isInvertible {Z : Scheme.{u}} (K : Z.IdealSheafData)
    (hK : (closedImmersionIdealSheaf K.subschemeι).IsInvertible) :
    K.IsLocallyPrincipalNonZeroDivisor := by
  intro z
  obtain ⟨U, s, hzU, hs⟩ := Ringed.exists_isGenerator (R := Z.sheaf)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 hK) z
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWU⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hzU U.2
  let ι := closedImmersionIdealSheafι K.subschemeι
  let s' : Γ(closedImmersionIdealSheaf K.subschemeι, W) := Ringed.res _ hWU s
  have hbij : Function.Bijective (fun r : Γ(Z, W) => r • s') := hs W hWU
  refine ⟨⟨W, hW⟩, hzW, ι.app W s', ?_, ?_⟩
  · refine mem_nonZeroDivisors_iff_right.2 fun r hr => ?_
    have h1 : ι.app W (r • s') = 0 := (Scheme.Modules.Hom.app_smul ι r s').trans hr
    have h0 : r • s' = (0 : Γ(Z, W)) • s' := by
      rw [zero_smul]
      exact modules_app_injective ι W (h1.trans (map_zero _).symm)
    exact hbij.1 h0
  · rw [← homRangeIdeal_closedImmersionIdealSheafι K ⟨W, hW⟩]
    ext t
    refine ⟨fun ⟨a, ha⟩ => ?_, fun ht => ?_⟩
    · obtain ⟨r, rfl⟩ := hbij.2 a
      exact Ideal.mem_span_singleton'.2 ⟨r, (Scheme.Modules.Hom.app_smul ι r s').symm.trans ha⟩
    · obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ht
      exact ⟨r • s', Scheme.Modules.Hom.app_smul ι r s'⟩

end InvertibleIdeal

/-! ### Ring maps out of a chart of the Rees algebra -/

section ReesChartAlgebra

open _root_.Polynomial HomogeneousLocalization

variable {A : Type u} [CommRing A] (I : Ideal A) {a : A} (ha : a ∈ I)

private theorem coe_reesDegOne_pow (k : ℕ) :
    ((reesDegOne I ha ^ k : reesAlgebra I) : A[X]) = monomial k (a ^ k) := by
  rw [Subalgebra.coe_pow]
  change (monomial 1 a : A[X]) ^ k = _
  rw [monomial_pow, one_mul]

/-- **Ring maps out of a chart of the Rees algebra.** Two ring maps `A[It]_(a t) → R` which agree
on `A` and send `a` to a non-zero-divisor agree: an element `y / (a t)ⁿ` with `y = b tⁿ` satisfies
`aⁿ · (y / (a t)ⁿ) = b`. -/
theorem reesAway_ringHom_ext {R : Type*} [CommRing R]
    {ρ₁ ρ₂ : Away (reesGrading I) (reesDegOne I ha) →+* R}
    (h : ρ₁.comp (reesAwayMap I ha) = ρ₂.comp (reesAwayMap I ha))
    (hnzd : ρ₁ (reesAwayMap I ha a) ∈ nonZeroDivisors R) : ρ₁ = ρ₂ := by
  ext z
  obtain ⟨⟨n, ⟨x, hx⟩, ⟨s, hs⟩, hsm⟩, hz⟩ := mk_surjective z
  obtain ⟨k, hk⟩ := hsm
  simp only at hk
  subst hk
  have hθ : ∀ r, ρ₂ (reesAwayMap I ha r) = ρ₁ (reesAwayMap I ha r) := fun r =>
    (RingHom.congr_fun h r).symm
  by_cases hnk : n = k
  · subst hnk
    have key : reesAwayMap I ha a ^ n * z = reesAwayMap I ha ((x : A[X]).coeff n) := by
      rw [← hz]
      apply val_injective
      rw [val_mul, val_pow, val_mk, val_reesAwayMap, val_reesAwayMap, Localization.mk_pow,
        Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, Subtype.ext ?_⟩
      have hx' := mem_reesGrading_iff.1 hx
      simp only [OneMemClass.coe_one, one_mul, one_pow, Subalgebra.coe_mul,
        Subalgebra.coe_pow]
      set b := (x : A[X]).coeff n
      change (C a) ^ n * (x : A[X]) = (monomial 1 a) ^ n * C b
      rw [hx', ← C_pow, C_mul_monomial, monomial_pow, one_mul, monomial_mul_C, mul_comm]
    have hpow : ρ₁ (reesAwayMap I ha a) ^ n ∈ nonZeroDivisors R := pow_mem hnzd n
    have e1 : ρ₁ (reesAwayMap I ha a) ^ n * ρ₁ z = ρ₁ (reesAwayMap I ha ((x : A[X]).coeff n)) := by
      rw [← map_pow, ← map_mul, key]
    have e2 : ρ₁ (reesAwayMap I ha a) ^ n * ρ₂ z = ρ₁ (reesAwayMap I ha ((x : A[X]).coeff n)) := by
      rw [← hθ, ← map_pow, ← map_mul, key, hθ]
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_left.1 hpow) _ (by rw [mul_sub, e1, e2, sub_self]))
  · have hak : a ^ k = 0 := by
      have := hs k (Ne.symm hnk)
      rwa [coe_reesDegOne_pow, coeff_monomial_same] at this
    have h0 : ρ₁ (reesAwayMap I ha a) ^ k = 0 := by
      rw [← map_pow, ← map_pow, hak, map_zero, map_zero]
    have h1 : (1 : R) = 0 := by
      have := pow_mem hnzd k
      rw [h0] at this
      exact (mem_nonZeroDivisors_iff_right.1 this) 1 (mul_zero 1)
    exact (subsingleton_of_zero_eq_one h1.symm).elim _ _

/-- On the chart `D₊(b t)`, `a = b · (a t)/(b t)`. -/
theorem reesAwayMap_eq_mul_isLocalizationElem {b : A} (hb : b ∈ I) :
    reesAwayMap I hb a =
      reesAwayMap I hb b * Away.isLocalizationElem (reesDegOne_mem I hb) (reesDegOne_mem I ha) := by
  apply val_injective
  rw [val_mul, val_reesAwayMap, val_reesAwayMap, Away.val_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_one, Subalgebra.coe_mul]
  change (monomial 1 b : A[X]) * C a = C b * monomial 1 a
  rw [monomial_mul_C, C_mul_monomial, mul_comm]

end ReesChartAlgebra

/-- If `x` and a non-zero-divisor `γ` generate the same principal ideal, `x` is a
non-zero-divisor. -/
private theorem mem_nonZeroDivisors_of_span_eq {R : Type*} [CommRing R] {x γ : R}
    (hγ : γ ∈ nonZeroDivisors R) (h : Ideal.span {x} = Ideal.span {γ}) :
    x ∈ nonZeroDivisors R := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self x)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self γ)
  have hvu : v * u = 1 := by
    have : (v * u - 1) * γ = 0 := by rw [sub_mul, mul_assoc, hu, hv, one_mul, sub_self]
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hγ) _ this)
  rw [← hu]
  exact mul_mem (IsUnit.of_mul_eq_one_right v hvu).mem_nonZeroDivisors hγ

end Hartshorne
