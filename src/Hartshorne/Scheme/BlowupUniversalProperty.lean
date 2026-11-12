/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BlowupExceptionalIdeal
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Hartshorne.Scheme.LocallyFreeRinged
import Hartshorne.Scheme.AffineGlobalSectionsExact
import Hartshorne.Scheme.ProjChartMorphism

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

section ReesChartLift

open _root_.Polynomial HomogeneousLocalization

variable {A : Type u} [CommRing A] (I : Ideal A) {a : A} (ha : a ∈ I)
  {R : Type u} [CommRing R] (θ : A →+* R)

/-- `p(t) ↦ θ(p)(1 / θ(a))`, from the Rees algebra `A[It]` to `R[1 / θ(a)]`. -/
private noncomputable def reesLiftLoc : reesAlgebra I →+* Localization.Away (θ a) :=
  (eval₂RingHom ((algebraMap R (Localization.Away (θ a))).comp θ)
    (IsLocalization.Away.invSelf (θ a))).comp (reesAlgebra I).val.toRingHom

private theorem reesLiftLoc_mem (hdiv : ∀ b ∈ I, θ b ∈ Ideal.span {θ a}) (p : reesAlgebra I) :
    reesLiftLoc I θ p ∈ (algebraMap R (Localization.Away (θ a))).range := by
  obtain ⟨p, hp⟩ := p
  have hcoeff : ∀ n, ∃ c : R, θ (p.coeff n) = c * θ a ^ n := by
    intro n
    have h1 : θ (p.coeff n) ∈ (I.map θ) ^ n := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I p).1 hp n)
    have h2 : I.map θ ≤ Ideal.span {θ a} := Ideal.map_le_iff_le_comap.2 hdiv
    have h3 := Ideal.pow_right_mono h2 n h1
    rw [Ideal.span_singleton_pow] at h3
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h3
    exact ⟨c, hc.symm⟩
  choose c hc using hcoeff
  change eval₂ _ _ p ∈ _
  rw [eval₂_eq_sum_range]
  refine Subring.sum_mem _ fun n _ => ⟨c n, ?_⟩
  rw [RingHom.comp_apply, hc, map_mul, map_pow, mul_assoc, ← mul_pow,
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- **Ring maps out of a chart of the Rees algebra, existence.** If `θ : A → R` sends `a ∈ I` to
a non-zero-divisor dividing `θ(I)`, then `θ` extends to `A[It]_(a t) → R`, `y/(a t)ⁿ ↦ c` where
`θ(y/tⁿ) = c θ(a)ⁿ`. -/
theorem exists_reesAway_ringHom (hnzd : θ a ∈ nonZeroDivisors R)
    (hdiv : ∀ b ∈ I, θ b ∈ Ideal.span {θ a}) :
    ∃ ψ : Away (reesGrading I) (reesDegOne I ha) →+* R, ψ.comp (reesAwayMap I ha) = θ := by
  set ι := algebraMap R (Localization.Away (θ a))
  have hinj : Function.Injective ι :=
    IsLocalization.injective (Localization.Away (θ a)) (Submonoid.powers_le.2 hnzd)
  let e := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  let F : reesAlgebra I →+* R :=
    e.symm.toRingHom.comp ((reesLiftLoc I θ).codRestrict _ (reesLiftLoc_mem I θ hdiv))
  have hF : ∀ p, ι (F p) = reesLiftLoc I θ p := fun p =>
    congrArg Subtype.val (e.apply_symm_apply ⟨_, reesLiftLoc_mem I θ hdiv p⟩)
  have hFr : ∀ r, F (algebraMap A (reesAlgebra I) r) = θ r := fun r => hinj (by
    rw [hF]
    change eval₂ _ _ (C r) = _
    rw [eval₂_C]
    rfl)
  have hF1 : IsUnit (F (reesDegOne I ha)) := by
    have : F (reesDegOne I ha) = 1 := hinj (by
      rw [hF, map_one]
      change eval₂ _ _ (monomial 1 a) = _
      rw [eval₂_monomial, pow_one, RingHom.comp_apply, IsLocalization.Away.mul_invSelf])
    rw [this]; exact isUnit_one
  refine ⟨awayLift F (reesDegOne I ha) hF1, RingHom.ext fun r => ?_⟩
  rw [RingHom.comp_apply, awayLift, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    val_reesAwayMap, Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift,
    IsLocalization.lift_eq, hFr]

end ReesChartLift

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

/-! ### Uniqueness of the factorization through the blowing-up -/

section Uniqueness

open AlgebraicGeometry

/-- Two morphisms mapping an open `V` into an affine open `C` agree on `V` when they induce the
same ring map `Γ(C) → Γ(V)`. -/
private theorem ι_comp_eq_of_appLE_eq {Y Z : Scheme.{u}} {g₁ g₂ : Z ⟶ Y} {C : Y.Opens}
    (hC : IsAffineOpen C) {V : Z.Opens} (h₁ : V ≤ g₁ ⁻¹ᵁ C) (h₂ : V ≤ g₂ ⁻¹ᵁ C)
    (h : g₁.appLE C V h₁ = g₂.appLE C V h₂) : V.ι ≫ g₁ = V.ι ≫ g₂ := by
  rw [← g₁.resLE_comp_ι h₁, ← g₂.resLE_comp_ι h₂]
  congr 1
  have : IsAffine C.toScheme := hC
  refine ext_of_isAffine ?_
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, h]

set_option backward.isDefEq.respectTransparency false in
private theorem appLE_specMap_fromSpec' {X : Scheme.{u}} {R : CommRingCat.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (φ : Γ(X, V) ⟶ R) (h : (⊤ : (Spec R).Opens) ≤ (Spec.map φ ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (Spec.map φ ≫ hV.fromSpec).appLE V ⊤ h = φ ≫ (Scheme.ΓSpecIso R).inv := by
  rw [← cancel_mono (Scheme.ΓSpecIso R).hom, Scheme.Hom.comp_appLE_assoc,
    IsAffineOpen.fromSpec_app_self, Category.assoc, Scheme.Hom.map_appLE_assoc,
    SpecMap_appLE_top_ΓSpecIso, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem appLE_congr_hom {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (hφψ : φ = ψ) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (e' : V ≤ ψ ⁻¹ᵁ U) : φ.appLE U V e = ψ.appLE U V e' := by
  subst hφψ; rfl

namespace QuasiCoherentGradedAlgebra

variable {X : Scheme.{u}} (S : QuasiCoherentGradedAlgebra X)

theorem chartι_image_le (U : X.AffineZariskiSite) {a : S.obj.obj (.op U)}
    (a_deg : a ∈ S.grading U 1) : S.chartι U a_deg ''ᵁ ⊤ ≤ S.relProjToBase ⁻¹ᵁ U.1 := by
  rintro _ ⟨w, -, rfl⟩
  change (S.chartι U a_deg ≫ S.relProjToBase) w ∈ U.1
  rw [chartι_relProjToBase, Scheme.Hom.comp_apply]
  exact U.2.range_fromSpec.le ⟨_, rfl⟩

/-- On the chart `D₊(a)`, the structure map `Γ(U, 𝒪_X) → S(U)_(a) ≅ Γ(D₊(a), 𝒪)` is the ring map
of the projection. -/
theorem chartMap_comp_chartSectionsIso_hom (U : X.AffineZariskiSite) {a : S.obj.obj (.op U)}
    (a_deg : a ∈ S.grading U 1) :
    S.chartMap U a ≫ (S.chartSectionsIso U a_deg).hom =
      S.relProjToBase.appLE U.1 (S.chartι U a_deg ''ᵁ ⊤) (S.chartι_image_le U a_deg) := by
  rw [← cancel_mono ((S.chartι U a_deg).appIso ⊤).hom, chartSectionsIso, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  have e' : (⊤ : (Spec (.of (HomogeneousLocalization.Away (S.grading U) a))).Opens) ≤
      (Spec.map (S.chartMap U a) ≫ U.2.fromSpec) ⁻¹ᵁ U.1 := fun x _ => by
    change (Spec.map (S.chartMap U a) ≫ U.2.fromSpec) x ∈ U.1
    rw [Scheme.Hom.comp_apply]
    exact U.2.range_fromSpec.le ⟨_, rfl⟩
  rw [appLE_congr_hom (S.chartι_relProjToBase U a_deg) _ _ _ e', appLE_specMap_fromSpec']

/-- For `g : Z ⟶ Proj_X S` over `f : Z ⟶ X` mapping `V` into the chart `D₊(a)`, the ring map
`S(U)_(a) → Γ(V, 𝒪_Z)` restricts on `Γ(U, 𝒪_X)` to the ring map of `f`. -/
theorem chartMap_comp_appLE {Z : Scheme.{u}} {f : Z ⟶ X} {g : Z ⟶ S.relProj}
    (hg : g ≫ S.relProjToBase = f) (U : X.AffineZariskiSite) {a : S.obj.obj (.op U)}
    (a_deg : a ∈ S.grading U 1) {V : Z.Opens} (hV : V ≤ g ⁻¹ᵁ (S.chartι U a_deg ''ᵁ ⊤))
    (hVf : V ≤ f ⁻¹ᵁ U.1) :
    S.chartMap U a ≫ (S.chartSectionsIso U a_deg).hom ≫ g.appLE _ V hV = f.appLE U.1 V hVf := by
  rw [← Category.assoc, chartMap_comp_chartSectionsIso_hom, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_hom hg _ _ _ _

end QuasiCoherentGradedAlgebra

namespace ReesAlgebraSheaf

variable {X : Scheme.{u}} (J : X.IdealSheafData)

/-- Over an affine open `U`, `Proj_X (⨁ Jᵈ)` is covered by the charts `D₊(a t)`, `a ∈ J(U)`. -/
theorem exists_mem_chartι_image (U : X.AffineZariskiSite) {p : (reesAlgebraSheaf J).relProj}
    (hp : p ∈ (reesAlgebraSheaf J).relProjToBase ⁻¹ᵁ U.1) :
    ∃ (a : Γ(X, U.1)) (ha : a ∈ idealOn J U),
      p ∈ (reesAlgebraSheaf J).chartι U (chartElt_mem J U ha) ''ᵁ ⊤ := by
  rw [QuasiCoherentGradedAlgebra.relProjToBase_preimage] at hp
  obtain ⟨y, rfl⟩ := hp
  obtain ⟨f, f_deg, hfy⟩ := ProjTwistingSheaf.exists_mem_one_notMem
    ((reesAlgebraSheaf J).adjoin_eq_top_of_generatedInDegreeOne (generatedInDegreeOne J) U) y
  obtain ⟨a, ha, hfa⟩ := (mem_grading_iff J U 1 f).1 f_deg
  rw [pow_one] at ha
  obtain rfl : f = chartElt J U ha := Subtype.ext hfa
  obtain ⟨z, hz⟩ := (reesAlgebraSheaf J).exists_chartι_eq U (chartElt_mem J U ha) y hfy
  exact ⟨a, ha, z, trivial, hz⟩

/-- Let `g : Z ⟶ Proj_X (⨁ Jᵈ)` lie over `f : Z ⟶ X` and map `V` into the chart `D₊(b t)`. If the
pull-back of `a` is a non-zero-divisor on `V` dividing the pull-back of `b`, then `g` maps `V`
into the chart `D₊(a t)`: on `D₊(b t)`, `a = b · (a t)/(b t)`, so `(a t)/(b t)` pulls back to a
unit. -/
theorem le_preimage_chartι_image {Z : Scheme.{u}} {f : Z ⟶ X}
    {g : Z ⟶ (reesAlgebraSheaf J).relProj} (hg : g ≫ (reesAlgebraSheaf J).relProjToBase = f)
    (U : X.AffineZariskiSite) {a b : Γ(X, U.1)} (ha : a ∈ idealOn J U) (hb : b ∈ idealOn J U)
    {V : Z.Opens} (hVb : V ≤ g ⁻¹ᵁ ((reesAlgebraSheaf J).chartι U (chartElt_mem J U hb) ''ᵁ ⊤))
    (hVf : V ≤ f ⁻¹ᵁ U.1) (hnzd : f.appLE U.1 V hVf a ∈ nonZeroDivisors Γ(Z, V))
    (hspan : f.appLE U.1 V hVf b ∈ Ideal.span {f.appLE U.1 V hVf a}) :
    V ≤ g ⁻¹ᵁ ((reesAlgebraSheaf J).chartι U (chartElt_mem J U ha) ''ᵁ ⊤) := by
  set e := HomogeneousLocalization.Away.isLocalizationElem (chartElt_mem J U hb)
    (chartElt_mem J U ha)
  set ρ := ((reesAlgebraSheaf J).chartSectionsIso U (chartElt_mem J U hb)).hom ≫ g.appLE _ V hVb
  have hθ := (reesAlgebraSheaf J).chartMap_comp_appLE hg U (chartElt_mem J U hb) hVb hVf
  have hθx : ∀ x, ρ ((reesAlgebraSheaf J).chartMap U (chartElt J U hb) x) = f.appLE U.1 V hVf x := fun x => by
    rw [← hθ]; rfl
  have key : f.appLE U.1 V hVf a = f.appLE U.1 V hVf b * ρ e := by
    rw [← hθx, ← hθx, chartMap_apply, chartMap_apply,
      reesAwayMap_eq_mul_isLocalizationElem _ ha hb]
    exact map_mul ρ.hom _ _
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hspan
  have hunit : IsUnit (ρ e) := by
    have : (w * ρ e - 1) * f.appLE U.1 V hVf a = 0 := by
      rw [sub_mul, one_mul, mul_right_comm, hw, ← key, sub_self]
    exact IsUnit.of_mul_eq_one_right w
      (sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hnzd) _ this))
  set s := ((reesAlgebraSheaf J).chartSectionsIso U (chartElt_mem J U hb)).hom e
  have h1 : V ≤ g ⁻¹ᵁ ((reesAlgebraSheaf J).relProj.basicOpen s) := by
    rw [Scheme.preimage_basicOpen]
    have : Z.basicOpen (g.appLE _ V hVb s) = V := Z.basicOpen_of_isUnit hunit
    rw [← this, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact inf_le_right
  refine h1.trans fun z hz => ?_
  change g z ∈ (reesAlgebraSheaf J).relProj.basicOpen s at hz
  change g z ∈ (reesAlgebraSheaf J).chartι U (chartElt_mem J U ha) ''ᵁ ⊤
  rw [show s = (((reesAlgebraSheaf J).chartι U (chartElt_mem J U hb)).appIso ⊤).inv
      ((Scheme.ΓSpecIso _).inv e) from rfl, ← Scheme.image_basicOpen,
    basicOpen_eq_of_affine] at hz
  obtain ⟨q, hq, hqz⟩ := hz
  have hq' : q ∈ Proj.awayι _ _ (chartElt_mem J U hb) one_pos ⁻¹ᵁ
      Proj.basicOpen _ (chartElt J U ha) := by
    rw [Proj.awayι_preimage_basicOpen]; exacts [hq, one_pos]
  rw [← Proj.opensRange_awayι _ _ (chartElt_mem J U ha) one_pos] at hq'
  obtain ⟨w', hw'⟩ := hq'
  refine ⟨w', trivial, ?_⟩
  rw [← hqz]
  change ((reesAlgebraSheaf J).projι U) ((Proj.awayι _ _ (chartElt_mem J U ha) one_pos) w') =
    ((reesAlgebraSheaf J).projι U) ((Proj.awayι _ _ (chartElt_mem J U hb) one_pos) q)
  rw [hw']

/-- **Uniqueness in Hartshorne II, Proposition 7.14**, for `π : Proj_X (⨁ Jᵈ) ⟶ X` and any ideal
sheaf `J`. If `f⁻¹J · 𝒪_Z` is locally generated by one non-zero-divisor, two morphisms
`g₁ g₂ : Z ⟶ Proj_X (⨁ Jᵈ)` over `f` are equal. Near a point, both map a neighbourhood `V` into
one chart `D₊(a t)`, `a ∈ J(U)`, on which `J · 𝒪 = (a)`; so `f^♯ a` generates `f⁻¹J · 𝒪_Z` on `V`
and is a non-zero-divisor there, and a ring map `S(U)_(a t) → Γ(V, 𝒪_Z)` restricting to `f^♯` on
`Γ(U, 𝒪_X)` is unique. -/
theorem hom_ext_of_isLocallyPrincipalNonZeroDivisor {Z : Scheme.{u}} {f : Z ⟶ X}
    (hf : (inverseImageIdeal f J).IsLocallyPrincipalNonZeroDivisor)
    {g₁ g₂ : Z ⟶ (reesAlgebraSheaf J).relProj}
    (h₁ : g₁ ≫ (reesAlgebraSheaf J).relProjToBase = f)
    (h₂ : g₂ ≫ (reesAlgebraSheaf J).relProjToBase = f) : g₁ = g₂ := by
  refine Scheme.hom_ext_of_forall g₁ g₂ fun z => ?_
  obtain ⟨U, hU, hzU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show f z ∈ (⊤ : X.Opens) from trivial)
  let U' : X.AffineZariskiSite := ⟨U, hU⟩
  have hπ : ∀ {g : Z ⟶ (reesAlgebraSheaf J).relProj}
      (_ : g ≫ (reesAlgebraSheaf J).relProjToBase = f),
      g z ∈ (reesAlgebraSheaf J).relProjToBase ⁻¹ᵁ U'.1 := fun {g} hg => by
    change (reesAlgebraSheaf J).relProjToBase (g z) ∈ U
    rw [← Scheme.Hom.comp_apply, hg]
    exact hzU
  obtain ⟨a, ha, hza⟩ := exists_mem_chartι_image J U' (hπ h₁)
  obtain ⟨b, hb, hzb⟩ := exists_mem_chartι_image J U' (hπ h₂)
  obtain ⟨V₀, hzV₀, γ, hγ, hV₀⟩ := hf z
  let O : Z.Opens :=
    g₁ ⁻¹ᵁ ((reesAlgebraSheaf J).chartι U' (chartElt_mem J U' ha) ''ᵁ ⊤) ⊓
      g₂ ⁻¹ᵁ ((reesAlgebraSheaf J).chartι U' (chartElt_mem J U' hb) ''ᵁ ⊤) ⊓ f ⁻¹ᵁ U ⊓ V₀
  have hzO : z ∈ O := ⟨⟨⟨hza, hzb⟩, hzU⟩, hzV₀⟩
  obtain ⟨r, hrO, hzr⟩ := V₀.2.exists_basicOpen_le ⟨z, hzO⟩ hzV₀
  have hV₀le : Z.basicOpen r ≤ V₀ := Z.basicOpen_le r
  have hV1 : Z.basicOpen r ≤
      g₁ ⁻¹ᵁ ((reesAlgebraSheaf J).chartι U' (chartElt_mem J U' ha) ''ᵁ ⊤) :=
    hrO.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hV2 : Z.basicOpen r ≤
      g₂ ⁻¹ᵁ ((reesAlgebraSheaf J).chartι U' (chartElt_mem J U' hb) ''ᵁ ⊤) :=
    hrO.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have hVf : Z.basicOpen r ≤ f ⁻¹ᵁ U'.1 := hrO.trans (inf_le_left.trans inf_le_right)
  have hVaff : IsAffineOpen (Z.basicOpen r) := V₀.2.basicOpen r
  have hKV : (inverseImageIdeal f J).ideal ⟨Z.basicOpen r, hVaff⟩ =
      Ideal.span {Z.presheaf.map (homOfLE hV₀le).op γ} := by
    rw [← (inverseImageIdeal f J).map_ideal (U := ⟨Z.basicOpen r, hVaff⟩) (V := V₀) hV₀le, hV₀,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hγV : Z.presheaf.map (homOfLE hV₀le).op γ ∈ nonZeroDivisors Γ(Z, Z.basicOpen r) := by
    have := V₀.2.isLocalization_basicOpen r
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r) Γ(Z, Z.basicOpen r) hγ
  have hJθ : (J.ideal ⟨U'.1, U'.2⟩).map (f.appLE U'.1 _ hVf).hom =
      (inverseImageIdeal f J).ideal ⟨Z.basicOpen r, hVaff⟩ :=
    (inverseImageIdeal_ideal f J ⟨U'.1, U'.2⟩ ⟨Z.basicOpen r, hVaff⟩ hVf).symm
  have hθ₁ := (reesAlgebraSheaf J).chartMap_comp_appLE h₁ U' (chartElt_mem J U' ha) hV1 hVf
  have hspanθ : (J.ideal ⟨U'.1, U'.2⟩).map (f.appLE U'.1 _ hVf).hom =
      Ideal.span {f.appLE U'.1 _ hVf a} := by
    rw [← hθ₁, CommRingCat.hom_comp, ← Ideal.map_map, map_chartMap, Ideal.map_span,
      Set.image_singleton]
    rfl
  have hnzd : f.appLE U'.1 _ hVf a ∈ nonZeroDivisors Γ(Z, Z.basicOpen r) :=
    mem_nonZeroDivisors_of_span_eq hγV (hspanθ.symm.trans (hJθ.trans hKV))
  have hbmem : f.appLE U'.1 _ hVf b ∈ Ideal.span {f.appLE U'.1 _ hVf a} :=
    hspanθ ▸ Ideal.mem_map_of_mem _ hb
  have hV2a := le_preimage_chartι_image J h₂ U' ha hb hV2 hVf hnzd hbmem
  have hθ₂ := (reesAlgebraSheaf J).chartMap_comp_appLE h₂ U' (chartElt_mem J U' ha) hV2a hVf
  have hρ : ((reesAlgebraSheaf J).chartSectionsIso U' (chartElt_mem J U' ha)).hom ≫
        g₁.appLE _ _ hV1 =
      ((reesAlgebraSheaf J).chartSectionsIso U' (chartElt_mem J U' ha)).hom ≫
        g₂.appLE _ _ hV2a := by
    ext1
    refine reesAway_ringHom_ext (idealOn J U') ha
      (RingHom.ext fun x => (congrArg (fun φ => φ.hom x) hθ₁).trans
        (congrArg (fun φ => φ.hom x) hθ₂).symm) ?_
    have := congrArg (fun φ => φ.hom a) hθ₁
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← this] at hnzd
    exact hnzd
  exact ⟨Z.basicOpen r, hzr, ι_comp_eq_of_appLE_eq
    ((isAffineOpen_top _).image_of_isOpenImmersion _) hV1 hV2a ((cancel_epi _).1 hρ)⟩

end ReesAlgebraSheaf

end Uniqueness

end Hartshorne
