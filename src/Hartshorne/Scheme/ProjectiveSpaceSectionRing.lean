/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.GradedGlobalSections
import Hartshorne.Scheme.ProjGradedModuleSheafCoherent
import Hartshorne.Scheme.ProjectiveSpaceChart

/-!
# The section ring of projective space

Hartshorne, *Algebraic Geometry*, II, Proposition 5.13 (p. 118).

Let `S = R[x₀, …, xᵣ]` with `r ≥ 1` and `X = Proj S`. The natural map `S → Γ_*(𝒪_X)`,
`s ↦ s · 1`, is an isomorphism (`ProjectiveSpaceSectionRing.sectionRingMap_bijective`,
`ProjectiveSpaceSectionRing.sectionRingEquiv`). It is a map of `S`-modules for the module
structure `GradedGlobalSections.gammaStarModule`, and it is graded: `S_d` goes to
`Γ(X, 𝒪_X(d))` (`ProjectiveSpaceSectionRing.sectionRingMap_of_mem`). `Γ_*(𝒪_X)` carries the
degreewise product `ProjectiveSpaceSectionRing.mulTwistGlobal` induced by
`𝒪_X(n) ⊗ 𝒪_X(m) → 𝒪_X(n + m)`, and the map is multiplicative on homogeneous elements
(`ProjectiveSpaceSectionRing.sectionRingMap_mul`). No full ring instance on `Γ_*(𝒪_X)` is built.

## Proof

On the chart `D₊(x_i)` a global section of `𝒪_X(n)` is a single fraction `a_i / x_i^{k_i}`
(`ProjGradedModuleSheaf.exists_globalValue_eq_mapOfLE`, from the chart isomorphism of
II.5.11(b)). Comparing the fractions on `D₊(x_i x_j)`, where `x_i x_j` is a nonzerodivisor, gives
`x_j^{k_j} a_i = x_i^{k_i} a_j` (`compat_of_values`). Since `r ≥ 1` there is a second variable,
and `x_0^{k_0} ∣ a_0 x_r^{k_r}` forces `x_0^{k_0} ∣ a_0`
(`MvPolynomialDvd.X_pow_dvd_of_dvd_mul_X_pow`). So every global section of `𝒪_X(n)` is `b / 1`
with `b ∈ S_n`, and `b = 0` for `n < 0` (`exists_globalValue_eq_mk`). These are the elements of
`⋂ᵢ S_{x_i}` of degree `n`, as in Hartshorne's argument.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization

namespace ProjGradedModuleSheaf

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
  (ℳ : ℤ → σM) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
  {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d)

/-- The value at `x` of a global section of `M~`. -/
def globalValue (g : (projGradedModuleSheaf 𝒜 ℳ).val.obj (op ⊤)) (x : Proj 𝒜) :
    HomogeneousLocalizedModule 𝒜 ℳ x.asHomogeneousIdeal.toIdeal.primeCompl :=
  (show (sheafInType 𝒜 ℳ).1.obj (op ⊤) from g).1 ⟨x, trivial⟩

omit [DirectSum.Decomposition ℳ] in
theorem globalValue_injective :
    Function.Injective (globalValue 𝒜 ℳ) := by
  intro g g' h
  exact Subtype.ext (funext fun x => congrFun h x.1)

theorem toChartΓ_eq_isoHom (m : HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f)) :
    (awayModuleIsoChartSections 𝒜 ℳ f_deg hd).hom m = toChartΓ 𝒜 ℳ f_deg hd m := by
  change (modulesSpecToSheaf.map (fromTildeChart 𝒜 ℳ f_deg hd)).1.app (op ⊤)
    (tilde.toOpen (awayModule 𝒜 ℳ f) ⊤ m) = _
  rw [fromTildeChart_app_toOpen]
  have : (homOfLE le_top : (⊤ : (Spec (.of (Away 𝒜 f))).Opens) ⟶ ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The chart map `M_(f) → Γ(D₊(f), M~)` is bijective** (from Hartshorne II.5.11(b)). -/
theorem toChartΓ_bijective : Function.Bijective (toChartΓ 𝒜 ℳ f_deg hd) := by
  have h := ConcreteCategory.bijective_of_isIso (awayModuleIsoChartSections 𝒜 ℳ f_deg hd).hom
  have key : ⇑(toChartΓ 𝒜 ℳ f_deg hd) = ⇑(awayModuleIsoChartSections 𝒜 ℳ f_deg hd).hom :=
    funext fun m => (toChartΓ_eq_isoHom 𝒜 ℳ f_deg hd m).symm
  rw [key]
  exact h

theorem mem_image_top_of_mem_basicOpen {x : Proj 𝒜} (hx : x ∈ Proj.basicOpen 𝒜 f) :
    x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤ := by
  have hD : (Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤ = Proj.basicOpen 𝒜 f :=
    (Scheme.Hom.image_top_eq_opensRange _).trans (Proj.opensRange_awayι 𝒜 f f_deg hd)
  rw [hD]
  exact hx

/-- On the chart `D₊(f)`, a global section of `M~` is a single fraction `m ∈ M_(f)`. -/
theorem exists_globalValue_eq_mapOfLE (g : (projGradedModuleSheaf 𝒜 ℳ).val.obj (op ⊤)) :
    ∃ m : HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f),
      ∀ (x : Proj 𝒜) (hx : x ∈ Proj.basicOpen 𝒜 f),
        globalValue 𝒜 ℳ g x = HomogeneousLocalizedModule.mapOfLE 𝒜 ℳ
          (powers_le_of_mem 𝒜 f_deg hd (mem_image_top_of_mem_basicOpen 𝒜 f_deg hd hx)) m := by
  let g' : chartSections 𝒜 ℳ f_deg hd ⊤ :=
    (show (sheafInType 𝒜 ℳ).1.obj (op ((Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤)) from
      (projGradedModuleSheaf 𝒜 ℳ).val.presheaf.map (homOfLE le_top).op g)
  obtain ⟨m, hm⟩ := (toChartΓ_bijective 𝒜 ℳ f_deg hd).2 g'
  refine ⟨m, fun x hx => ?_⟩
  have := congrArg (fun s => chartEval s x (mem_image_top_of_mem_basicOpen 𝒜 f_deg hd hx)) hm
  exact this.symm

/-- A fraction `m ∈ M_(f)` vanishing at every point of `D₊(f)` is zero. -/
theorem eq_zero_of_mapOfLE_eq_zero (m : HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f))
    (h : ∀ (x : Proj 𝒜) (hx : x ∈ (Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤),
      HomogeneousLocalizedModule.mapOfLE 𝒜 ℳ (powers_le_of_mem 𝒜 f_deg hd hx) m = 0) :
    m = 0 := by
  apply (toChartΓ_bijective 𝒜 ℳ f_deg hd).1
  rw [map_zero]
  apply chartSections_ext
  intro x hx
  rw [toChartΓ_apply, chartEval_toChartSection, h x hx]
  rfl

end ProjGradedModuleSheaf

namespace MvPolynomialDvd

open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- `X_i^k` divides `p` exactly when every monomial of `p` has `x_i`-exponent at least `k`. -/
theorem X_pow_dvd_iff {i : σ} {k : ℕ} {p : MvPolynomial σ R} :
    X i ^ k ∣ p ↔ ∀ d : σ →₀ ℕ, d i < k → coeff d p = 0 := by
  classical
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h d hd
    have hnle : ¬ Finsupp.single i k ≤ d := fun hle => by
      have := hle i
      rw [Finsupp.single_eq_same] at this
      omega
    rw [← coeff_modMonomial_of_not_le p hnle, h, coeff_zero]
  · intro h
    ext d
    rw [coeff_zero]
    by_cases hle : Finsupp.single i k ≤ d
    · exact coeff_modMonomial_of_le p hle
    · rw [coeff_modMonomial_of_not_le p hle]
      apply h
      by_contra hk
      apply hle
      rw [Finsupp.single_le_iff]
      omega

/-- For `i ≠ j`, if `x_i^k` divides `a x_j^m` then it divides `a`. -/
theorem X_pow_dvd_of_dvd_mul_X_pow {i j : σ} (hij : i ≠ j) {k m : ℕ} {a : MvPolynomial σ R}
    (h : X i ^ k ∣ a * X j ^ m) : X i ^ k ∣ a := by
  classical
  rw [X_pow_dvd_iff] at h ⊢
  intro d hd
  have h2 := h (d + Finsupp.single j m) (by simpa [Finsupp.single_apply, Ne.symm hij] using hd)
  rwa [X_pow_eq_monomial, coeff_mul_monomial', if_pos le_add_self, add_tsub_cancel_right,
    mul_one] at h2

end MvPolynomialDvd

namespace ProjectiveSpaceSectionRing

section SectionRing

open MvPolynomial ProjGradedModuleSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {r : ℕ}

local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R

theorem X_pow_mem (i : Fin (r + 1)) (k : ℕ) : (X i ^ k : MvPolynomial (Fin (r + 1)) R) ∈ 𝒮 k :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X_pow i k)

/-- On `ℙʳ_R`, two chart fractions `a_i / x_i^{k_i}` and `a_j / x_j^{k_j}` describing the same
section on `D₊(x_i) ∩ D₊(x_j)` satisfy `x_j^{k_j} a_i = x_i^{k_i} a_j`. -/
theorem compat_of_values (n : ℤ) {i j : Fin (r + 1)} {ki kj : ℕ}
    {ai aj : MvPolynomial (Fin (r + 1)) R} (hai : ai ∈ gradedTwist 𝒮 n ki)
    (haj : aj ∈ gradedTwist 𝒮 n kj)
    (h : ∀ x : Proj 𝒮, x ∈ Proj.basicOpen 𝒮 (X i * X j) →
      ∀ (hi : X i ^ ki ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
        (hj : X j ^ kj ∈ x.asHomogeneousIdeal.toIdeal.primeCompl),
        (LocalizedModule.mk ai ⟨X i ^ ki, hi⟩ : LocalizedModule _ (MvPolynomial (Fin (r + 1)) R)) =
          LocalizedModule.mk aj ⟨X j ^ kj, hj⟩) :
    X j ^ kj * ai = X i ^ ki * aj := by
  have hf : (X i * X j : MvPolynomial (Fin (r + 1)) R) ∈ 𝒮 2 :=
    (mem_homogeneousSubmodule _ _).2 ((isHomogeneous_X R i).mul (isHomogeneous_X R j))
  set K := ki + kj
  set w : MvPolynomial (Fin (r + 1)) R := X j ^ kj * ai - X i ^ ki * aj
  set u : MvPolynomial (Fin (r + 1)) R := (X i ^ kj * X j ^ ki) * w
  have hw : w ∈ gradedTwist 𝒮 n ((kj : ℤ) + ki) := by
    refine sub_mem ?_ ?_
    · exact smul_mem_graded_nat 𝒮 (gradedTwist 𝒮 n) (X_pow_mem j kj) hai
    · have := smul_mem_graded_nat 𝒮 (gradedTwist 𝒮 n) (X_pow_mem i ki) haj
      rwa [show ((ki : ℕ) : ℤ) + kj = (kj : ℤ) + ki by ring] at this
  have hXX : (X i ^ kj * X j ^ ki : MvPolynomial (Fin (r + 1)) R) ∈ 𝒮 (kj + ki) :=
    SetLike.GradedMul.mul_mem (X_pow_mem i kj) (X_pow_mem j ki)
  have hu : u ∈ gradedTwist 𝒮 n ((2 * K : ℕ) : ℤ) := by
    have := smul_mem_graded_nat 𝒮 (gradedTwist 𝒮 n) hXX hw
    rwa [show (((kj + ki : ℕ)) : ℤ) + ((kj : ℤ) + ki) = ((2 * K : ℕ) : ℤ) by push_cast [K]; ring]
      at this
  have hden : ((X i * X j) ^ K : MvPolynomial (Fin (r + 1)) R) ∈ 𝒮 (2 * K) := by
    rw [show 2 * K = K • 2 by rw [smul_eq_mul, mul_comm]]
    exact SetLike.pow_mem_graded K hf
  let μ : HomogeneousLocalizedModule 𝒮 (gradedTwist 𝒮 n) (Submonoid.powers (X i * X j)) :=
    HomogeneousLocalizedModule.mk (2 * K) u hu ((X i * X j) ^ K) hden ⟨K, rfl⟩
  have hμ : μ = 0 := by
    refine eq_zero_of_mapOfLE_eq_zero 𝒮 (gradedTwist 𝒮 n) hf two_pos μ fun x hx => ?_
    have hfx := awayι_mem_basicOpen 𝒮 hf two_pos hx
    have hxi : (X i : MvPolynomial (Fin (r + 1)) R) ∉ x.asHomogeneousIdeal := fun h' =>
      hfx (Ideal.mul_mem_right _ _ h')
    have hxj : (X j : MvPolynomial (Fin (r + 1)) R) ∉ x.asHomogeneousIdeal := fun h' =>
      hfx (Ideal.mul_mem_left _ _ h')
    have hpi : X i ^ ki ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := fun h' =>
      hxi (x.isPrime.mem_of_pow_mem _ h')
    have hpj : X j ^ kj ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := fun h' =>
      hxj (x.isPrime.mem_of_pow_mem _ h')
    obtain ⟨v, hv⟩ := LocalizedModule.mk_eq.1 (h x hfx hpi hpj)
    apply HomogeneousLocalizedModule.ext
    rw [HomogeneousLocalizedModule.mapOfLE_mk, HomogeneousLocalizedModule.val_mk,
      HomogeneousLocalizedModule.val_zero, ← LocalizedModule.zero_mk 1]
    refine LocalizedModule.mk_eq.2 ⟨v, ?_⟩
    simp only [Submonoid.smul_def, smul_eq_mul, mul_zero, OneMemClass.coe_one, one_mul] at hv ⊢
    simp only [u, w]
    linear_combination (X i ^ kj * X j ^ ki) * hv
  have hval := congrArg HomogeneousLocalizedModule.val hμ
  rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_zero,
    ← LocalizedModule.zero_mk 1] at hval
  obtain ⟨⟨v, N, rfl⟩, hv⟩ := LocalizedModule.mk_eq.1 hval
  simp only [Submonoid.smul_def, smul_eq_mul, mul_zero, OneMemClass.coe_one, one_mul] at hv
  have hreg : IsRegular ((X i * X j) ^ N * (X i ^ kj * X j ^ ki) :
      MvPolynomial (Fin (r + 1)) R) :=
    ((isRegular_X.mul isRegular_X).pow N).mul ((isRegular_X_pow kj).mul (isRegular_X_pow ki))
  have hw0 : w = 0 := hreg.left (show _ * w = _ * 0 by rw [mul_zero, ← hv, mul_assoc])
  exact sub_eq_zero.1 hw0

/-- **Global sections of `𝒪(n)` on `ℙʳ_R`, `r ≥ 1`.** Every global section of `𝒪(n)` is
`b / 1` for some `b ∈ S_n` (with `b = 0` when `n < 0`). -/
theorem exists_globalValue_eq_mk (hr : 0 < r) (n : ℤ)
    (g : (projTwistingSheaf 𝒮 n).val.obj (op ⊤)) :
    ∃ b : MvPolynomial (Fin (r + 1)) R, b ∈ gradedTwist 𝒮 n 0 ∧
      ∀ x : Proj 𝒮, (globalValue 𝒮 (gradedTwist 𝒮 n) g x).val = LocalizedModule.mk b 1 := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · have hsub : ∀ p : MvPolynomial (Fin (r + 1)) R, p = 0 := fun p =>
      MvPolynomial.ext _ _ fun _ => Subsingleton.elim _ _
    refine ⟨0, zero_mem _, fun x => ?_⟩
    generalize (globalValue 𝒮 (gradedTwist 𝒮 n) g x).val = y
    induction y using LocalizedModule.induction_on with
    | h m t => rw [hsub m, LocalizedModule.zero_mk, LocalizedModule.zero_mk]
  choose m hm using fun i : Fin (r + 1) =>
    exists_globalValue_eq_mapOfLE 𝒮 (gradedTwist 𝒮 n) (X_mem_homogeneousSubmodule_one R i)
      one_pos g
  choose k a ha c hc hcx hmk using fun i => HomogeneousLocalizedModule.mk_surjective (m i)
  have hci : ∀ i, c i = X i ^ k i := by
    intro i
    obtain ⟨e, he⟩ := hcx i
    have he' : k i = e := DirectSum.degree_eq_of_mem_mem 𝒮 (hc i) (he ▸ X_pow_mem i e)
      (he ▸ (isRegular_X_pow e).ne_zero)
    rw [← he, he']
  have hval : ∀ i (x : Proj 𝒮) (hx : x ∈ Proj.basicOpen 𝒮 (X i))
      (h' : X i ^ k i ∈ x.asHomogeneousIdeal.toIdeal.primeCompl),
      (globalValue 𝒮 (gradedTwist 𝒮 n) g x).val = LocalizedModule.mk (a i) ⟨X i ^ k i, h'⟩ := by
    intro i x hx h'
    rw [hm i x hx, hmk i, HomogeneousLocalizedModule.mapOfLE_mk,
      HomogeneousLocalizedModule.val_mk]
    congr 1
    exact Subtype.ext (hci i)
  have hcomp : ∀ i j, X j ^ k j * a i = X i ^ k i * a j := by
    intro i j
    refine compat_of_values n (ha i) (ha j) fun x hx hi hj => ?_
    rw [Proj.basicOpen_mul] at hx
    rw [← hval i x hx.1 hi, ← hval j x hx.2 hj]
  have h0 : (0 : Fin (r + 1)) ≠ Fin.last r := by
    rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    omega
  obtain ⟨b₀, hb₀⟩ := MvPolynomialDvd.X_pow_dvd_of_dvd_mul_X_pow h0
    (show X 0 ^ k 0 ∣ a 0 * X (Fin.last r) ^ k (Fin.last r) from
      ⟨a (Fin.last r), by rw [mul_comm]; exact hcomp 0 (Fin.last r)⟩)
  obtain ⟨b, hb, hab⟩ : ∃ b, b ∈ gradedTwist 𝒮 n 0 ∧ a 0 = X 0 ^ k 0 * b := by
    have ha0 : a 0 ∈ 𝒮 (n + k 0).toNat ∧ (n + k 0 < 0 → a 0 = 0) := ha 0
    by_cases hneg : n + (k 0 : ℤ) < 0
    · exact ⟨0, zero_mem _, by rw [ha0.2 hneg, mul_zero]⟩
    · have hdec : a 0 = (DirectSum.decompose 𝒮 (X 0 ^ k 0 * b₀) (n + k 0).toNat :
          MvPolynomial (Fin (r + 1)) R) := by
        rw [← hb₀, DirectSum.decompose_of_mem_same 𝒮 ha0.1]
      by_cases hle : k 0 ≤ (n + k 0).toNat
      · refine ⟨DirectSum.decompose 𝒮 b₀ ((n + k 0).toNat - k 0), ?_, ?_⟩
        · exact (mem_gradedTwist_of_eq (k := (n + k 0).toNat - k 0) (by omega)).2
            (SetLike.coe_mem _)
        · rw [hdec, DirectSum.coe_decompose_mul_of_left_mem_of_le 𝒮 (X_pow_mem 0 (k 0)) hle]
      · refine ⟨0, zero_mem _, ?_⟩
        rw [mul_zero, hdec,
          DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒮 (X_pow_mem 0 (k 0)) hle]
  have haj : ∀ j, a j = X j ^ k j * b := by
    intro j
    apply (isRegular_X_pow (k 0)).left
    show X 0 ^ k 0 * a j = X 0 ^ k 0 * (X j ^ k j * b)
    rw [hcomp j 0, hab]
    ring
  refine ⟨b, hb, fun x => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, x ∈ Proj.basicOpen 𝒮 (X j) := by
    have hx : x ∈ (⨆ j, Proj.basicOpen 𝒮 (X j) : (Proj 𝒮).Opens) := by
      rw [iSup_proj_basicOpen_X_eq_top]
      trivial
    exact Opens.mem_iSup.mp hx
  have hpj : X j ^ k j ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := fun h' =>
    hj (x.isPrime.mem_of_pow_mem _ h')
  rw [hval j x hj hpj, haj j]
  refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
  simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul]

/-- On `ℙʳ_R`, `r ≥ 1`, the twists `𝒪(n)` with `n < 0` have no nonzero global sections. -/
theorem projTwistingSheaf_global_eq_zero (hr : 0 < r) {n : ℤ} (hn : n < 0)
    (g : (projTwistingSheaf 𝒮 n).val.obj (op ⊤)) : g = 0 := by
  obtain ⟨b, hb, hg⟩ := exists_globalValue_eq_mk hr n g
  have hb0 : b = 0 := hb.2 (by omega)
  apply globalValue_injective 𝒮 (gradedTwist 𝒮 n)
  funext x
  apply HomogeneousLocalizedModule.ext
  rw [hg x, hb0, LocalizedModule.zero_mk]
  rfl

theorem globalValue_twistSection (d : ℕ) (s : 𝒮 d) (x : Proj 𝒮) :
    (globalValue 𝒮 (gradedTwist 𝒮 d) (GradedGlobalSections.twistSection d s (op ⊤)) x).val =
      LocalizedModule.mk (s : MvPolynomial (Fin (r + 1)) R) 1 :=
  rfl

/-- On `ℙʳ_R`, `r ≥ 1`, `s ↦ s / 1` is a bijection `S_d → Γ(ℙʳ_R, 𝒪(d))`. -/
theorem twistSection_top_bijective (hr : 0 < r) (d : ℕ) :
    Function.Bijective fun s : 𝒮 d => GradedGlobalSections.twistSection d s (op ⊤) := by
  constructor
  · intro s s' h
    have h' := fun x => congrArg (fun g => (globalValue 𝒮 (gradedTwist 𝒮 d) g x).val) h
    simp only [globalValue_twistSection] at h'
    have hs := (mem_gradedTwist_of_eq (n := (d : ℤ)) (d := ((0 : ℕ) : ℤ)) (k := d)
      (by omega)).2 s.2
    have hs' := (mem_gradedTwist_of_eq (n := (d : ℤ)) (d := ((0 : ℕ) : ℤ)) (k := d)
      (by omega)).2 s'.2
    have := compat_of_values (r := r) (d : ℤ) (i := 0) (j := 0) hs hs' fun x _ hi hj => by
      have e := h' x
      simp only [pow_zero] at hi hj ⊢
      exact e
    simp only [pow_zero, one_mul] at this
    exact Subtype.ext this
  · intro g
    obtain ⟨b, hb, hg⟩ := exists_globalValue_eq_mk hr d g
    refine ⟨⟨b, (mem_gradedTwist_of_eq (by omega)).1 hb⟩, ?_⟩
    apply globalValue_injective 𝒮 (gradedTwist 𝒮 d)
    funext x
    apply HomogeneousLocalizedModule.ext
    rw [hg x]
    rfl

end SectionRing

/-! ### The section ring map `S → Γ_*(𝒪_X)` -/

section GammaStar

open GradedGlobalSections Ringed MonoidalCategory MvPolynomial ProjGradedModuleSheaf

attribute [local instance] MvPolynomial.gradedAlgebra GradedGlobalSections.gammaStarModule

variable {R : Type u} [CommRing R] {r : ℕ}

local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R
local notation "𝒪" => 𝟙_ (Scheme.Modules (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)))

variable (R r) in
/-- The global section `1 ⊗ 1` of `𝒪_X ⊗ 𝒪_X(0)`, the unit of `Γ_*(𝒪_X)`. -/
def unitSection : twistGlobal 𝒪 0 :=
  tmulSection _ _ (oneSec (op ⊤)) (twistSection 0 ⟨1, SetLike.GradedOne.one_mem⟩ (op ⊤))

variable (R r) in
/-- **The natural map `S → Γ_*(𝒪_X)`**, `s ↦ s · 1`, as a map of `S`-modules. On `S_d` it is
`s ↦ s / 1 ∈ Γ(X, 𝒪_X(d))`. -/
def sectionRingMap :
    MvPolynomial (Fin (r + 1)) R →ₗ[MvPolynomial (Fin (r + 1)) R] GammaStar 𝒪 :=
  LinearMap.toSpanSingleton _ _ (DirectSum.of (fun m => twistGlobal 𝒪 m) 0 (unitSection R r))

/-- The section ring map is graded: it sends `S_d` to `Γ(X, 𝒪_X(d))`. -/
theorem sectionRingMap_of_mem {d : ℕ} {s : MvPolynomial (Fin (r + 1)) R} (hs : s ∈ 𝒮 d) :
    sectionRingMap R r s = DirectSum.of (fun m => twistGlobal 𝒪 m) (0 + d)
      (mulGlobal 𝒪 0 d ⟨s, hs⟩ (unitSection R r)) :=
  smul_of 𝒪 hs 0 (unitSection R r)

/-- The left unitor on global sections, `Γ(X, 𝒪_X ⊗ 𝒪_X(n)) → Γ(X, 𝒪_X(n))`. -/
def unitorGlobal (n : ℤ) : twistGlobal 𝒪 n → (projTwistingSheaf 𝒮 n).val.obj (op ⊤) :=
  fun y => (λ_ (projTwistingSheaf 𝒮 n)).hom.val.app (op ⊤) y

theorem unitorGlobal_bijective (n : ℤ) :
    Function.Bijective (unitorGlobal (R := R) (r := r) n) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun z => (λ_ (projTwistingSheaf 𝒮 n)).inv.val.app (op ⊤) z, fun y => ?_, fun z => ?_⟩
  · change ((λ_ (projTwistingSheaf 𝒮 n)).hom ≫ (λ_ _).inv).val.app (op ⊤) y = y
    rw [Iso.hom_inv_id]
    rfl
  · change ((λ_ (projTwistingSheaf 𝒮 n)).inv ≫ (λ_ _).hom).val.app (op ⊤) z = z
    rw [Iso.inv_hom_id]
    rfl

theorem unitorGlobal_add (n : ℤ) (y y' : twistGlobal 𝒪 n) :
    unitorGlobal (R := R) (r := r) n (y + y') = unitorGlobal n y + unitorGlobal n y' :=
  map_add _ _ _

theorem unitorGlobal_zero (n : ℤ) : unitorGlobal (R := R) (r := r) n 0 = 0 :=
  map_zero _

/-- The degree-`n` part of `s`, as an element of `S` (zero for `n < 0`). -/
def degreePart (n : ℤ) (s : MvPolynomial (Fin (r + 1)) R) : MvPolynomial (Fin (r + 1)) R :=
  if 0 ≤ n then (DirectSum.decompose 𝒮 s n.toNat : MvPolynomial (Fin (r + 1)) R) else 0

theorem degreePart_add (n : ℤ) (s t : MvPolynomial (Fin (r + 1)) R) :
    degreePart n (s + t) = degreePart n s + degreePart n t := by
  unfold degreePart
  split_ifs
  · rw [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
  · rw [add_zero]

theorem degreePart_zero (n : ℤ) : degreePart n (0 : MvPolynomial (Fin (r + 1)) R) = 0 := by
  unfold degreePart
  split_ifs
  · rw [DirectSum.decompose_zero]
    rfl
  · rfl

theorem globalValue_add {n : ℤ} (g g' : (projTwistingSheaf 𝒮 n).val.obj (op ⊤)) (x : Proj 𝒮) :
    globalValue 𝒮 (gradedTwist 𝒮 n) (g + g') x =
      globalValue 𝒮 (gradedTwist 𝒮 n) g x + globalValue 𝒮 (gradedTwist 𝒮 n) g' x :=
  rfl

theorem globalValue_zero {n : ℤ} (x : Proj 𝒮) :
    globalValue 𝒮 (gradedTwist 𝒮 n) (0 : (projTwistingSheaf 𝒮 n).val.obj (op ⊤)) x = 0 :=
  rfl

/-- The value at `x` of an element of `Γ(X, 𝒪_X ⊗ 𝒪_X(n))`. -/
def twistValue (n : ℤ) (t : twistGlobal 𝒪 n) (x : Proj 𝒮) :
    LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl (MvPolynomial (Fin (r + 1)) R) :=
  (globalValue 𝒮 (gradedTwist 𝒮 n) (unitorGlobal n t) x).val

theorem twistValue_add (n : ℤ) (t t' : twistGlobal 𝒪 n) (x : Proj 𝒮) :
    twistValue n (t + t') x = twistValue n t x + twistValue n t' x := by
  have e := congrArg (fun g => (globalValue 𝒮 (gradedTwist 𝒮 n) g x).val)
    (unitorGlobal_add (R := R) (r := r) n t t')
  exact e

theorem twistValue_zero (n : ℤ) (x : Proj 𝒮) : twistValue n (0 : twistGlobal 𝒪 n) x = 0 := by
  have e := congrArg (fun g => (globalValue 𝒮 (gradedTwist 𝒮 n) g x).val)
    (unitorGlobal_zero (R := R) (r := r) n)
  exact e

theorem eq_of_twistValue_eq {n : ℤ} {t t' : twistGlobal 𝒪 n}
    (h : ∀ x, twistValue n t x = twistValue n t' x) :
    t = t' := by
  apply (unitorGlobal_bijective n).1
  apply globalValue_injective 𝒮 (gradedTwist 𝒮 n)
  funext x
  exact HomogeneousLocalizedModule.ext (h x)

theorem eq_of_twistValue_component_eq {y y' : GammaStar 𝒪}
    (h : ∀ n x, twistValue n (y n) x = twistValue n (y' n) x) :
    y = y' := by
  ext n
  exact eq_of_twistValue_eq (h n)

theorem twistValue_of_ne {m n : ℤ} (h : m ≠ n) (z : twistGlobal 𝒪 m) (x : Proj 𝒮) :
    twistValue n (DirectSum.of (fun k => twistGlobal 𝒪 k) m z n) x = 0 :=
  (congrArg (fun t => twistValue n t x) (DirectSum.of_eq_of_ne _ _ _ h.symm)).trans
    (twistValue_zero n x)

theorem twistValue_of_same {n : ℤ} (z : twistGlobal 𝒪 n) (x : Proj 𝒮) :
    twistValue n (DirectSum.of (fun k => twistGlobal 𝒪 k) n z n) x = twistValue n z x :=
  congrArg (fun t => twistValue n t x) (DirectSum.of_eq_same _ _)

/-- `s · 1 = s / 1` on values, for `s ∈ S_d`. -/
theorem twistValue_mulGlobal_unitSection {d : ℕ} {s : MvPolynomial (Fin (r + 1)) R} (hs : s ∈ 𝒮 d)
    (x : Proj 𝒮) :
    twistValue (0 + d) (mulGlobal 𝒪 0 d ⟨s, hs⟩ (unitSection R r)) x = LocalizedModule.mk s 1 := by
  let h := (twistMulHom 𝒮 0 d).val.app (op ⊤) (tmulSection _ _
    (twistSection 0 ⟨1, SetLike.GradedOne.one_mem⟩ (op ⊤)) (twistSection d ⟨s, hs⟩ (op ⊤)))
  have e0 : mulGlobal 𝒪 0 d ⟨s, hs⟩ (unitSection R r) = tmulSection _ _ (oneSec (op ⊤)) h :=
    mulMap_tmulSection 𝒪 0 d ⟨s, hs⟩ (oneSec (op ⊤)) _
  have e1 := leftUnitor_hom_tmulSection (projTwistingSheaf 𝒮 (0 + d)) (U := op ⊤)
    (1 : (Proj 𝒮).ringCatSheaf.obj.obj (op ⊤)) h
  refine (congrArg (fun t => twistValue (0 + d) t x) e0).trans ?_
  refine (congrArg (fun g => (globalValue 𝒮 (gradedTwist 𝒮 (0 + d)) g x).val)
    (e1.trans (one_smul ((Proj 𝒮).ringCatSheaf.obj.obj (op ⊤)) h))).trans ?_
  refine (twistMulHom_tmul_twistSection_apply (𝒜 := 𝒮) 0 d ⟨s, hs⟩
    (twistSection 0 ⟨1, SetLike.GradedOne.one_mem⟩ (op ⊤)) ⟨x, trivial⟩).trans ?_
  change (s : MvPolynomial (Fin (r + 1)) R) • LocalizedModule.mk (1 : MvPolynomial _ R) 1 = _
  rw [LocalizedModule.smul'_mk, smul_eq_mul, mul_one]

theorem localizedModule_mk_add_one {S : Submonoid (MvPolynomial (Fin (r + 1)) R)}
    (a b : MvPolynomial (Fin (r + 1)) R) :
    (LocalizedModule.mk (a + b) 1 : LocalizedModule S (MvPolynomial (Fin (r + 1)) R)) =
      LocalizedModule.mk a 1 + LocalizedModule.mk b 1 := by
  rw [LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]

theorem degreePart_of_mem {d : ℕ} {s : MvPolynomial (Fin (r + 1)) R} (hs : s ∈ 𝒮 d) (n : ℤ) :
    degreePart n s = if n = d then s else 0 := by
  classical
  unfold degreePart
  by_cases hn : 0 ≤ n
  · rw [if_pos hn]
    by_cases hnd : n = d
    · rw [if_pos hnd, show n.toNat = d by omega, DirectSum.decompose_of_mem_same 𝒮 hs]
    · rw [if_neg hnd, DirectSum.decompose_of_mem_ne 𝒮 hs (by omega)]
  · rw [if_neg hn, if_neg (by omega)]

/-- **The components of `s · 1`.** The degree-`n` component of the image of `s` in `Γ_*(𝒪_X)`
is the section `s_n / 1` of `𝒪_X(n)`. -/
theorem twistValue_sectionRingMap (s : MvPolynomial (Fin (r + 1)) R) (n : ℤ) (x : Proj 𝒮) :
    twistValue n (sectionRingMap R r s n) x = LocalizedModule.mk (degreePart n s) 1 := by
  classical
  induction s using DirectSum.Decomposition.inductionOn 𝒮 with
  | zero =>
    refine (congrArg (fun y : GammaStar 𝒪 => twistValue n (y n) x)
      (map_zero (sectionRingMap R r))).trans
      ?_
    rw [degreePart_zero, LocalizedModule.zero_mk]
    exact twistValue_zero n x
  | @homogeneous d m =>
    rw [degreePart_of_mem m.2]
    refine (congrArg (fun y : GammaStar 𝒪 => twistValue n (y n) x)
      (sectionRingMap_of_mem m.2)).trans ?_
    by_cases hnd : (0 + d : ℤ) = n
    · subst hnd
      rw [if_pos (zero_add _)]
      exact (twistValue_of_same _ x).trans (twistValue_mulGlobal_unitSection m.2 x)
    · rw [if_neg (by omega), LocalizedModule.zero_mk]
      exact twistValue_of_ne hnd _ x
  | add s t hs ht =>
    refine (congrArg (fun y : GammaStar 𝒪 => twistValue n (y n) x)
      (map_add (sectionRingMap R r) s t)).trans
      ?_
    rw [DirectSum.add_apply, twistValue_add, hs, ht, degreePart_add, localizedModule_mk_add_one]

theorem degreePart_natCast (d : ℕ) (s : MvPolynomial (Fin (r + 1)) R) :
    degreePart (d : ℤ) s = (DirectSum.decompose 𝒮 s d : MvPolynomial (Fin (r + 1)) R) := by
  unfold degreePart
  rw [if_pos (Int.natCast_nonneg d), Int.toNat_natCast]

theorem eq_of_mk_eq_mk {d : ℕ} (hr : 0 < r) {a b : MvPolynomial (Fin (r + 1)) R} (ha : a ∈ 𝒮 d)
    (hb : b ∈ 𝒮 d) (h : ∀ x : Proj 𝒮,
      (LocalizedModule.mk a 1 : LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl _) =
        LocalizedModule.mk b 1) : a = b := by
  have key : GradedGlobalSections.twistSection d ⟨a, ha⟩ (op ⊤) =
      GradedGlobalSections.twistSection d ⟨b, hb⟩ (op ⊤) := by
    apply globalValue_injective 𝒮 (gradedTwist 𝒮 d)
    funext x
    exact HomogeneousLocalizedModule.ext (h x)
  exact congrArg Subtype.val ((twistSection_top_bijective (R := R) hr d).1 key)

/-- **Hartshorne II, Proposition 5.13.** For `S = R[x₀, …, xᵣ]` with `r ≥ 1` and `X = Proj S`,
the natural map `S → Γ_*(𝒪_X)` is bijective. -/
theorem sectionRingMap_bijective (hr : 0 < r) : Function.Bijective (sectionRingMap R r) := by
  classical
  constructor
  · intro s t hst
    have hv : ∀ (n : ℤ) (x : Proj 𝒮),
        (LocalizedModule.mk (degreePart n s) 1 :
          LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl
          _) = LocalizedModule.mk (degreePart n t) 1 := fun n x => by
      rw [← twistValue_sectionRingMap, ← twistValue_sectionRingMap]
      exact congrArg (fun y : GammaStar 𝒪 => twistValue n (y n) x) hst
    apply (DirectSum.decompose 𝒮).injective
    ext d : 1
    apply Subtype.ext
    apply eq_of_mk_eq_mk hr (SetLike.coe_mem _) (SetLike.coe_mem _)
    intro x
    have := hv d x
    rwa [degreePart_natCast, degreePart_natCast] at this
  · intro y
    induction y using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of n z =>
      obtain ⟨b, hb, hg⟩ := exists_globalValue_eq_mk hr n (unitorGlobal n z)
      have hb' : b ∈ 𝒮 (n + 0).toNat ∧ (n + 0 < 0 → b = 0) := hb
      refine ⟨b, eq_of_twistValue_component_eq fun m x => ?_⟩
      rw [twistValue_sectionRingMap]
      by_cases hm : n = m
      · subst hm
        rw [twistValue_of_same]
        refine Eq.trans ?_ (hg x).symm
        congr 1
        unfold degreePart
        split_ifs with h0
        · rw [add_zero] at hb'
          exact DirectSum.decompose_of_mem_same 𝒮 hb'.1
        · exact (hb'.2 (by omega)).symm
      · rw [twistValue_of_ne hm]
        have : degreePart m b = 0 := by
          unfold degreePart
          split_ifs with h0
          · by_cases hn : n < 0
            · rw [hb'.2 (by omega), DirectSum.decompose_zero]
              rfl
            · rw [add_zero] at hb'
              exact DirectSum.decompose_of_mem_ne 𝒮 hb'.1 (by omega)
          · rfl
        rw [this, LocalizedModule.zero_mk]
    | add y y' hy hy' =>
      obtain ⟨s, rfl⟩ := hy
      obtain ⟨t, rfl⟩ := hy'
      exact ⟨s + t, map_add _ _ _⟩

variable (R) in
/-- **Hartshorne II, Proposition 5.13**, as an isomorphism of graded `S`-modules: for
`S = R[x₀, …, xᵣ]` with `r ≥ 1`, the natural map `S → Γ_*(𝒪_X)` is an isomorphism. -/
def sectionRingEquiv (hr : 0 < r) :
    MvPolynomial (Fin (r + 1)) R ≃ₗ[MvPolynomial (Fin (r + 1)) R] GammaStar 𝒪 :=
  LinearEquiv.ofBijective (sectionRingMap R r) (sectionRingMap_bijective hr)

/-- **The product on `Γ_*(𝒪_X)`**, degreewise:
`Γ(X, 𝒪_X ⊗ 𝒪_X(n)) × Γ(X, 𝒪_X ⊗ 𝒪_X(m)) → Γ(X, 𝒪_X ⊗ 𝒪_X(n + m))`, through the unitors and
the multiplication `𝒪_X(n) ⊗ 𝒪_X(m) → 𝒪_X(n + m)`. -/
def mulTwistGlobal (n m : ℤ) (y : twistGlobal 𝒪 n) (z : twistGlobal 𝒪 m) :
    twistGlobal 𝒪 (n + m) :=
  (λ_ (projTwistingSheaf 𝒮 (n + m))).inv.val.app (op ⊤)
    ((twistMulHom 𝒮 n m).val.app (op ⊤) (tmulSection _ _ (unitorGlobal n y) (unitorGlobal m z)))

/-- On values, the product of `Γ_*(𝒪_X)` is the product of fractions. -/
theorem twistValue_mulTwistGlobal (n m : ℤ) (y : twistGlobal 𝒪 n) (z : twistGlobal 𝒪 m)
    (x : Proj 𝒮) :
    twistValue (n + m) (mulTwistGlobal n m y z) x =
      (show Localization x.asHomogeneousIdeal.toIdeal.primeCompl from twistValue m z x) •
        twistValue n y x := by
  have e : unitorGlobal (R := R) (r := r) (n + m) (mulTwistGlobal n m y z) =
      (twistMulHom 𝒮 n m).val.app (op ⊤)
        (tmulSection _ _ (unitorGlobal n y) (unitorGlobal m z)) := by
    change ((λ_ (projTwistingSheaf 𝒮 (n + m))).inv ≫ (λ_ _).hom).val.app (op ⊤) _ = _
    rw [Iso.inv_hom_id]
    rfl
  exact (congrArg (fun g => (globalValue 𝒮 (gradedTwist 𝒮 (n + m)) g x).val) e).trans
    (twistMulHom_tmulSection (𝒜 := 𝒮) n m (U := op ⊤) _ _ ⟨x, trivial⟩)

/-- **The section ring map is multiplicative** (Hartshorne II.5.13, "graded ring
homomorphism"): for `s ∈ S_d` and `t ∈ S_e`, the product in `Γ_*(𝒪_X)` of the degree-`d`
component of the image of `s` and the degree-`e` component of the image of `t` is the
degree-`(d + e)` component of the image of `st`. -/
theorem sectionRingMap_mul {d e : ℕ} {s t : MvPolynomial (Fin (r + 1)) R} (hs : s ∈ 𝒮 d)
    (ht : t ∈ 𝒮 e) :
    mulTwistGlobal d e (sectionRingMap R r s d) (sectionRingMap R r t e) =
      sectionRingMap R r (s * t) ((d : ℤ) + e) := by
  apply eq_of_twistValue_eq
  intro x
  rw [twistValue_mulTwistGlobal, twistValue_sectionRingMap, twistValue_sectionRingMap,
    twistValue_sectionRingMap, degreePart_of_mem hs, degreePart_of_mem ht,
    degreePart_of_mem (SetLike.GradedMul.mul_mem hs ht), if_pos rfl, if_pos rfl,
    if_pos (by push_cast; rfl)]
  change Localization.mk t 1 • LocalizedModule.mk s 1 = _
  rw [LocalizedModule.mk_smul_mk, smul_eq_mul, mul_comm, mul_one]

end GammaStar

end ProjectiveSpaceSectionRing

end Hartshorne
