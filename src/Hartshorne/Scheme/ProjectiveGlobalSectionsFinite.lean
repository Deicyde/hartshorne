/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSectionRingIntegralClosure
import Hartshorne.Scheme.FiniteIntegralClosureField
import Hartshorne.Scheme.TopIsoRestriction
import Hartshorne.Intersection.GradedPrimeFiltration

/-!
# Finiteness of projective global sections: the integral case

Hartshorne, *Algebraic Geometry*, II, Theorem 5.19 (pp. 122–123), the last step of the proof.

Let `S` be a graded domain, finitely generated as an algebra over a field `k`, and generated over
`S₀` by finitely many elements `f₁, …, f_m` of degree one. Then for every `n ≥ 0` the global
sections `Γ(Proj S, 𝒪(n))` form a finitely generated `S₀`-module.

## Proof

Following Hartshorne. A global section of `𝒪(n)` is determined by its value `z` in the fraction
field `K` of `S` (`ProjectiveSectionRing.sectionToFraction`). On each chart `D₊(fᵢ)` it is a single
fraction `aᵢ / fᵢ^{jᵢ}` with `aᵢ ∈ S_{jᵢ + n}`, so `z` satisfies the chart condition `ChartCond`.
Such a `z` multiplies the nonzero finitely generated ideal `S_{≥ ∑ jᵢ}` into itself
(`exists_mem_mul_of_le`, where `S` is spanned in each degree by monomials in the `fᵢ`), so it is
integral over `S` (`isIntegral_of_chartCond`). The integral closure of `S` in `K` is a finite
`S`-module (Theorem I.3.9A), so the `S`-span of all such `z` is finitely generated, by finitely
many of them. Comparing homogeneous components in `K` of a relation
`z = ∑ cᵢ zᵢ` (`ProjectiveSectionRing.eq_zero_of_sum_isHomFrac_eq_zero`) replaces each `cᵢ` by its
degree-zero part, so these finitely many sections generate over `S₀`
(`exists_finset_of_chartCond`).
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open ProjGradedModuleSheaf ProjectiveSectionRing
open scoped DirectSum

namespace ProjectiveGlobalSectionsFinite

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {ι : Type*}

/-! ### Monomials in degree-one generators -/

private theorem prod_pow_mem {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1) (β : ι →₀ ℕ) :
    (β.prod fun i e => f i ^ e) ∈ 𝒜 β.degree := by
  rw [Finsupp.prod, Finsupp.degree_apply]
  exact SetLike.prod_mem_graded 𝒜 (fun i => β i) (fun i => f i ^ β i) fun i _ => by
    simpa using SetLike.pow_mem_graded (β i) (hf i)

/-- If `fᵢ^{jᵢ} z = aᵢ ∈ S_{jᵢ + n}` for every `i`, then `z` times a monomial of degree `d ≥ ∑ jᵢ`
in the `fᵢ` lies in `S_{d + n}`. -/
private theorem exists_mem_mul_monomial [Fintype ι] [Nonempty ι] {f : ι → A}
    (hf : ∀ i, f i ∈ 𝒜 1) {n : ℕ} {z : FractionRing A} {j : ι → ℕ} {a : ι → A}
    (ha : ∀ i, a i ∈ 𝒜 (j i + n))
    (hza : ∀ i, algebraMap A (FractionRing A) (a i) =
      algebraMap A (FractionRing A) (f i) ^ j i * z)
    {d : ℕ} (hd : ∑ i, j i ≤ d) (β : ι →₀ ℕ) (hβd : β.degree = d) :
    ∃ b ∈ 𝒜 (d + n), algebraMap A (FractionRing A) b =
      z * algebraMap A (FractionRing A) (β.prod fun i e => f i ^ e) := by
  obtain ⟨i, hi⟩ : ∃ i, j i ≤ β i := by
    by_contra! hlt
    have : ∑ i, β i < ∑ i, j i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hlt i
    rw [← Finsupp.degree_eq_sum, hβd] at this
    omega
  set β' := β - Finsupp.single i (j i) with hβ'
  have hβ : β = Finsupp.single i (j i) + β' := by
    rw [hβ', add_tsub_cancel_of_le]
    exact Finsupp.single_le_iff.2 hi
  have hdeg : d = j i + β'.degree := by
    rw [← hβd, hβ, map_add, Finsupp.degree_single]
  have hprod : (β.prod fun i e => f i ^ e) = f i ^ j i * β'.prod fun i e => f i ^ e := by
    rw [hβ, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    congr 1
    exact Finsupp.prod_single_index (pow_zero _)
  refine ⟨a i * β'.prod fun i e => f i ^ e, ?_, ?_⟩
  · have := SetLike.mul_mem_graded (ha i) (prod_pow_mem hf β')
    rwa [show j i + n + β'.degree = d + n by omega] at this
  · rw [hprod, map_mul, map_mul, hza i, map_pow]
    ring

/-- If `fᵢ^{jᵢ} z = aᵢ ∈ S_{jᵢ + n}` for every `i`, and the `fᵢ ∈ S₁` generate `S` over `S₀`, then
`z · S_d ⊆ S_{d + n}` once `d ≥ ∑ jᵢ`. -/
private theorem exists_mem_mul_of_le [Fintype ι] [Nonempty ι] {f : ι → A}
    (hf : ∀ i, f i ∈ 𝒜 1) (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤)
    {n : ℕ} {z : FractionRing A} {j : ι → ℕ} {a : ι → A}
    (ha : ∀ i, a i ∈ 𝒜 (j i + n))
    (hza : ∀ i, algebraMap A (FractionRing A) (a i) =
      algebraMap A (FractionRing A) (f i) ^ j i * z)
    {d : ℕ} (hd : ∑ i, j i ≤ d) {g : A} (hg : g ∈ 𝒜 d) :
    ∃ b ∈ 𝒜 (d + n), algebraMap A (FractionRing A) b = z * algebraMap A (FractionRing A) g := by
  classical
  have hmono := fun β hβ => exists_mem_mul_monomial hf ha hza hd β hβ
  choose! b hb hbz using hmono
  obtain ⟨P, rfl⟩ : ∃ P : MvPolynomial ι (𝒜 0), MvPolynomial.aeval f P = g := by
    have : g ∈ Algebra.adjoin (𝒜 0) (Set.range f) := hgen ▸ Algebra.mem_top
    rw [Algebra.adjoin_range_eq_range_aeval] at this
    exact this
  have hmem : ∀ β : ι →₀ ℕ, ((P.coeff β).1 * β.prod fun i e => f i ^ e) ∈ 𝒜 β.degree := by
    intro β
    have := SetLike.mul_mem_graded (P.coeff β).2 (prod_pow_mem hf β)
    rwa [zero_add] at this
  have h1 : MvPolynomial.aeval f P =
      ∑ β ∈ P.support, (P.coeff β).1 * β.prod fun i e => f i ^ e := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [MvPolynomial.aeval_monomial]
    rfl
  have hexp : MvPolynomial.aeval f P =
      ∑ β ∈ P.support with β.degree = d, (P.coeff β).1 * β.prod fun i e => f i ^ e := by
    calc MvPolynomial.aeval f P
        = (DirectSum.decompose 𝒜 (MvPolynomial.aeval f P) d : A) :=
          (DirectSum.decompose_of_mem_same 𝒜 hg).symm
      _ = ∑ β ∈ P.support,
          (DirectSum.decompose 𝒜 ((P.coeff β).1 * β.prod fun i e => f i ^ e) d : A) := by
          rw [h1, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
            AddSubmonoidClass.coe_finsetSum]
      _ = _ := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun β _ => ?_
          split_ifs with h
          · exact DirectSum.decompose_of_mem_same 𝒜 (h ▸ hmem β)
          · exact DirectSum.decompose_of_mem_ne 𝒜 (hmem β) h
  refine ⟨∑ β ∈ P.support with β.degree = d, (P.coeff β).1 * b β, ?_, ?_⟩
  · refine sum_mem fun β hβ => ?_
    have := SetLike.mul_mem_graded (P.coeff β).2 (hb β (Finset.mem_filter.1 hβ).2)
    rwa [zero_add] at this
  · rw [hexp, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [map_mul, map_mul, hbz β (Finset.mem_filter.1 hβ).2]
    ring

/-! ### The chart condition and integrality -/

variable (𝒜) in
/-- **The chart condition** on `z ∈ K`: on every chart `D₊(fᵢ)` with `fᵢ ≠ 0`, `z` is a fraction
`a / fᵢ^j` with `a ∈ S_{j + n}`. -/
def ChartCond (f : ι → A) (n : ℕ) (z : FractionRing A) : Prop :=
  ∀ i, f i ≠ 0 → ∃ (j : ℕ) (a : A), a ∈ 𝒜 (j + n) ∧
    algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) (f i) ^ j * z

omit [GradedRing 𝒜] in
private theorem chartCond_choose {f : ι → A} {n : ℕ} {z : FractionRing A}
    (hz : ChartCond 𝒜 f n z) :
    ∃ (j : ι → ℕ) (a : ι → A), (∀ i, a i ∈ 𝒜 (j i + n)) ∧
      ∀ i, algebraMap A (FractionRing A) (a i) = algebraMap A (FractionRing A) (f i) ^ j i * z := by
  classical
  have h : ∀ i, ∃ (j : ℕ) (a : A), a ∈ 𝒜 (j + n) ∧
      algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) (f i) ^ j * z := by
    intro i
    by_cases hi : f i = 0
    · exact ⟨1, 0, zero_mem _, by rw [hi, map_zero, zero_pow one_ne_zero, zero_mul]⟩
    · exact hz i hi
  choose j a ha hza using h
  exact ⟨j, a, ha, hza⟩

/-- **The determinant trick.** An element `z ∈ K` satisfying the chart condition is integral over
`S`: it multiplies the nonzero finitely generated ideal `S_{≥ ∑ jᵢ}` into itself. -/
private theorem isIntegral_of_chartCond [Fintype ι] [IsDomain A] [IsNoetherianRing A]
    {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1) (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤)
    (hne : ∃ i, f i ≠ 0) {n : ℕ} {z : FractionRing A} (hz : ChartCond 𝒜 f n z) :
    IsIntegral A z := by
  obtain ⟨j, a, ha, hza⟩ := chartCond_choose hz
  obtain ⟨i₀, hi₀⟩ := hne
  have : Nonempty ι := ⟨i₀⟩
  set N := ∑ i, j i
  let G : Set A := {g | ∃ d, N ≤ d ∧ g ∈ 𝒜 d}
  let M : Submodule A (FractionRing A) :=
    Submodule.span A (algebraMap A (FractionRing A) '' G)
  have hMfg : M.FG := by
    have h1 : (Submodule.span A G).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Algebra.linearMap A (FractionRing A))
    rwa [Submodule.map_span] at h2
  have hM0 : M ≠ ⊥ := by
    intro hM
    have hmem : algebraMap A (FractionRing A) (f i₀ ^ N) ∈ M :=
      Submodule.subset_span ⟨_, ⟨N, le_rfl, by
        simpa using SetLike.pow_mem_graded N (hf i₀)⟩, rfl⟩
    rw [hM, Submodule.mem_bot,
      map_eq_zero_iff _ (IsFractionRing.injective A (FractionRing A))] at hmem
    exact pow_ne_zero N hi₀ hmem
  refine isIntegral_of_smul_mem_submodule M hM0 hMfg z fun w hw => ?_
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g, ⟨d, hd, hg⟩, rfl⟩ := hw
    obtain ⟨b, hb, hbz⟩ := exists_mem_mul_of_le hf hgen ha hza hd hg
    rw [smul_eq_mul, ← hbz]
    exact Submodule.subset_span ⟨b, ⟨d + n, by omega, hb⟩, rfl⟩
  | zero => simp
  | add w w' _ _ hw hw' =>
    rw [smul_add]
    exact add_mem hw hw'
  | smul c w _ hw =>
    rw [smul_comm]
    exact M.smul_mem c hw

/-! ### Homogeneous fractions -/

section HomFrac

variable [IsDomain A]

private theorem isHomFrac_zero (n : ℕ) : IsHomFrac (𝒜 := 𝒜) n 0 :=
  ⟨0, 0, 1, zero_mem _, SetLike.GradedOne.one_mem, one_ne_zero, by simp⟩

private theorem isHomFrac_add {n : ℕ} {z w : FractionRing A} (hz : IsHomFrac (𝒜 := 𝒜) n z)
    (hw : IsHomFrac (𝒜 := 𝒜) n w) : IsHomFrac (𝒜 := 𝒜) n (z + w) := by
  have := hz.sub ((isHomFrac_zero n).sub hw)
  rwa [zero_sub, sub_neg_eq_add] at this

private theorem isHomFrac_smul {n e : ℕ} {z : FractionRing A} (hz : IsHomFrac (𝒜 := 𝒜) n z)
    {c : A} (hc : c ∈ 𝒜 e) : IsHomFrac (𝒜 := 𝒜) (n + e) (c • z) := by
  obtain ⟨e', a, s, ha, hs, hs0, rfl⟩ := hz
  refine ⟨e', c * a, s, ?_, hs, hs0, ?_⟩
  · have := SetLike.mul_mem_graded hc ha
    rwa [show e + (e' + n) = e' + (n + e) by ring] at this
  · rw [Algebra.smul_def, map_mul, mul_div_assoc]

private theorem isHomFrac_of_chartCond {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1) {n : ℕ}
    {z : FractionRing A} (hz : ChartCond 𝒜 f n z) {i : ι} (hi : f i ≠ 0) :
    IsHomFrac (𝒜 := 𝒜) n z := by
  obtain ⟨j, a, ha, hza⟩ := hz i hi
  have h0 : algebraMap A (FractionRing A) (f i ^ j) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 (pow_ne_zero j hi)
  refine ⟨j, a, f i ^ j, ha, by simpa using SetLike.pow_mem_graded j (hf i), pow_ne_zero j hi, ?_⟩
  rw [eq_div_iff h0, hza, map_pow, mul_comm]

end HomFrac

/-! ### Finiteness over `S₀` -/

/-- **Finitely many elements generate over `S₀`.** Let `S` be a Noetherian graded domain,
generated over `S₀` by finitely many `fᵢ ∈ S₁`, not all zero, whose integral closure in `K` is a
finite `S`-module. Then for any set `V ⊆ K` of elements satisfying the chart condition in degree
`n`, there are finitely many elements of `V` of which every element of `V` is an
`S₀`-linear combination. -/
theorem exists_finset_of_chartCond [Fintype ι] [IsDomain A] [IsNoetherianRing A]
    (hfin : Module.Finite A (integralClosure A (FractionRing A)))
    {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1) (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤)
    (hne : ∃ i, f i ≠ 0) (n : ℕ) (V : Set (FractionRing A)) (hV : ∀ z ∈ V, ChartCond 𝒜 f n z) :
    ∃ G : Finset (FractionRing A), ↑G ⊆ V ∧
      ∀ z ∈ V, ∃ c : FractionRing A → 𝒜 0, z = ∑ g ∈ G, (c g : A) • g := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  -- the `S`-span of `V` lies in the integral closure, so it is finitely generated
  have hle : Submodule.span A V ≤ Subalgebra.toSubmodule (integralClosure A (FractionRing A)) := by
    rw [Submodule.span_le]
    intro z hz
    exact isIntegral_of_chartCond hf hgen ⟨i₀, hi₀⟩ (hV z hz)
  have hfg : (Submodule.span A V).FG :=
    Submodule.FG.of_le (Module.Finite.iff_fg.1 hfin) hle
  obtain ⟨G, hGV, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset V).1 hfg
  refine ⟨G, hGV, fun z hz => ?_⟩
  have hzG : z ∈ Submodule.span A (G : Set (FractionRing A)) :=
    hspan ▸ Submodule.subset_span hz
  obtain ⟨c, -, hcz⟩ := Submodule.mem_span_finset.1 hzG
  refine ⟨fun g => DirectSum.decompose 𝒜 (c g) 0, ?_⟩
  -- compare homogeneous components of `z = ∑ c_g g`
  have hhom : ∀ g ∈ G, IsHomFrac (𝒜 := 𝒜) n g := fun g hg =>
    isHomFrac_of_chartCond hf (hV g (hGV hg)) hi₀
  let E : Finset ℕ := insert 0 (G.biUnion fun g => (DirectSum.decompose 𝒜 (c g)).support)
  let w : ℕ → FractionRing A := fun e => ∑ g ∈ G, (DirectSum.decompose 𝒜 (c g) e : A) • g
  have hw : ∀ e, IsHomFrac (𝒜 := 𝒜) (n + e) (w e) := by
    intro e
    refine Finset.sum_induction _ (IsHomFrac (𝒜 := 𝒜) (n + e)) (fun _ _ => isHomFrac_add)
      (isHomFrac_zero _) fun g hg => isHomFrac_smul (hhom g hg) (SetLike.coe_mem _)
  have hsumw : ∑ e ∈ E, w e = z := by
    rw [← hcz, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [← Finset.sum_subset (s₁ := (DirectSum.decompose 𝒜 (c g)).support) (s₂ := E),
      DirectSum.sum_support_decompose]
    · intro e he
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨g, hg, he⟩)
    · intro e _ he
      rw [DFinsupp.notMem_support_iff.1 he]
      rfl
  let u : ℕ → FractionRing A := fun m => w (m - n) - if m = n then z else 0
  have hu : ∀ m ∈ E.image (· + n), IsHomFrac (𝒜 := 𝒜) m (u m) := by
    intro m hm
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hm
    have h1 : IsHomFrac (𝒜 := 𝒜) (e + n) (w (e + n - n)) := by
      rw [Nat.add_sub_cancel, add_comm]
      exact hw e
    refine h1.sub ?_
    split_ifs with h
    · rw [h]
      exact isHomFrac_of_chartCond hf (hV z hz) hi₀
    · exact isHomFrac_zero _
  have hsumu : ∑ m ∈ E.image (· + n), u m = 0 := by
    rw [Finset.sum_image fun _ _ _ _ h => Nat.add_right_cancel h]
    simp only [u, Nat.add_sub_cancel, Finset.sum_sub_distrib, hsumw, add_eq_right]
    rw [Finset.sum_ite_eq' E 0 (fun _ => z)]
    simp [E]
  have h0 := eq_zero_of_sum_isHomFrac_eq_zero _ u hu hsumu n
    (Finset.mem_image.2 ⟨0, Finset.mem_insert_self _ _, zero_add n⟩)
  simp only [u, Nat.sub_self, sub_eq_zero] at h0
  exact h0.symm

/-! ### The `S₀`-module of global sections of `𝒪(n)` -/

variable (𝒜) in
/-- The ring map `S₀ → Γ(Proj S, 𝒪)` of the structure morphism `Proj S ⟶ Spec S₀`. -/
def degreeZeroToGlobal : 𝒜 0 →+* Γ(Proj 𝒜, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appTop).hom

/-- The global function coming from `c ∈ S₀` is the constant `c / 1`. -/
theorem degreeZeroToGlobal_val (c : 𝒜 0) (x : Proj 𝒜) :
    ((degreeZeroToGlobal 𝒜 c).1 ⟨x, trivial⟩).val = Localization.mk (c : A) 1 := by
  rw [degreeZeroToGlobal, CommRingCat.hom_comp, RingHom.comp_apply]
  simp only [Proj.toSpecZero, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  erw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv
    (Scheme.Hom.appTop (Spec.map _)), ← Scheme.ΓSpecIso_inv_naturality]
  rw [show Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 1) = _ from Proj.basicOpenToSpec_app_top _ 1]
  simp only [CommRingCat.comp_apply]
  simp only [Scheme.isoOfEq_inv, Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  have h1 : (⊤ : (Proj 𝒜).Opens) ≤ Proj.basicOpen 𝒜 1 := by rw [Proj.basicOpen_one]
  erw [Hartshorne.topIso_inv_appTop_presheaf_map_map h1]
  rw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  change ((((Proj.awayToSection 𝒜 1).hom' _).1 ⟨x, h1 trivial⟩)).val = _
  change (HomogeneousLocalization.mk ⟨0, c, 1, one_mem _⟩).val = _
  rw [HomogeneousLocalization.val_mk]
  rfl

/-! ### The `ℤ`-grading extending the `ℕ`-grading -/

section IntGrading

variable (𝒜) in
/-- The grading of `S` extended by zero to negative degrees, as `ℤ`-submodules (the pieces
`S(0)_d` of `gradedTwist 𝒜 0`). The graded prime filtration is stated for `ℤ`-graded algebras;
this puts `S` in that setting. -/
def intGrading (d : ℤ) : Submodule ℤ A := (gradedTwist 𝒜 0 d).toIntSubmodule

omit [GradedRing 𝒜] in
theorem mem_intGrading_iff {d : ℤ} {a : A} : a ∈ intGrading 𝒜 d ↔ a ∈ gradedTwist 𝒜 0 d :=
  Iff.rfl

omit [GradedRing 𝒜] in
theorem mem_intGrading_natCast {k : ℕ} {a : A} : a ∈ intGrading 𝒜 (k : ℤ) ↔ a ∈ 𝒜 k :=
  mem_gradedTwist_of_eq (by simp)

instance intGrading.gradedMonoid : SetLike.GradedMonoid (intGrading 𝒜) where
  one_mem := (mem_gradedTwist_of_eq (k := 0) (by simp)).2 (SetLike.GradedOne.one_mem (A := 𝒜))
  mul_mem := by
    intro i j a b ha hb
    rw [mem_intGrading_iff] at ha hb ⊢
    by_cases hi : 0 + i < 0
    · rw [eq_zero_of_mem_gradedTwist ha hi, zero_mul]
      exact zero_mem _
    by_cases hj : 0 + j < 0
    · rw [eq_zero_of_mem_gradedTwist hb hj, mul_zero]
      exact zero_mem _
    refine (mem_gradedTwist_of_eq (k := i.toNat + j.toNat) (by omega)).2 ?_
    exact SetLike.GradedMul.mul_mem (by simpa using mem_of_mem_gradedTwist ha)
      (by simpa using mem_of_mem_gradedTwist hb)

omit [GradedRing 𝒜] in
/-- The inclusion `S_k → intGrading 𝒜 k`. -/
private def intGradingIncl (k : ℕ) : 𝒜 k →+ intGrading 𝒜 (k : ℤ) where
  toFun x := ⟨x, mem_intGrading_natCast.2 x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (𝒜) in
private noncomputable def intGradingDecompose : A →+ ⨁ d : ℤ, intGrading 𝒜 d :=
  (DirectSum.toAddMonoid fun k : ℕ =>
    (DirectSum.of (fun d : ℤ => intGrading 𝒜 d) (k : ℤ)).comp (intGradingIncl k)).comp
    (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

private theorem intGradingDecompose_of_mem {k : ℕ} {a : A} (ha : a ∈ 𝒜 k) :
    intGradingDecompose 𝒜 a =
      DirectSum.of (fun d : ℤ => intGrading 𝒜 d) (k : ℤ) ⟨a, mem_intGrading_natCast.2 ha⟩ := by
  classical
  simp only [intGradingDecompose, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, DirectSum.decomposeAddEquiv_apply,
    DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
  rfl

noncomputable instance intGrading.decomposition : DirectSum.Decomposition (intGrading 𝒜) :=
  .ofAddHom (intGrading 𝒜) (intGradingDecompose 𝒜)
    (by
      ext a
      induction a using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | @homogeneous k a =>
        obtain ⟨a, ha⟩ := a
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply,
          intGradingDecompose_of_mem ha, DirectSum.coeAddMonoidHom_of]
      | add a b ha hb =>
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply,
          map_add] at ha hb ⊢
        rw [ha, hb])
    (by
      refine DirectSum.addHom_ext fun d y => ?_
      obtain ⟨y, hy⟩ := y
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      by_cases h : 0 + d < 0
      · obtain rfl := eq_zero_of_mem_gradedTwist (mem_intGrading_iff.1 hy) h
        rw [map_zero]
        exact (map_zero (DirectSum.of (fun d : ℤ => intGrading 𝒜 d) d)).symm
      · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 h)
        obtain rfl : d = (k : ℤ) := by omega
        rw [intGradingDecompose_of_mem (mem_intGrading_natCast.1 hy)])

noncomputable instance intGrading.gradedAlgebra : GradedAlgebra (intGrading 𝒜) where

variable {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]

variable (ℳ : ℤ → σM) in
/-- A `ℤ`-graded module, with its pieces regarded as `ℤ`-submodules. -/
def intModuleGrading (d : ℤ) : Submodule ℤ M where
  carrier := ℳ d
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' n _ hm := zsmul_mem hm n

theorem mem_intModuleGrading_iff {ℳ : ℤ → σM} {d : ℤ} {m : M} :
    m ∈ intModuleGrading ℳ d ↔ m ∈ ℳ d :=
  Iff.rfl

/-- The identity `ℳ d → intModuleGrading ℳ d`. -/
private def intModuleGradingIncl (ℳ : ℤ → σM) (d : ℤ) : ℳ d →+ intModuleGrading ℳ d where
  toFun x := ⟨x, x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance intModuleGrading.decomposition {ℳ : ℤ → σM} [DirectSum.Decomposition ℳ] :
    DirectSum.Decomposition (intModuleGrading ℳ) :=
  .ofAddHom (intModuleGrading ℳ)
    ((DirectSum.map (intModuleGradingIncl ℳ)).comp (DirectSum.decomposeAddEquiv ℳ).toAddMonoidHom)
    (by
      ext m
      induction m using DirectSum.Decomposition.inductionOn ℳ with
      | zero => simp
      | @homogeneous k m =>
        obtain ⟨m, hm⟩ := m
        classical
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply,
          AddEquiv.coe_toAddMonoidHom, DirectSum.decomposeAddEquiv_apply,
          DirectSum.decompose_of_mem ℳ hm, DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
        rfl
      | add a b ha hb =>
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply,
          map_add] at ha hb ⊢
        rw [ha, hb])
    (by
      classical
      refine DirectSum.addHom_ext fun d y => ?_
      obtain ⟨y, hy⟩ := y
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply, AddEquiv.coe_toAddMonoidHom, DirectSum.decomposeAddEquiv_apply,
        DirectSum.decompose_of_mem ℳ (show y ∈ ℳ d from hy), DirectSum.map_of]
      rfl)

instance intModuleGrading.gradedSMul {ℳ : ℤ → σM} [SetLike.GradedSMul 𝒜 ℳ] :
    SetLike.GradedSMul (intGrading 𝒜) (intModuleGrading ℳ) where
  smul_mem := by
    intro i j a m ha hm
    rw [mem_intGrading_iff] at ha
    rw [mem_intModuleGrading_iff] at hm ⊢
    change a • m ∈ ℳ (i + j)
    by_cases hi : 0 + i < 0
    · rw [eq_zero_of_mem_gradedTwist ha hi, zero_smul]
      exact zero_mem _
    · have := smul_mem_graded_nat 𝒜 ℳ (by simpa using mem_of_mem_gradedTwist ha) hm
      rwa [show ((i.toNat : ℕ) : ℤ) + j = i + j by omega] at this

omit [GradedRing 𝒜] in
/-- A module graded over the `ℤ`-extension `intGrading 𝒜` is graded over `𝒜`. -/
theorem gradedSMul_of_intGrading {N σN : Type*} [AddCommGroup N] [Module A N] [SetLike σN N]
    {𝒩 : ℤ → σN} [SetLike.GradedSMul (intGrading 𝒜) 𝒩] : SetLike.GradedSMul 𝒜 𝒩 where
  smul_mem := by
    intro i j a m ha hm
    have := SetLike.GradedSMul.smul_mem (A := intGrading 𝒜) (mem_intGrading_natCast.2 ha) hm
    exact this

end IntGrading

/-! ### Left exactness of global sections of `M~` -/

section LeftExact

variable {M' σM' : Type u} [AddCommGroup M'] [Module A M'] [SetLike σM' M']
  [AddSubgroupClass σM' M'] {ℳ' : ℤ → σM'} [SetLike.GradedSMul 𝒜 ℳ'] [DirectSum.Decomposition ℳ']
  {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
  {ℳ : ℤ → σM} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
  {M'' σM'' : Type u} [AddCommGroup M''] [Module A M''] [SetLike σM'' M'']
  [AddSubgroupClass σM'' M''] {ℳ'' : ℤ → σM''} [SetLike.GradedSMul 𝒜 ℳ'']
  [DirectSum.Decomposition ℳ'']

omit [DirectSum.Decomposition ℳ'] [DirectSum.Decomposition ℳ] in
private theorem gradedLocMap_mk (g : M' →ₗ[A] M) (hg : ∀ (i : ℤ) (m : M'), m ∈ ℳ' i → g m ∈ ℳ i)
    {T : Submonoid A} (k : ℕ) (m : M') (hm : m ∈ ℳ' k) (f : A) (hf : f ∈ 𝒜 k) (hfT : f ∈ T) :
    gradedLocMap g hg T (HomogeneousLocalizedModule.mk k m hm f hf hfT) =
      HomogeneousLocalizedModule.mk k (g m) (hg _ _ hm) f hf hfT :=
  HomogeneousLocalizedModule.ext (IsLocalizedModule.map_LocalizedModules _ _ _ _)

omit [DirectSum.Decomposition ℳ'] [DirectSum.Decomposition ℳ] in
private theorem gradedLocMap_injective (g : M' →ₗ[A] M)
    (hg : ∀ (i : ℤ) (m : M'), m ∈ ℳ' i → g m ∈ ℳ i) (hginj : Function.Injective g)
    (T : Submonoid A) : Function.Injective (gradedLocMap (𝒜 := 𝒜) g hg T) := fun _ _ hyz =>
  HomogeneousLocalizedModule.ext (IsLocalizedModule.map_injective T _ _ g hginj
    (congrArg HomogeneousLocalizedModule.val hyz))

omit [DirectSum.Decomposition ℳ'] in
/-- A graded linear map commutes with taking homogeneous components. -/
private theorem decompose_map (g : M' →ₗ[A] M) (hg : ∀ (i : ℤ) (m : M'), m ∈ ℳ' i → g m ∈ ℳ i)
    [DirectSum.Decomposition ℳ'] (m : M') (j : ℤ) :
    (DirectSum.decompose ℳ (g m) j : M) = g (DirectSum.decompose ℳ' m j) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ' m]
  rw [map_sum, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_eq_single j]
  · exact DirectSum.decompose_of_mem_same ℳ (hg j _ (SetLike.coe_mem _))
  · intro b _ hb
    exact DirectSum.decompose_of_mem_ne ℳ (hg b _ (SetLike.coe_mem _)) hb
  · intro hj
    rw [DFinsupp.notMem_support_iff.1 hj]
    simp

omit [DirectSum.Decomposition ℳ'] [DirectSum.Decomposition ℳ] in
/-- If `c ∉ 𝔭` kills a homogeneous `n`, so does a homogeneous component of `c` outside `𝔭`. -/
private theorem exists_component_smul_eq_zero (x : ProjectiveSpectrum 𝒜) {c : A}
    (hc : c ∉ x.asHomogeneousIdeal) {k : ℤ} {n : M''} (hn : n ∈ ℳ'' k) (hcn : c • n = 0) :
    ∃ e : ℕ, (DirectSum.decompose 𝒜 c e : A) ∉ x.asHomogeneousIdeal ∧
      (DirectSum.decompose 𝒜 c e : A) • n = 0 := by
  classical
  obtain ⟨e, he⟩ : ∃ e : ℕ, (DirectSum.decompose 𝒜 c e : A) ∉ x.asHomogeneousIdeal := by
    by_contra! hall
    apply hc
    rw [← DirectSum.sum_support_decompose 𝒜 c]
    exact sum_mem fun e _ => hall e
  refine ⟨e, he, ?_⟩
  have hmem : ∀ e' : ℕ, (DirectSum.decompose 𝒜 c e' : A) • n ∈ ℳ'' ((e' : ℤ) + k) :=
    fun e' => smul_mem_graded_nat 𝒜 ℳ'' (SetLike.coe_mem _) hn
  have h1 := congrArg (fun z => (DirectSum.decompose ℳ'' z ((e : ℤ) + k) : M'')) hcn
  simp only [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at h1
  rw [← h1]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 c]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
    AddSubmonoidClass.coe_finsetSum]
  by_cases hsupp : e ∈ (DirectSum.decompose 𝒜 c).support
  · rw [Finset.sum_eq_single e]
    · exact (DirectSum.decompose_of_mem_same ℳ'' (hmem e)).symm
    · intro b _ hb
      exact DirectSum.decompose_of_mem_ne ℳ'' (hmem b) (by omega)
    · intro h
      exact absurd hsupp h
  · rw [DFinsupp.notMem_support_iff.1 hsupp, ZeroMemClass.coe_zero, zero_smul]
    refine (Finset.sum_eq_zero fun b hb => ?_).symm
    exact DirectSum.decompose_of_mem_ne ℳ'' (hmem b) (by rintro h; exact hsupp (by
      have : b = e := by omega
      exact this ▸ hb))

variable (g : M' →ₗ[A] M) (hg : ∀ (i : ℤ) (m : M'), m ∈ ℳ' i → g m ∈ ℳ i)
  (q : M →ₗ[A] M'') (hq : ∀ (i : ℤ) (m : M), m ∈ ℳ i → q m ∈ ℳ'' i)

/-- **Left exactness on sections.** If `0 → M' → M → M''` is exact (as graded modules), a section
of `M~` whose image in `M''~` vanishes comes from a section of `M'~`. Locally the section is
`m / f`; then `q(m) / f = 0` gives a homogeneous `c ∉ 𝔭` with `c q(m) = 0`, so `c m = g(m')` and the
section is `m' / c f` near the point. -/
theorem exists_sections_of_gradedLocMap_eq_zero (hginj : Function.Injective g)
    (hexact : ∀ m, q m = 0 → ∃ m', g m' = m) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (s : (sheafInType 𝒜 ℳ).1.obj (op U)) (hs : ∀ x, gradedLocMap q hq _ (s.1 x) = 0) :
    ∃ t : (sheafInType 𝒜 ℳ').1.obj (op U), ∀ x, gradedLocMap g hg _ (t.1 x) = s.1 x := by
  classical
  have hloc : ∀ x : U, ∃ (V : Opens (ProjectiveSpectrum.top 𝒜)) (_ : x.1 ∈ V) (i : V ⟶ U)
      (k : ℕ) (m' : M') (hm' : m' ∈ ℳ' k) (f : A) (hf : f ∈ 𝒜 k)
      (f_nin : ∀ y : V, f ∉ y.1.asHomogeneousIdeal), ∀ y : V,
        gradedLocMap g hg _ (HomogeneousLocalizedModule.mk k m' hm' f hf (f_nin y)) =
          s.1 (i y) := by
    intro x
    obtain ⟨V, hxV, i, k, m, hm, f, hf, f_nin, w⟩ := s.2 x
    beta_reduce at w
    have h0 := hs (i ⟨x.1, hxV⟩)
    rw [w ⟨x.1, hxV⟩, gradedLocMap_mk] at h0
    have h1 := congrArg HomogeneousLocalizedModule.val h0
    rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_zero,
      ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
    obtain ⟨c, hc⟩ := h1
    rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def] at hc
    obtain ⟨e, hce, hce0⟩ := exists_component_smul_eq_zero x.1 c.2 (hq _ _ hm) hc
    set ce := (DirectSum.decompose 𝒜 (c : A) e : A) with hce_def
    have hce_mem : ce ∈ 𝒜 e := SetLike.coe_mem _
    have hqm : q (ce • m) = 0 := by rw [map_smul, hce0]
    obtain ⟨m₁, hm₁⟩ := hexact _ hqm
    have hcm : ce • m ∈ ℳ ((k + e : ℕ) : ℤ) := by
      have := smul_mem_graded_nat 𝒜 ℳ hce_mem hm
      rwa [show (e : ℤ) + k = ((k + e : ℕ) : ℤ) by push_cast; ring] at this
    set m' := (DirectSum.decompose ℳ' m₁ ((k + e : ℕ) : ℤ) : M') with hm'_def
    have hgm' : g m' = ce • m := by
      rw [hm'_def, ← decompose_map g hg, hm₁]
      exact DirectSum.decompose_of_mem_same ℳ hcm
    have hcef : ce * f ∈ 𝒜 (k + e) := by
      have := SetLike.mul_mem_graded hce_mem hf
      rwa [add_comm e k] at this
    refine ⟨V ⊓ ProjectiveSpectrum.basicOpen 𝒜 ce, ⟨hxV, hce⟩, Opens.infLELeft _ _ ≫ i, k + e, m',
      SetLike.coe_mem _, ce * f, hcef, fun y => ?_, fun y => ?_⟩
    · exact y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem y.2.2 (f_nin ⟨y.1, y.2.1⟩)
    · rw [gradedLocMap_mk]
      change _ = s.1 (i ⟨y.1, y.2.1⟩)
      rw [w ⟨y.1, y.2.1⟩]
      apply HomogeneousLocalizedModule.ext
      rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_mk, hgm']
      exact LocalizedModule.mk_cancel_common_left ⟨ce, y.2.2⟩ ⟨f, f_nin ⟨y.1, y.2.1⟩⟩ m
  have hpt : ∀ x : U, ∃ y', gradedLocMap g hg _ y' = s.1 x := by
    intro x
    obtain ⟨V, hxV, i, k, m', hm', f, hf, f_nin, w⟩ := hloc x
    exact ⟨_, w ⟨x.1, hxV⟩⟩
  choose t0 ht0 using hpt
  refine ⟨⟨t0, fun x => ?_⟩, ht0⟩
  obtain ⟨V, hxV, i, k, m', hm', f, hf, f_nin, w⟩ := hloc x
  exact ⟨V, hxV, i, k, m', hm', f, hf, f_nin, fun y =>
    gradedLocMap_injective g hg hginj _ ((ht0 (i y)).trans (w y).symm)⟩

include hg hq in
/-- **Finiteness through a left exact sequence** (Hartshorne's reduction to the factors of a
filtration, "since `A` is Noetherian"). If `0 → M' → M → M''` is an exact sequence of graded
modules, `S₀` is Noetherian, and `Γ(Proj S, M'~)`, `Γ(Proj S, M''~)` are finite `S₀`-modules, then so
is `Γ(Proj S, M~)`. -/
theorem moduleFinite_sections_of_exact [IsNoetherianRing (𝒜 0)] (hginj : Function.Injective g)
    (hexact : ∀ m, q m = 0 → ∃ m', g m' = m)
    [Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 ℳ').val.obj (op ⊤)))]
    [Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 ℳ'').val.obj (op ⊤)))] :
    Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 ℳ).val.obj (op ⊤))) := by
  let G' := ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).map
    ((projGradedModuleSheafMap g hg).val.app (op ⊤))).hom
  let Q := ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).map
    ((projGradedModuleSheafMap q hq).val.app (op ⊤))).hom
  have hker : LinearMap.ker Q ≤ LinearMap.range G' := by
    intro s hs
    rw [LinearMap.mem_ker] at hs
    have hpt : ∀ x, gradedLocMap q hq _
        ((show (sheafInType 𝒜 ℳ).1.obj (op ⊤) from s).1 x) = 0 := fun x =>
      congrArg (fun z : (projGradedModuleSheaf 𝒜 ℳ'').val.obj (op ⊤) =>
        (show (sheafInType 𝒜 ℳ'').1.obj (op ⊤) from z).1 x) hs
    obtain ⟨t, ht⟩ := exists_sections_of_gradedLocMap_eq_zero g hg q hq hginj hexact _ hpt
    exact ⟨t, Subtype.ext (funext ht)⟩
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker Q (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq]
  refine Submodule.FG.of_le ?_ hker
  rw [← Submodule.map_top]
  exact Module.Finite.fg_top.map G'

omit [DirectSum.Decomposition ℳ'] [DirectSum.Decomposition ℳ] in
include hg in
/-- **Finiteness along an injective graded map.** If `g : M' → M` is injective and graded,
`S₀` is Noetherian and `Γ(Proj S, M~)` is a finite `S₀`-module, so is `Γ(Proj S, M'~)`. -/
theorem moduleFinite_sections_of_injective [IsNoetherianRing (𝒜 0)]
    (hginj : Function.Injective g)
    [Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 ℳ).val.obj (op ⊤)))] :
    Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 ℳ').val.obj (op ⊤))) := by
  let G' := ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).map
    ((projGradedModuleSheafMap g hg).val.app (op ⊤))).hom
  refine Module.Finite.of_injective G' fun t t' htt' => ?_
  apply Subtype.ext
  funext x
  exact gradedLocMap_injective g hg hginj _ (congrArg
    (fun z : (projGradedModuleSheaf 𝒜 ℳ).val.obj (op ⊤) =>
      (show (sheafInType 𝒜 ℳ).1.obj (op ⊤) from z).1 x) htt')

end LeftExact

/-! ### Reduction to the factors of a graded prime filtration -/

section Filtration

attribute [local instance] gradedSMul_of_intGrading

variable (𝒜) in
/-- The factor `(S/𝔭)(l)` of a graded prime filtration (Proposition I.7.4), for a prime `𝔭`
homogeneous for the `ℤ`-extension of the grading, as a graded `S`-module. -/
abbrev primeFactor (p : PrimeSpectrum A) (hp : p.1.IsHomogeneous (intGrading 𝒜)) (l : ℤ) :=
  gradedModuleTwist (gradedQuotientPiece (intGrading 𝒜) (intGrading 𝒜)
    (homogeneousIdealSubmodule (intGrading 𝒜) p.1 hp)) l

instance primeFactor.gradedSMul (p : PrimeSpectrum A) (hp : p.1.IsHomogeneous (intGrading 𝒜))
    (l : ℤ) : SetLike.GradedSMul 𝒜 (primeFactor 𝒜 p hp l) :=
  haveI : SetLike.GradedSMul (intGrading 𝒜) (gradedQuotientPiece (intGrading 𝒜) (intGrading 𝒜)
      (homogeneousIdealSubmodule (intGrading 𝒜) p.1 hp)) :=
    gradedQuotientPieceGradedSMul (intGrading 𝒜) (intGrading 𝒜) _
  haveI : SetLike.GradedSMul (intGrading 𝒜) (primeFactor 𝒜 p hp l) :=
    gradedModuleTwistGradedSMul (intGrading 𝒜) _ l
  gradedSMul_of_intGrading

variable {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
  {ℳ : ℤ → σM} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

/-- **Reduction to the prime factors** (Hartshorne's use of Proposition I.7.4 in the proof of
Theorem 5.19). Let `S` be Noetherian and `M` a finitely generated graded `S`-module. If
`Γ(Proj S, (S/𝔭)(l)~)` is a finite `S₀`-module for every homogeneous prime `𝔭` and every `l`,
then so is `Γ(Proj S, M~)`: filter `M` with factors `(S/𝔭)(l)` and use left exactness. -/
theorem moduleFinite_sections_of_primeFactors [IsNoetherianRing A] [IsNoetherianRing (𝒜 0)]
    [Module.Finite A M]
    (hfac : ∀ (p : PrimeSpectrum A) (hp : p.1.IsHomogeneous (intGrading 𝒜)) (l : ℤ),
      Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
        ((projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤)))) :
    Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 ℳ).val.obj (op ⊤))) := by
  classical
  obtain ⟨s, hhead, hlast⟩ := exists_gradedPrimeFiltration (intGrading 𝒜) (intModuleGrading ℳ)
  let P : HomogeneousSubmodule (intGrading 𝒜) (intModuleGrading ℳ) → Prop := fun N =>
    Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜
        (gradedSubmodulePiece (intGrading 𝒜) (intModuleGrading ℳ) N)).val.obj (op ⊤)))
  have hbot : P ⊥ := by
    have : Subsingleton (⊥ : HomogeneousSubmodule (intGrading 𝒜) (intModuleGrading ℳ)) :=
      ⟨fun a b => Subtype.ext (((Submodule.mem_bot A).1 a.2).trans
        ((Submodule.mem_bot A).1 b.2).symm)⟩
    have : ∀ T : Submonoid A, Subsingleton (LocalizedModule T
        (⊥ : HomogeneousSubmodule (intGrading 𝒜) (intModuleGrading ℳ))) := fun T =>
      ⟨fun a b => by
        induction a using LocalizedModule.induction_on with | h m t =>
        induction b using LocalizedModule.induction_on with | h m' t' =>
        rw [Subsingleton.elim m 0, Subsingleton.elim m' 0, LocalizedModule.zero_mk,
          LocalizedModule.zero_mk]⟩
    have : Subsingleton ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
        ((projGradedModuleSheaf 𝒜
          (gradedSubmodulePiece (intGrading 𝒜) (intModuleGrading ℳ) ⊥)).val.obj (op ⊤))) :=
      ⟨fun t t' => globalValue_injective 𝒜 _ (funext fun x =>
        HomogeneousLocalizedModule.ext (Subsingleton.elim _ _))⟩
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  have hstep : ∀ N₁ N₂, IsGradedPrimeFiltrationStep (intGrading 𝒜) (intModuleGrading ℳ) N₁ N₂ →
      P N₁ → P N₂ := by
    rintro N₁ N₂ ⟨h, p, hp, l, ⟨e⟩⟩ hN₁
    have := hfac p hp l
    have : Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
        ((projGradedModuleSheaf 𝒜
          (gradedSubmodulePiece (intGrading 𝒜) (intModuleGrading ℳ) N₁)).val.obj (op ⊤))) := hN₁
    let g : N₁ →ₗ[A] N₂ :=
      { toFun := fun m => ⟨m.1, h m.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let q := e.toLinearEquiv.symm.toLinearMap ∘ₗ (gradedSubmoduleOf _ _ N₁ N₂ h).toSubmodule.mkQ
    refine moduleFinite_sections_of_exact (ℳ' := gradedSubmodulePiece _ _ N₁)
      (ℳ := gradedSubmodulePiece _ _ N₂) (ℳ'' := primeFactor 𝒜 p hp l) g
      (fun _ _ hm => hm) q (fun i m hm => ?_)
      (fun a b hab => Subtype.ext (congrArg (fun z : N₂ => (z : M)) hab)) (fun m hm => ?_)
    · obtain ⟨x, hx, hxe⟩ := (Set.ext_iff.1 (e.map_piece i)
        ((gradedSubmoduleOf _ _ N₁ N₂ h).toSubmodule.mkQ m)).2 ⟨m, hm, rfl⟩
      change e.toLinearEquiv.symm _ ∈ _
      rw [← hxe]
      simpa using hx
    · have hm' : (gradedSubmoduleOf _ _ N₁ N₂ h).toSubmodule.mkQ m = 0 :=
        e.toLinearEquiv.symm.injective (hm.trans (map_zero _).symm)
      have hmem : m ∈ (gradedSubmoduleOf _ _ N₁ N₂ h).toSubmodule :=
        (Submodule.Quotient.mk_eq_zero (gradedSubmoduleOf _ _ N₁ N₂ h).toSubmodule).1 hm'
      exact ⟨⟨m.1, hmem⟩, rfl⟩
  have hall : ∀ i, P (s i) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      change P s.head
      rw [hhead]
      exact hbot
    | succ i ih => exact hstep _ _ (s.step i) ih
  have htop : P ⊤ := hlast ▸ hall (Fin.last _)
  have : Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜
        (gradedSubmodulePiece (intGrading 𝒜) (intModuleGrading ℳ) ⊤)).val.obj (op ⊤))) := htop
  let ι : M →ₗ[A] (⊤ : HomogeneousSubmodule (intGrading 𝒜) (intModuleGrading ℳ)) :=
    { toFun := fun m => ⟨m, show m ∈ (⊤ : Submodule A M) from Submodule.mem_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact moduleFinite_sections_of_injective (ℳ' := ℳ)
    (ℳ := gradedSubmodulePiece (intGrading 𝒜) (intModuleGrading ℳ) ⊤) ι (fun _ _ hm => hm)
    (fun a b hab => congrArg Subtype.val hab)

end Filtration

variable [IsDomain A]

/-- Multiplication by the constant `c ∈ S₀` multiplies values in `K` by `c`. -/
theorem sectionValue_degreeZeroToGlobal_smul (n : ℤ) (c : 𝒜 0)
    (g : (projTwistingSheaf 𝒜 n).val.obj (op ⊤)) (x : Proj 𝒜) :
    sectionValue n (degreeZeroToGlobal 𝒜 c • g) x =
      algebraMap A (FractionRing A) c * sectionValue n g x := by
  unfold sectionValue
  change toFraction x (((degreeZeroToGlobal 𝒜 c).1 ⟨x, trivial⟩ •
    globalValue 𝒜 (gradedTwist 𝒜 n) g x).val) = _
  rw [HomogeneousLocalizedModule.val_smul, degreeZeroToGlobal_val, toFraction_mk_smul]
  simp

/-- On a chart `D₊(f)` with `f ∈ S₁` nonzero, the value in `K` of a global section of `𝒪(n)` is
`a / f^j` with `a ∈ S(n)_j`. -/
private theorem exists_mem_gradedTwist_eq_pow_mul {f : A} (f_deg : f ∈ 𝒜 1) (hf : f ≠ 0) (n : ℤ)
    (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) (g : (projTwistingSheaf 𝒜 n).val.obj (op ⊤)) :
    ∃ (j : ℕ) (a : A), a ∈ gradedTwist 𝒜 n j ∧ algebraMap A (FractionRing A) a =
      algebraMap A (FractionRing A) f ^ j * sectionValue n g (genericPoint h) := by
  obtain ⟨m, hm⟩ := exists_globalValue_eq_mapOfLE 𝒜 (gradedTwist 𝒜 n) f_deg one_pos g
  have hη : genericPoint h ∈ Proj.basicOpen 𝒜 f := by
    rw [Proj.mem_basicOpen]
    intro hmem
    have h0 : f ∈ (⊥ : HomogeneousIdeal 𝒜).toIdeal := hmem
    rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h0
    exact hf h0
  obtain ⟨d, a, ha, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective m
  obtain ⟨j, rfl⟩ := hsx
  have hfj : f ^ j ≠ 0 := pow_ne_zero j hf
  have hdj : d = j := DirectSum.degree_eq_of_mem_mem 𝒜 hs
    (by simpa using SetLike.pow_mem_graded j f_deg) hfj
  subst hdj
  refine ⟨d, a, ha, ?_⟩
  unfold sectionValue
  rw [hm _ hη, HomogeneousLocalizedModule.mapOfLE_mk, HomogeneousLocalizedModule.val_mk,
    toFraction_mk]
  have := (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hfj
  simp only [map_pow] at this ⊢
  field_simp

/-- The value in `K` of a global section of `𝒪(n)`, multiplied by `f_{i₀}^m` where
`n + m = d ≥ 0`, satisfies the chart condition in degree `d`. -/
theorem chartCond_pow_mul_sectionValue {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1)
    (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) {n : ℤ} {m d : ℕ} (hnmd : n + m = d) (i₀ : ι)
    (g : (projTwistingSheaf 𝒜 n).val.obj (op ⊤)) :
    ChartCond 𝒜 f d
      (algebraMap A (FractionRing A) (f i₀) ^ m * sectionValue n g (genericPoint h)) := by
  intro i hi
  obtain ⟨j, a, ha, hza⟩ := exists_mem_gradedTwist_eq_pow_mul (hf i) hi n h g
  by_cases hneg : n + j < 0
  · refine ⟨0, 0, zero_mem _, ?_⟩
    rw [ha.2 hneg, map_zero] at hza
    have hfi : algebraMap A (FractionRing A) (f i) ^ j ≠ 0 :=
      pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hi)
    rw [(mul_eq_zero.1 hza.symm).resolve_left hfi]
    simp
  · refine ⟨j, a * f i₀ ^ m, ?_, ?_⟩
    · have h1 : a ∈ 𝒜 (n + j).toNat := ha.1
      have := SetLike.mul_mem_graded h1 (by simpa using SetLike.pow_mem_graded m (hf i₀))
      rwa [show (n + j).toNat + m = j + d by omega] at this
    · rw [map_mul, hza, map_pow]
      ring

omit [IsDomain A] in
/-- If `S₊ ≠ 0`, some generator `fᵢ` is nonzero. -/
private theorem exists_ne_zero_of_not_irrelevant_le {f : ι → A}
    (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤)
    (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥) : ∃ i, f i ≠ 0 := by
  by_contra! h0
  apply h
  intro a ha
  have hbot : Algebra.adjoin (𝒜 0) (Set.range f) = ⊥ := by
    rw [eq_bot_iff, Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    rw [h0 i]
    exact zero_mem _
  have hmem : a ∈ (⊥ : Subalgebra (𝒜 0) A) := by
    rw [← hbot, hgen]
    exact Algebra.mem_top
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hmem
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha
  change (algebraMap (𝒜 0) A c) ∈ (⊥ : HomogeneousIdeal 𝒜).toIdeal
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]
  change (c : A) = 0
  rw [← DirectSum.decompose_of_mem_same 𝒜 c.2]
  exact ha

/-- **Hartshorne II, Theorem 5.19, the integral case** (the last step of Hartshorne's proof). Let
`S` be a graded domain, finitely generated as an algebra over a field `k`, and generated over `S₀`
by finitely many elements `fᵢ` of degree one. Then for every `n ∈ ℤ`, `Γ(Proj S, 𝒪(n))` is a
finitely generated `S₀`-module, through the structure morphism `Proj S ⟶ Spec S₀`. -/
theorem moduleFinite_projTwistingSheaf_of_isDomain (k : Type u) [Field k] [Algebra k A]
    [Algebra.FiniteType k A] [Fintype ι] {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) (n : ℤ) :
    Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projTwistingSheaf 𝒜 n).val.obj (op ⊤))) := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  by_cases h : HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥
  · -- `Proj S` is empty
    have hempty : IsEmpty (Proj 𝒜) :=
      ⟨fun x => (show ProjectiveSpectrum 𝒜 from x).not_irrelevant_le (h.trans bot_le)⟩
    have : Subsingleton ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
        ((projTwistingSheaf 𝒜 n).val.obj (op ⊤))) :=
      ⟨fun g g' => globalValue_injective 𝒜 (gradedTwist 𝒜 n) (funext fun x => hempty.elim x)⟩
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  obtain ⟨i₀, hi₀⟩ := exists_ne_zero_of_not_irrelevant_le hgen h
  have hfin : Module.Finite A (integralClosure A (FractionRing A)) :=
    moduleFinite_integralClosure_of_finiteType_of_field k A (FractionRing A) (FractionRing A)
  let η := genericPoint h
  -- multiply by `u = f_{i₀}^m` to reach a degree `d ≥ 0`
  obtain ⟨m, d, hnmd⟩ : ∃ m d : ℕ, n + m = d := ⟨(-n).toNat, (n + (-n).toNat).toNat, by omega⟩
  set u := algebraMap A (FractionRing A) (f i₀) ^ m
  have hu : u ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hi₀)
  let sv : (projTwistingSheaf 𝒜 n).val.obj (op ⊤) →+ FractionRing A :=
    AddMonoidHom.mk' (fun g => sectionValue n g η) fun g g' => sectionValue_add _ g g' η
  let sv' := (AddMonoidHom.mulLeft u).comp sv
  obtain ⟨G, hGV, hG⟩ := exists_finset_of_chartCond hfin hf hgen ⟨i₀, hi₀⟩ d (Set.range sv')
    (by rintro _ ⟨g, rfl⟩; exact chartCond_pow_mul_sectionValue hf h hnmd i₀ g)
  have hpre : ∀ v ∈ G, ∃ g, sv' g = v := fun v hv => hGV hv
  choose! pre hpre using hpre
  let pre' : FractionRing A → (ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projTwistingSheaf 𝒜 n).val.obj (op ⊤)) := pre
  refine ⟨⟨G.image pre', ?_⟩⟩
  rw [eq_top_iff]
  rintro g -
  obtain ⟨c, hc⟩ := hG (sv' g) ⟨g, rfl⟩
  have key : (show (projTwistingSheaf 𝒜 n).val.obj (op ⊤) from g) =
      ∑ v ∈ G, degreeZeroToGlobal 𝒜 (c v) • pre v := by
    rw [← sub_eq_zero]
    apply eq_zero_of_sectionValue_eq_zero h
    refine (mul_eq_zero.1 (?_ : sv' (_ - _) = 0)).resolve_left hu
    rw [map_sub, map_sum, sub_eq_zero, hc]
    refine Finset.sum_congr rfl fun v hv => ?_
    change _ = u * sectionValue n (degreeZeroToGlobal 𝒜 (c v) • pre v) η
    have e : u * sectionValue n (pre v) η = v := hpre v hv
    rw [sectionValue_degreeZeroToGlobal_smul, Algebra.smul_def, mul_left_comm, e]
  change g = ∑ v ∈ G, c v • pre' v at key
  rw [key]
  exact sum_mem fun v hv => Submodule.smul_mem _ _
    (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hv)))

end ProjectiveGlobalSectionsFinite

end Hartshorne
