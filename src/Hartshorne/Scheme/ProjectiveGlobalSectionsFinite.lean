/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSectionRingIntegralClosure
import Hartshorne.Scheme.FiniteIntegralClosureField
import Hartshorne.Scheme.TopIsoRestriction

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
