/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSectionRingIntegralClosure
import Hartshorne.Scheme.FiniteIntegralClosureField
import Hartshorne.Scheme.TopIsoRestriction
import Hartshorne.Intersection.GradedPrimeFiltration
import Hartshorne.Scheme.ProjGammaStarReconstruction

/-!
# Finiteness of projective global sections on `Proj S`

Hartshorne, *Algebraic Geometry*, II, Theorem 5.19 (pp. 122–123), for the sheaf `M~` of a
finitely generated graded module on `Proj S`.

Let `S` be a graded ring which is a finite-type algebra over a field `k` and is generated over
`S₀` by finitely many elements `f₁, …, f_m` of degree one, and let `M` be a finitely generated
graded `S`-module. Then `Γ(Proj S, M~)` is a finitely generated `S₀`-module
(`moduleFinite_sections_of_finite`). The `S₀`-module structure is restriction of scalars along
`degreeZeroToGlobal`, the ring map `S₀ → Γ(Proj S, 𝒪)` of `Proj S ⟶ Spec S₀`.

## Proof

Following Hartshorne.

* **Filtration** (`moduleFinite_sections_of_primeFactors`). By Proposition I.7.4
  (`exists_gradedPrimeFiltration`, stated for `ℤ`-graded algebras, applied through the
  `ℤ`-extension `intGrading` of the grading) `M` has a filtration by graded submodules with
  factors `(S/𝔭)(l)` (`primeFactor`), `𝔭` a homogeneous prime. Global sections of `M~` are left
  exact (`exists_sections_of_gradedLocMap_eq_zero`: a section of `M~` locally `m / f` with image
  `0` in `M''~` is locally `m' / c f` with `g(m') = c m`), so finiteness passes along the
  filtration since `S₀` is Noetherian (`moduleFinite_sections_of_exact`,
  `moduleFinite_sections_of_injective`).
* **The factors** (`moduleFinite_sections_primeFactor`). If `S₊ ⊆ 𝔭` the sheaf `(S/𝔭)(l)~`
  vanishes. Otherwise `𝔭` is a point of `Proj S`, and a global section is determined by its value
  in the fraction field `K` of the domain `S/𝔭` at that point. On each chart `D₊(fᵢ)` it is a single
  fraction `aᵢ / fᵢ^{jᵢ}` with `aᵢ ∈ (S/𝔭)_{jᵢ + l}`: the value satisfies the chart condition
  `ChartCond`. Such a `z` multiplies the nonzero finitely generated ideal `(S/𝔭)_{≥ ∑ jᵢ}` into
  itself (`exists_mem_mul_of_le`), so it is integral over `S/𝔭` (`isIntegral_of_chartCond`).
  The integral closure of `S/𝔭` in `K` is a finite module (Theorem I.3.9A,
  `moduleFinite_integralClosure_of_finiteType_of_field`), so the span of all such values is
  finitely generated, by finitely many of them; comparing homogeneous components of a relation
  `z = ∑ cᵢ zᵢ` replaces each `cᵢ` by its degree-zero part (`exists_finset_of_chartCond`).
  Negative twists are handled by multiplying by a power of a generator outside `𝔭`.

The same argument gives the integral case on `Proj S` itself for `𝒪(n)`
(`moduleFinite_projTwistingSheaf_of_isDomain`).
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

omit [DirectSum.Decomposition ℳ'] in
/-- **Surjectivity on global sections from the charts.** Let `g : M' → M` be injective and
graded, and let the charts `D₊(fᵢ)`, `fᵢ ∈ S₁`, cover `Proj S`. If every `M'_(fᵢ) → M_(fᵢ)` is
surjective, every global section of `M~` comes from a global section of `M'~`: on `D₊(fᵢ)` it is
a single fraction, which lifts to `M'_(fᵢ)`, and the lifts agree pointwise by injectivity. -/
theorem exists_sections_of_surjective_charts {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1)
    (hcov : ∀ x : Proj 𝒜, ∃ i, f i ∉ x.asHomogeneousIdeal) (hginj : Function.Injective g)
    (hsurj : ∀ i, Function.Surjective (gradedLocMap (𝒜 := 𝒜) g hg (Submonoid.powers (f i))))
    (t : (projGradedModuleSheaf 𝒜 ℳ).val.obj (op ⊤)) :
    ∃ s : (sheafInType 𝒜 ℳ').1.obj (op ⊤), ∀ x, gradedLocMap g hg _ (s.1 x) =
      globalValue 𝒜 ℳ t x.1 := by
  classical
  have hloc : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒜)), ∃ (i : ι) (k : ℕ) (m : M')
      (hm : m ∈ ℳ' k) (j : ℕ) (hj : f i ^ j ∈ 𝒜 k), f i ∉ x.1.asHomogeneousIdeal ∧
      ∀ (y : Proj 𝒜) (hy : f i ∉ y.asHomogeneousIdeal),
        gradedLocMap g hg _ (HomogeneousLocalizedModule.mk k m hm (f i ^ j) hj
          (show f i ^ j ∈ y.asHomogeneousIdeal.toIdeal.primeCompl from
            fun hmem => hy (y.isPrime.mem_of_pow_mem _ hmem))) = globalValue 𝒜 ℳ t y := by
    intro x
    obtain ⟨i, hi⟩ := hcov x.1
    obtain ⟨n, hn⟩ := exists_globalValue_eq_mapOfLE 𝒜 ℳ (hf i) one_pos t
    obtain ⟨m', hm'⟩ := hsurj i n
    obtain ⟨k, m, hm, s0, hs0, hs0T, rfl⟩ := HomogeneousLocalizedModule.mk_surjective m'
    obtain ⟨j, rfl⟩ := hs0T
    refine ⟨i, k, m, hm, j, hs0, hi, fun y hy => ?_⟩
    rw [hn y hy, ← hm', gradedLocMap_mk, gradedLocMap_mk, HomogeneousLocalizedModule.mapOfLE_mk]
  have hpt : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒜)), ∃ y',
      gradedLocMap g hg _ y' = globalValue 𝒜 ℳ t x.1 := by
    intro x
    obtain ⟨i, k, m, hm, j, hj, hi, w⟩ := hloc x
    exact ⟨_, w x.1 hi⟩
  choose s0 hs0 using hpt
  refine ⟨⟨s0, fun x => ?_⟩, hs0⟩
  obtain ⟨i, k, m, hm, j, hj, hi, w⟩ := hloc x
  refine ⟨ProjectiveSpectrum.basicOpen 𝒜 (f i), hi, homOfLE le_top, k, m, hm, f i ^ j, hj,
    fun y hmem => y.2 (y.1.isPrime.mem_of_pow_mem _ hmem), fun y => ?_⟩
  exact gradedLocMap_injective g hg hginj _ ((hs0 _).trans (w y.1 y.2).symm)

omit [DirectSum.Decomposition ℳ'] in
include hg in
/-- **Finiteness from the charts.** Under the hypotheses of `exists_sections_of_surjective_charts`,
if `Γ(Proj S, M'~)` is a finite `S₀`-module, so is `Γ(Proj S, M~)`. -/
theorem moduleFinite_sections_of_surjective_charts {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1)
    (hcov : ∀ x : Proj 𝒜, ∃ i, f i ∉ x.asHomogeneousIdeal) (hginj : Function.Injective g)
    (hsurj : ∀ i, Function.Surjective (gradedLocMap (𝒜 := 𝒜) g hg (Submonoid.powers (f i))))
    [Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 ℳ').val.obj (op ⊤)))] :
    Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 ℳ).val.obj (op ⊤))) := by
  let G' := ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).map
    ((projGradedModuleSheafMap g hg).val.app (op ⊤))).hom
  refine Module.Finite.of_surjective G' fun t => ?_
  obtain ⟨s, hs⟩ := exists_sections_of_surjective_charts g hg hf hcov hginj hsurj t
  exact ⟨s, globalValue_injective 𝒜 ℳ (funext fun x => hs ⟨x, trivial⟩)⟩

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

/-! ### The prime factors `(S/𝔭)(l)` -/

section PrimeFactor

attribute [local instance] gradedSMul_of_intGrading

/-- The `𝒜`-component of `r` in degree `k` is its `intGrading 𝒜`-component. -/
private theorem coe_decompose_intGrading (r : A) (k : ℕ) :
    (DirectSum.decompose (intGrading 𝒜) r (k : ℤ) : A) = DirectSum.decompose 𝒜 r k := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 r]
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_eq_single k]
  · exact DirectSum.decompose_of_mem_same _ (mem_intGrading_natCast.2 (SetLike.coe_mem _))
  · intro b _ hb
    exact DirectSum.decompose_of_mem_ne _ (mem_intGrading_natCast.2 (SetLike.coe_mem _))
      (by exact_mod_cast hb)
  · intro hk
    rw [DFinsupp.notMem_support_iff.1 hk]
    simp

private theorem isHomogeneous_of_intGrading {I : Ideal A}
    (hI : I.IsHomogeneous (intGrading 𝒜)) : I.IsHomogeneous 𝒜 := fun k r hr => by
  rw [← coe_decompose_intGrading]
  exact hI (k : ℤ) hr

/-- `a / s ↦ a / s̄ ∈ Frac(S/𝔭)`, for denominators outside `𝔭`. -/
private def toFracQ (I : Ideal A) [I.IsPrime] {T : Submonoid A} (hT : T ≤ I.primeCompl)
    (m : LocalizedModule T (A ⧸ I)) : FractionRing (A ⧸ I) :=
  m.liftOn (fun q => algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) q.1 /
      algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) (Ideal.Quotient.mk I q.2)) (by
    rintro ⟨a, s⟩ ⟨b, t⟩ ⟨w, hw⟩
    have hne : ∀ u : T, algebraMap (A ⧸ I) (FractionRing (A ⧸ I))
        (Ideal.Quotient.mk I u) ≠ 0 := fun u => by
      rw [map_ne_zero_iff _ (IsFractionRing.injective _ _), ne_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hT u.2
    simp only [Submonoid.smul_def] at hw
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def] at hw
    simp only [Ideal.Quotient.algebraMap_eq] at hw
    have h := congrArg (algebraMap (A ⧸ I) (FractionRing (A ⧸ I))) hw
    simp only [map_mul] at h
    change algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) a /
        algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) (Ideal.Quotient.mk I s) =
      algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) b /
        algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) (Ideal.Quotient.mk I t)
    rw [div_eq_div_iff (hne s) (hne t)]
    have := mul_left_cancel₀ (hne w) h
    linear_combination this)

private theorem toFracQ_mk (I : Ideal A) [I.IsPrime] {T : Submonoid A} (hT : T ≤ I.primeCompl) (a : A ⧸ I) (s : T) :
    toFracQ I hT (LocalizedModule.mk a s) =
      algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) a /
        algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) (Ideal.Quotient.mk I s) :=
  LocalizedModule.liftOn_mk _ _ _

private theorem toFracQ_add (I : Ideal A) [I.IsPrime] {T : Submonoid A} (hT : T ≤ I.primeCompl)
    (m m' : LocalizedModule T (A ⧸ I)) : toFracQ I hT (m + m') = toFracQ I hT m + toFracQ I hT m' := by
  induction m using LocalizedModule.induction_on with | h a s =>
  induction m' using LocalizedModule.induction_on with | h b t =>
  have hne : ∀ u : T, algebraMap (A ⧸ I) (FractionRing (A ⧸ I))
      (Ideal.Quotient.mk I u) ≠ 0 := fun u => by
    rw [map_ne_zero_iff _ (IsFractionRing.injective _ _), ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hT u.2
  have hs := hne s
  have ht := hne t
  rw [LocalizedModule.mk_add_mk, toFracQ_mk, toFracQ_mk, toFracQ_mk]
  simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Submonoid.coe_mul,
    map_add, map_mul]
  field_simp

private theorem toFracQ_mk_smul (I : Ideal A) [I.IsPrime] {T : Submonoid A} (hT : T ≤ I.primeCompl) (c : A)
    (m : LocalizedModule T (A ⧸ I)) :
    toFracQ I hT ((Localization.mk c 1 : Localization T) • m) =
      algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) (Ideal.Quotient.mk I c) * toFracQ I hT m := by
  induction m using LocalizedModule.induction_on with | h b t =>
  rw [LocalizedModule.mk_smul_mk, toFracQ_mk, toFracQ_mk, one_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, map_mul, mul_div_assoc]

variable (p : PrimeSpectrum A) (hp : p.1.IsHomogeneous (intGrading 𝒜))

variable (𝒜) in
/-- The prime `𝔭` as a homogeneous ideal of `S`. -/
private def primeIdeal : HomogeneousIdeal 𝒜 := ⟨p.1, isHomogeneous_of_intGrading hp⟩

/-- The point `𝔭` of `Proj S`, when `S₊ ⊄ 𝔭`. -/
private def primePoint (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ primeIdeal 𝒜 p hp) : Proj 𝒜 :=
  (⟨primeIdeal 𝒜 p hp, p.isPrime, h⟩ : ProjectiveSpectrum 𝒜)

private instance primeIdeal_isPrime : (primeIdeal 𝒜 p hp).toIdeal.IsPrime := p.isPrime

/-- Away from `V₊(𝔭)` the sheaf `(S/𝔭)(l)~` vanishes: an element `a ∈ 𝔭` outside the point
kills every fraction. -/
private theorem globalValue_val_eq_zero (l : ℤ) (x : Proj 𝒜) {a : A} (hap : a ∈ p.1)
    (hax : a ∉ x.asHomogeneousIdeal)
    (s : (projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤)) :
    (globalValue 𝒜 (primeFactor 𝒜 p hp l) s x).val = 0 := by
  generalize (globalValue 𝒜 (primeFactor 𝒜 p hp l) s x).val = y
  induction y using LocalizedModule.induction_on with | h m t =>
  rw [← LocalizedModule.mk_cancel_common_left ⟨a, hax⟩ t m]
  have ham : a • m = 0 := by
    induction m using Submodule.Quotient.induction_on with | H b =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact p.1.mul_mem_right b hap
  rw [Submonoid.smul_def]
  change LocalizedModule.mk (a • m) _ = 0
  rw [ham, LocalizedModule.zero_mk]

variable (l : ℤ) (h : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ primeIdeal 𝒜 p hp)

/-- The value in `Frac(S/𝔭)` at the point `𝔭` of a global section of `(S/𝔭)(l)~`. -/
private def primeValue (s : (projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤)) :
    FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) :=
  toFracQ (primeIdeal 𝒜 p hp).toIdeal le_rfl (globalValue 𝒜 (primeFactor 𝒜 p hp l) s (primePoint p hp h)).val

private theorem primeValue_add (s s' : (projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤)) :
    primeValue p hp l h (s + s') = primeValue p hp l h s + primeValue p hp l h s' :=
  toFracQ_add _ le_rfl _ _

private theorem primeValue_smul (c : 𝒜 0)
    (s : (projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤)) :
    primeValue p hp l h (degreeZeroToGlobal 𝒜 c • s) =
      algebraMap (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal)) (Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal c) *
        primeValue p hp l h s := by
  unfold primeValue
  change toFracQ (primeIdeal 𝒜 p hp).toIdeal le_rfl (((degreeZeroToGlobal 𝒜 c).1 ⟨primePoint p hp h, trivial⟩ •
    globalValue 𝒜 (primeFactor 𝒜 p hp l) s (primePoint p hp h)).val) = _
  rw [HomogeneousLocalizedModule.val_smul, degreeZeroToGlobal_val]
  erw [toFracQ_mk_smul]

private theorem eq_zero_of_primeValue_eq_zero
    {s : (projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤)}
    (hs : primeValue p hp l h s = 0) : s = 0 := by
  apply globalValue_injective 𝒜 (primeFactor 𝒜 p hp l)
  funext x
  apply HomogeneousLocalizedModule.ext
  change (globalValue 𝒜 (primeFactor 𝒜 p hp l) s x).val = 0
  let s' : (sheafInType 𝒜 (primeFactor 𝒜 p hp l)).1.obj (op ⊤) := s
  by_cases hpx : p.1 ≤ x.asHomogeneousIdeal.toIdeal
  · obtain ⟨V, hxV, i, d, m, hm, f, hf, f_nin, w⟩ := s'.2 ⟨x, trivial⟩
    beta_reduce at w
    have hηV : (primePoint p hp h : ProjectiveSpectrum 𝒜) ∈ V := by
      have hcl : x ∈ closure ({(primePoint p hp h : ProjectiveSpectrum 𝒜)} :
          Set (ProjectiveSpectrum 𝒜)) :=
        (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := 𝒜) _ x).1 hpx
      obtain ⟨y, hyV, hy⟩ := mem_closure_iff.1 hcl (show Set (ProjectiveSpectrum 𝒜) from V.1)
        V.2 hxV
      rw [Set.mem_singleton_iff.1 hy] at hyV
      exact hyV
    have e1 := congrArg HomogeneousLocalizedModule.val (w ⟨x, hxV⟩)
    have e2 := congrArg HomogeneousLocalizedModule.val (w ⟨_, hηV⟩)
    unfold primeValue at hs
    change toFracQ (primeIdeal 𝒜 p hp).toIdeal le_rfl (s'.1 (i ⟨_, hηV⟩)).val = 0 at hs
    rw [e2, HomogeneousLocalizedModule.val_mk] at hs
    erw [toFracQ_mk] at hs
    rw [div_eq_zero_iff] at hs
    have hm0 : m = 0 := by
      rcases hs with hs | hs
      · exact (map_eq_zero_iff (algebraMap (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal)))
          (IsFractionRing.injective (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal)))).1 hs
      · exfalso
        rw [map_eq_zero_iff (algebraMap (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal)))
          (IsFractionRing.injective (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal))),
          Ideal.Quotient.eq_zero_iff_mem] at hs
        exact f_nin ⟨_, hηV⟩ hs
    change (s'.1 (i ⟨x, hxV⟩)).val = 0
    rw [e1, HomogeneousLocalizedModule.val_mk]
    subst hm0
    exact LocalizedModule.zero_mk _
  · obtain ⟨a, hap, hax⟩ := Set.not_subset.1 hpx
    exact globalValue_val_eq_zero p hp l x hap hax s


/-- On a chart `D₊(f)` with `f ∈ S₁`, `f ∉ 𝔭`, the value of a section of `(S/𝔭)(l)~` is
`ā / f̄^j` with `a ∈ S_{j + l}` (zero if `j + l < 0`). -/
private theorem exists_primeValue_chart {f : A} (f_deg : f ∈ 𝒜 1) (hf : f ∉ p.1)
    (s : (projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤)) :
    ∃ (j : ℕ) (a : A), a ∈ intGrading 𝒜 (j + l) ∧
      algebraMap (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal))
          (Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal a) =
        algebraMap (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal))
          (Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal f) ^ j * primeValue p hp l h s := by
  obtain ⟨m, hm⟩ := exists_globalValue_eq_mapOfLE 𝒜 (primeFactor 𝒜 p hp l) f_deg one_pos s
  have hη : primePoint p hp h ∈ Proj.basicOpen 𝒜 f := hf
  obtain ⟨d, a', ha', t, ht, htx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective m
  obtain ⟨j, rfl⟩ := htx
  have hfj : f ^ j ∉ p.1 := fun hmem => hf (p.isPrime.mem_of_pow_mem _ hmem)
  have hdj : d = j := DirectSum.degree_eq_of_mem_mem 𝒜 ht
    (by simpa using SetLike.pow_mem_graded j f_deg) (fun h0 => hfj (by
      simp only at h0
      rw [h0]
      exact zero_mem _))
  subst hdj
  obtain ⟨a, ha, rfl⟩ := ha'
  refine ⟨d, a, ha, ?_⟩
  unfold primeValue
  rw [hm _ hη, HomogeneousLocalizedModule.mapOfLE_mk, HomogeneousLocalizedModule.val_mk]
  erw [toFracQ_mk]
  have h0 : algebraMap (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal))
      (Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (f ^ d)) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective _ _), ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hfj
  rw [map_pow, map_pow] at h0 ⊢
  field_simp
  rfl

/-- The value of a section of `(S/𝔭)(l)~`, multiplied by `f̄_{i₀}^m` with `l + m = d ≥ 0`,
satisfies the chart condition in degree `d` for `S/𝔭` and the images of the `fᵢ`. -/
private theorem chartCond_primeValue {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1) {m d : ℕ}
    (hlmd : l + m = d) (i₀ : ι)
    (s : (projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤)) :
    ChartCond (gradedQuotient 𝒜 (primeIdeal 𝒜 p hp))
      (fun i => Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (f i)) d
      (algebraMap (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal))
        (Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (f i₀)) ^ m * primeValue p hp l h s) := by
  intro i hi
  have hfi : f i ∉ p.1 := fun hmem => hi (Ideal.Quotient.eq_zero_iff_mem.2 hmem)
  obtain ⟨j, a, ha, hza⟩ := exists_primeValue_chart p hp l h (hf i) hfi s
  have hne : algebraMap (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal))
      (Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (f i)) ^ j ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hi)
  by_cases hneg : 0 + ((j : ℤ) + l) < 0
  · refine ⟨0, 0, zero_mem _, ?_⟩
    rw [eq_zero_of_mem_gradedTwist ha hneg, map_zero, map_zero] at hza
    rw [(mul_eq_zero.1 hza.symm).resolve_left hne]
    simp
  · refine ⟨j, Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (a * f i₀ ^ m), ?_, ?_⟩
    · apply mk_mem_gradedQuotient
      have h1 : a ∈ 𝒜 (0 + ((j : ℤ) + l)).toNat := mem_of_mem_gradedTwist ha
      have := SetLike.mul_mem_graded h1 (by simpa using SetLike.pow_mem_graded m (hf i₀))
      rwa [show (0 + ((j : ℤ) + l)).toNat + m = j + d by omega] at this
    · rw [map_mul, map_mul, hza, map_pow, map_pow]
      ring

end PrimeFactor

section PrimeFactorFinite

attribute [local instance] gradedSMul_of_intGrading

variable (p : PrimeSpectrum A) (hp : p.1.IsHomogeneous (intGrading 𝒜))

/-- **Hartshorne II, Theorem 5.19, for the factor `(S/𝔭)(l)`** (the last step of Hartshorne's
proof: `(S/𝔭)(l)~` is `𝒪_Y(l)` on the integral closed subscheme `Y = V₊(𝔭)`). Let `S` be a
finite-type algebra over a field `k`, generated over `S₀` by finitely many `fᵢ ∈ S₁`, and `𝔭` a
homogeneous prime. Then `Γ(Proj S, (S/𝔭)(l)~)` is a finite `S₀`-module for every `l ∈ ℤ`. -/
theorem moduleFinite_sections_primeFactor (k : Type u) [Field k] [Algebra k A]
    [Algebra.FiniteType k A] [Fintype ι] {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) (l : ℤ) :
    Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤))) := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hcov : ∀ x : Proj 𝒜, ∃ i, f i ∉ x.asHomogeneousIdeal := by
    intro x
    have hx : x ∈ (⊤ : (Proj 𝒜).Opens) := trivial
    rw [← Proj.iSup_basicOpen_eq_top' 𝒜 f (fun i => ⟨1, hf i⟩) hgen] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨i, hi⟩
  by_cases h : HomogeneousIdeal.irrelevant 𝒜 ≤ primeIdeal 𝒜 p hp
  · -- `S₊ ⊆ 𝔭`: the sheaf vanishes
    have : Subsingleton ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤))) := ⟨fun s s' => globalValue_injective 𝒜 _ (funext fun x => by
      obtain ⟨i, hi⟩ := hcov x
      have hfi : f i ∈ p.1 := h (by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
          DirectSum.decompose_of_mem_ne 𝒜 (hf i) (by omega)])
      exact HomogeneousLocalizedModule.ext ((globalValue_val_eq_zero p hp l x hfi hi s).trans
        (globalValue_val_eq_zero p hp l x hfi hi s').symm))⟩
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  have : Algebra.FiniteType k (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k (primeIdeal 𝒜 p hp).toIdeal)
      (Ideal.Quotient.mkₐ_surjective k (primeIdeal 𝒜 p hp).toIdeal)
  have hfb : ∀ i, Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (f i) ∈ gradedQuotient 𝒜 (primeIdeal 𝒜 p hp) 1 :=
    fun i => mk_mem_gradedQuotient (hf i)
  have hgenb : Algebra.adjoin (gradedQuotient 𝒜 (primeIdeal 𝒜 p hp) 0)
      (Set.range fun i => Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (f i)) = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
    have ha : a ∈ Algebra.adjoin (𝒜 0) (Set.range f) := hgen ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap c =>
      exact Subalgebra.algebraMap_mem _
        (⟨Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal c, mk_mem_gradedQuotient c.2⟩ :
          gradedQuotient 𝒜 (primeIdeal 𝒜 p hp) 0)
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
  obtain ⟨i₀, hi₀⟩ : ∃ i, f i ∉ p.1 := hcov (primePoint p hp h)
  have hfb0 : Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (f i₀) ≠ 0 := fun h0 => hi₀ (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hfin : Module.Finite (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (integralClosure (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal))) :=
    moduleFinite_integralClosure_of_finiteType_of_field k (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal)) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal))
  obtain ⟨m, d, hlmd⟩ : ∃ m d : ℕ, l + m = d := ⟨(-l).toNat, (l + (-l).toNat).toNat, by omega⟩
  set u := algebraMap (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) (FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal)) (Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (f i₀)) ^ m
  have hu : u ≠ 0 := pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hfb0)
  let sv : (projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤) →+ FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) :=
    AddMonoidHom.mk' (primeValue p hp l h) (primeValue_add p hp l h)
  let sv' := (AddMonoidHom.mulLeft u).comp sv
  obtain ⟨G, hGV, hG⟩ := exists_finset_of_chartCond hfin hfb hgenb ⟨i₀, hfb0⟩ d (Set.range sv')
    (by rintro _ ⟨g, rfl⟩; exact chartCond_primeValue p hp l h hf hlmd i₀ g)
  have hpre : ∀ v ∈ G, ∃ g, sv' g = v := fun v hv => hGV hv
  choose! pre hpre using hpre
  let pre' : FractionRing (A ⧸ (primeIdeal 𝒜 p hp).toIdeal) → ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤))) := pre
  refine ⟨⟨G.image pre', ?_⟩⟩
  rw [eq_top_iff]
  rintro g -
  obtain ⟨c, hc⟩ := hG (sv' g) ⟨g, rfl⟩
  have hlift : ∀ v, ∃ c' : 𝒜 0, Ideal.Quotient.mk (primeIdeal 𝒜 p hp).toIdeal (c' : A) = (c v : (A ⧸ (primeIdeal 𝒜 p hp).toIdeal)) := fun v => by
    obtain ⟨a, ha, hae⟩ := mem_gradedQuotient_iff.1 (c v).2
    exact ⟨⟨a, ha⟩, hae⟩
  choose c' hc' using hlift
  have key : (show (projGradedModuleSheaf 𝒜 (primeFactor 𝒜 p hp l)).val.obj (op ⊤) from g) =
      ∑ v ∈ G, degreeZeroToGlobal 𝒜 (c' v) • pre v := by
    rw [← sub_eq_zero]
    apply eq_zero_of_primeValue_eq_zero p hp l h
    refine (mul_eq_zero.1 (?_ : sv' (_ - _) = 0)).resolve_left hu
    rw [map_sub, map_sum, sub_eq_zero, hc]
    refine Finset.sum_congr rfl fun v hv => ?_
    have e : u * primeValue p hp l h (pre v) = v := hpre v hv
    change _ = u * primeValue p hp l h (degreeZeroToGlobal 𝒜 (c' v) • pre v)
    rw [primeValue_smul, hc' v, mul_left_comm, e, Algebra.smul_def]
  change g = ∑ v ∈ G, c' v • pre' v at key
  rw [key]
  exact sum_mem fun v hv => Submodule.smul_mem _ _
    (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hv)))

/-- **Hartshorne II, Theorem 5.19, for `M~`.** Let `S` be a graded ring which is a finite-type
algebra over a field `k`, generated over `S₀` by finitely many elements `fᵢ` of degree one, and let
`M` be a finitely generated graded `S`-module. Then `Γ(Proj S, M~)` is a finite `S₀`-module.
Following Hartshorne: filter `M` with factors `(S/𝔭)(l)` (Proposition I.7.4), use left exactness
of global sections, and treat each factor by integrality over `S/𝔭`. -/
theorem moduleFinite_sections_of_finite (k : Type u) [Field k] [Algebra k A]
    [Algebra.FiniteType k A] [Fintype ι] {f : ι → A} (hf : ∀ i, f i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤)
    {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
    {ℳ : ℤ → σM} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] [Module.Finite A M] :
    Module.Finite (𝒜 0) ((ModuleCat.restrictScalars (degreeZeroToGlobal 𝒜)).obj
      ((projGradedModuleSheaf 𝒜 ℳ).val.obj (op ⊤))) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing (𝒜 0) :=
    isNoetherianRing_of_surjective A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜)
      fun a => ⟨a, GradedRing.projZeroRingHom'_apply_coe 𝒜 a⟩
  exact moduleFinite_sections_of_primeFactors fun p hp l =>
    moduleFinite_sections_primeFactor p hp k hf hgen l

end PrimeFactorFinite

section IntegralCase

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

end IntegralCase

/-! ### Homogeneous spans -/

section HomogeneousSpan

variable {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
  {ℳ : ℤ → σM} [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

/-- The component of `a • m` in degree `i`, for `m` homogeneous of degree `d`, is
`a_{i - d} • m`. -/
private theorem coe_decompose_smul_of_mem (a : A) {d : ℤ} {m : M} (hm : m ∈ intModuleGrading ℳ d)
    (i : ℤ) : (DirectSum.decompose (intModuleGrading ℳ) (a • m) i : M) =
      (DirectSum.decompose (intGrading 𝒜) a (i - d) : A) • m := by
  classical
  have hmem : ∀ e : ℤ, (DirectSum.decompose (intGrading 𝒜) a e : A) • m ∈
      intModuleGrading ℳ (e + d) := fun e =>
    SetLike.GradedSMul.smul_mem (A := intGrading 𝒜) (SetLike.coe_mem _) hm
  conv_lhs => rw [← DirectSum.sum_support_decompose (intGrading 𝒜) a]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
    AddSubmonoidClass.coe_finsetSum]
  by_cases hsupp : i - d ∈ (DirectSum.decompose (intGrading 𝒜) a).support
  · rw [Finset.sum_eq_single (i - d)]
    · have := hmem (i - d)
      rw [sub_add_cancel] at this
      exact DirectSum.decompose_of_mem_same _ this
    · intro b _ hb
      exact DirectSum.decompose_of_mem_ne _ (hmem b) (by omega)
    · intro h
      exact absurd hsupp h
  · rw [DFinsupp.notMem_support_iff.1 hsupp, ZeroMemClass.coe_zero, zero_smul]
    refine Finset.sum_eq_zero fun b hb => ?_
    exact DirectSum.decompose_of_mem_ne _ (hmem b) (by rintro h; exact hsupp (by
      have : b = i - d := by omega
      exact this ▸ hb))

variable (𝒜) in
/-- The homogeneous submodule spanned by a set of homogeneous elements. -/
def homogeneousSpan (S : Set M) (hS : ∀ m ∈ S, ∃ d, m ∈ intModuleGrading ℳ d) :
    HomogeneousSubmodule (intGrading 𝒜) (intModuleGrading ℳ) where
  toSubmodule := Submodule.span A S
  is_homogeneous' := by
    classical
    intro i m hm
    induction hm using Submodule.span_induction generalizing i with
    | mem x hx =>
      obtain ⟨d, hd⟩ := hS x hx
      by_cases hid : i = d
      · subst hid
        rw [DirectSum.decompose_of_mem_same _ hd]
        exact Submodule.subset_span hx
      · rw [DirectSum.decompose_of_mem_ne _ hd (Ne.symm hid)]
        exact zero_mem _
    | zero => simp
    | add x y _ _ hx hy =>
      rw [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      exact add_mem (hx i) (hy i)
    | smul a x _ hx =>
      rw [← DirectSum.sum_support_decompose (intModuleGrading ℳ) x, Finset.smul_sum,
        DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
      refine sum_mem fun j _ => ?_
      rw [coe_decompose_smul_of_mem (𝒜 := 𝒜) a (SetLike.coe_mem _) i]
      exact Submodule.smul_mem _ _ (hx j)

end HomogeneousSpan

/-! ### Coherent sheaves on `Proj S` -/

section Coherent

open GammaStarReconstruction GradedGlobalSections

set_option backward.isDefEq.respectTransparency false in
/-- If the sections of `M~` over `D₊(f)` are a finite module, so is `M_(f)` over `S_(f)` (the
converse of `ProjGradedModuleSheaf.finite_sections_basicOpen`). -/
theorem finite_away_of_finite_sections {M σM : Type u} [AddCommGroup M] [Module A M]
    [SetLike σM M] [AddSubgroupClass σM M] {ℳ : ℤ → σM} [SetLike.GradedSMul 𝒜 ℳ]
    [DirectSum.Decomposition ℳ] {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d)
    (h : Module.Finite Γ(Proj 𝒜, Proj.basicOpen 𝒜 f)
      Γ(projGradedModuleSheaf 𝒜 ℳ, Proj.basicOpen 𝒜 f)) :
    Module.Finite (Away 𝒜 f) (HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f)) := by
  have hD : (Proj.awayι 𝒜 f f_deg hd) ''ᵁ ⊤ = Proj.basicOpen 𝒜 f :=
    (Scheme.Hom.image_top_eq_opensRange _).trans (Proj.opensRange_awayι 𝒜 f f_deg hd)
  have h₃ := (CoherentAux.finite_congr_opens (projGradedModuleSheaf 𝒜 ℳ) hD).2 h
  have h₂ := (CoherentAux.finite_restrict_iff (Proj.awayι 𝒜 f f_deg hd)
    (projGradedModuleSheaf 𝒜 ℳ) ⊤).2 h₃
  let _ : Module Γ(Spec (.of (Away 𝒜 f)), ⊤) (chartSections 𝒜 ℳ f_deg hd ⊤) :=
    inferInstanceAs (Module Γ(Spec (.of (Away 𝒜 f)), ⊤)
      Γ(chartModule 𝒜 ℳ f_deg hd, ⊤))
  have h₁ : Module.Finite (Away 𝒜 f) (chartSections 𝒜 ℳ f_deg hd ⊤) := by
    refine (CoherentAux.finite_iff_of_ringEquiv (N := chartSections 𝒜 ℳ f_deg hd ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).symm.commRingCatIsoToRingEquiv
      (fun a n => ?_)).2 h₂
    have : (⊤ : (Spec (.of (Away 𝒜 f))).Opens).leTop = 𝟙 ⊤ := Subsingleton.elim _ _
    change ((Spec (.of (Away 𝒜 f))).presheaf.map (⊤ : (Spec (.of (Away 𝒜 f))).Opens).leTop.op
      ((Scheme.ΓSpecIso _).inv a)) • n = _
    rw [this, op_id, CategoryTheory.Functor.map_id]
    rfl
  exact Module.Finite.equiv (awayModuleIsoChartSections 𝒜 ℳ f_deg hd).symm.toLinearEquiv

variable (F : (Proj 𝒜).Modules)

/-- `Γ(X, F(n)) → Γ_*(F)_n`. -/
private def gammaStarGradingIncl (n : ℤ) : twistGlobal F n →+ gammaStarGrading F n where
  toFun y := ⟨DirectSum.of _ n y, y, rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- `Γ_*(F) = ⨁ₙ Γ(X, F(n))` is decomposed by its summands. -/
noncomputable instance gammaStarGrading.decomposition :
    DirectSum.Decomposition (gammaStarGrading F) :=
  .ofAddHom (gammaStarGrading F) (DirectSum.map (gammaStarGradingIncl F))
    (by
      classical
      refine DirectSum.addHom_ext fun n y => ?_
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.map_of,
        DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
      rfl)
    (by
      classical
      refine DirectSum.addHom_ext fun n z => ?_
      obtain ⟨_, y, rfl⟩ := z
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      change DirectSum.map (gammaStarGradingIncl F) (DirectSum.of _ n y) = _
      rw [DirectSum.map_of]
      rfl)

end Coherent

end ProjectiveGlobalSectionsFinite

end Hartshorne
