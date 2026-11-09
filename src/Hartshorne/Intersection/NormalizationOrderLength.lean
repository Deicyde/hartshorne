/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Localization.Integer

/-!
# Orders via the normalization are lengths

Let `A` be a one-dimensional Noetherian local domain with fraction field `K` whose integral
closure `B` in `K` is a finite `A`-module. Then `B` is a semilocal Dedekind domain, its
localizations at maximal ideals are discrete valuation rings, and for `a ≠ 0` in `A`
`ℓ_A(A/aA) = ∑_𝔪 ord_{B_𝔪}(a) [κ(𝔪) : κ]`.
-/

universe u

open IsLocalRing

namespace Hartshorne.NormalizationOrderLength

section Lengths

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The image of `A` in `B`, as an `A`-submodule. -/
abbrev baseSubmodule (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] : Submodule A B :=
  LinearMap.range (Algebra.linearMap A B)

/-- If `B / A` has finite length, then `ℓ_A(A/aA) = ℓ_A(B/aB)` for a nonzero `a`. This is the
snake lemma for multiplication by `a` on `0 → A → B → B/A → 0`, in the form of the two
filtrations `aA ⊆ A ⊆ B` and `aA ⊆ aB ⊆ B`. -/
theorem length_quotient_span_eq_length_quotient_span_algebraMap [IsDomain B]
    [FaithfulSMul A B] {a : A} (ha : a ≠ 0)
    (hfin : Module.length A (B ⧸ baseSubmodule A B) ≠ ⊤) :
    Module.length A (A ⧸ Ideal.span {a}) =
      Module.length A (B ⧸ Ideal.span {algebraMap A B a}) := by
  set N1 := baseSubmodule A B
  set N0 : Submodule A B := Submodule.span A {algebraMap A B a}
  have hinj := FaithfulSMul.algebraMap_injective A B
  have ha' : algebraMap A B a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have h01 : N0 ≤ N1 := Submodule.span_le.mpr (by simp [N1])
  -- the sequence `0 → A/aA → B/aA → B/A → 0`
  have hfα : Ideal.span {a} ≤ N0.comap (Algebra.linearMap A B) := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact Submodule.mem_span_singleton.mpr ⟨c, by simp [Algebra.smul_def]⟩
  let f : A ⧸ Ideal.span {a} →ₗ[A] B ⧸ N0 := Submodule.mapQ _ _ (Algebra.linearMap A B) hfα
  let g : B ⧸ N0 →ₗ[A] B ⧸ N1 := Submodule.factor h01
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
    refine ⟨c, hinj ?_⟩
    rw [map_mul, ← Algebra.smul_def, hc]
    rfl
  have hg : Function.Surjective g := Submodule.factor_surjective h01
  have hfg : Function.Exact f g := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change (Submodule.Quotient.mk y : B ⧸ N1) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
      have h' : y = Algebra.linearMap A B x - (Algebra.linearMap A B x - y) := by abel
      rw [h']
      exact N1.sub_mem ⟨x, rfl⟩ (h01 hx)
  -- the sequence `0 → B/A → B/aA → B/aB → 0`, the first map being multiplication by `a`
  have hfβ : N1 ≤ N0.comap (LinearMap.mulLeft A (algebraMap A B a)) := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨x, by simp [Algebra.smul_def, mul_comm]⟩
  let f' : B ⧸ N1 →ₗ[A] B ⧸ N0 := Submodule.mapQ _ _ _ hfβ
  have hg'0 : N0 ≤ LinearMap.ker
      (Ideal.Quotient.mkₐ A (Ideal.span {algebraMap A B a})).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ rfl
    change Ideal.Quotient.mk _ (algebraMap A B a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let g' : B ⧸ N0 →ₗ[A] B ⧸ Ideal.span {algebraMap A B a} :=
    N0.liftQ (Ideal.Quotient.mkₐ A _).toLinearMap hg'0
  have hf' : Function.Injective f' := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    refine ⟨c, mul_left_cancel₀ ha' ?_⟩
    rw [LinearMap.mulLeft_apply] at hc
    rw [← hc]
    simp [Algebra.smul_def, mul_comm]
  have hg' : Function.Surjective g' := by
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have hfg' : Function.Exact f' g' := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [g', Submodule.liftQ_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Set.mem_range]
    constructor
    · intro hy
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      refine ⟨Submodule.Quotient.mk b, ?_⟩
      rw [Submodule.mapQ_apply, LinearMap.mulLeft_apply, mul_comm]
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq, LinearMap.mulLeft_apply] at hx
      have h1 : algebraMap A B a * x - y ∈ Ideal.span {algebraMap A B a} := by
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
        rw [← hc, Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      have h2 : algebraMap A B a * x ∈ Ideal.span {algebraMap A B a} :=
        Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have h' : y = algebraMap A B a * x - (algebraMap A B a * x - y) := by abel
      rw [h']
      exact Ideal.sub_mem _ h2 h1
  have hα := Module.length_eq_add_of_exact f g hf hg hfg
  have hβ := Module.length_eq_add_of_exact f' g' hf' hg' hfg'
  rw [hα, add_comm] at hβ
  exact WithTop.add_left_cancel hfin hβ

open scoped Pointwise in
/-- Length over `A` is additive along products: `ℓ_A(B/cbB) = ℓ_A(B/bB) + ℓ_A(B/cB)`. -/
theorem length_quotient_span_mul [IsDomain B] (b : B) {c : B} (hc : c ≠ 0) :
    Module.length A (B ⧸ Ideal.span {c * b}) =
      Module.length A (B ⧸ Ideal.span {b}) + Module.length A (B ⧸ Ideal.span {c}) := by
  have hc' : c ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hc
  have := Module.length_eq_add_of_exact ((Ideal.mulQuot c (Ideal.span {b})).restrictScalars A)
    ((Ideal.quotOfMul c (Ideal.span {b})).restrictScalars A)
    (Ideal.mulQuot_injective (Ideal.span {b}) hc') (Ideal.quotOfMul_surjective (Ideal.span {b}))
    (Ideal.exact_mulQuot_quotOfMul (Ideal.span {b}))
  have lem : c • Ideal.span {b} = Ideal.span {c * b} := by
    rw [← Submodule.singleton_set_smul]
    simp [← Ideal.submodule_span_eq, Submodule.set_smul_span]
  rw [lem] at this
  exact this

theorem length_quotient_span_unit {u : B} (hu : IsUnit u) :
    Module.length A (B ⧸ Ideal.span {u}) = 0 := by
  rw [Ideal.span_singleton_eq_top.mpr hu]
  exact Module.length_eq_zero

/-- A finitely generated module killed by a nonzero element of a one-dimensional Noetherian
domain has finite length; applied to `B / A`. -/
theorem length_quotient_baseSubmodule_ne_top [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Module.Finite A B] {d : A} (hd : d ≠ 0)
    (h : ∀ b : B, d • b ∈ baseSubmodule A B) :
    Module.length A (B ⧸ baseSubmodule A B) ≠ ⊤ := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
  set N1 := baseSubmodule A B
  have hker : ∀ i, Ideal.span {d} ≤
      LinearMap.ker (LinearMap.toSpanSingleton A (B ⧸ N1) (Submodule.Quotient.mk (s i))) := by
    intro i x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, mul_smul,
      ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero N1).mpr (h (s i)), smul_zero]
  let φ : (Fin n → A ⧸ Ideal.span {d}) →ₗ[A] B ⧸ N1 :=
    ∑ i, (Submodule.liftQ _ _ (hker i)) ∘ₗ LinearMap.proj i
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy : y ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hy
    refine ⟨fun i ↦ Submodule.Quotient.mk (c i), ?_⟩
    rw [← hc, ← Submodule.mkQ_apply, map_sum]
    simp only [φ, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul]
    rfl
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective φ hφ)
  rw [Module.length_pi_of_fintype]
  have hd' : d ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hd
  have := isFiniteLength_quotient_span_singleton A hd'
  rw [← Module.length_ne_top_iff] at this
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp this
  rw [← hk, ← Nat.cast_sum]
  exact ENat.natCast_ne_top _

end Lengths


variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

local notation "𝓑" => integralClosure A K

omit [IsNoetherianRing A] [IsLocalRing A] in
theorem isFractionRing_integralClosure : IsFractionRing 𝓑 K :=
  integralClosure.isFractionRing_of_finite_extension (A := A) K K

attribute [local instance] isFractionRing_integralClosure

omit [IsNoetherianRing A] [IsLocalRing A] in
theorem dimensionLEOne_of_ringKrullDim_eq_one (hA : ringKrullDim A = 1) :
    Ring.DimensionLEOne A := by
  have : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, hA]
    simp
  exact ⟨fun hne hp ↦ hp.isMaximal_of_ne_bot hne⟩

theorem isDedekindDomain_integralClosure (hA : ringKrullDim A = 1) [Module.Finite A 𝓑] :
    IsDedekindDomain 𝓑 := by
  have : IsNoetherianRing 𝓑 := IsNoetherianRing.of_finite A 𝓑
  have := dimensionLEOne_of_ringKrullDim_eq_one hA
  refine (isDedekindDomain_iff 𝓑 K).mpr ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro x hx
  have hx' : IsIntegral A x := isIntegral_trans x hx
  exact ⟨⟨x, hx'⟩, rfl⟩

omit [IsDomain A] [IsNoetherianRing A] [IsFractionRing A K] in
theorem finite_setOf_isMaximal_integralClosure [Module.Finite A 𝓑] :
    {m : Ideal 𝓑 | m.IsMaximal}.Finite := by
  refine (Algebra.QuasiFinite.finite_primesOver (maximalIdeal A) (S := 𝓑)).subset ?_
  intro m (hm : m.IsMaximal)
  refine ⟨hm.isPrime, ⟨?_⟩⟩
  have : (m.comap (algebraMap A 𝓑)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  exact (IsLocalRing.eq_maximalIdeal this).symm

omit [IsDomain A] [IsNoetherianRing A] [IsFractionRing A K] in
/-- The maximal ideals of `B` lie over the maximal ideal of `A`. -/
theorem comap_eq_maximalIdeal (m : Ideal 𝓑) [m.IsMaximal] :
    m.comap (algebraMap A 𝓑) = maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)

omit [IsNoetherianRing A] in
theorem ne_bot_of_isMaximal (hA : ringKrullDim A = 1) (m : Ideal 𝓑) [m.IsMaximal] : m ≠ ⊥ := by
  intro h
  have h1 := comap_eq_maximalIdeal K m
  rw [h, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A 𝓑)] at h1
  have : IsField A := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h1.symm
  have h0 := ringKrullDim_eq_zero_of_isField this
  rw [hA] at h0
  exact absurd h0 (by decide)

theorem isDiscreteValuationRing_localization (hA : ringKrullDim A = 1) [Module.Finite A 𝓑]
    (m : Ideal 𝓑) [m.IsMaximal] : IsDiscreteValuationRing (Localization.AtPrime m) := by
  have := isDedekindDomain_integralClosure K hA
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain 𝓑
    (ne_bot_of_isMaximal K hA m) _

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- Some nonzero `d ∈ A` satisfies `dB ⊆ A`. -/
theorem exists_smul_mem_baseSubmodule [Module.Finite A 𝓑] :
    ∃ d : A, d ≠ 0 ∧ ∀ b : 𝓑, d • b ∈ baseSubmodule A 𝓑 := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := 𝓑)
  obtain ⟨⟨d, hd⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors A) Finset.univ (fun i ↦ (s i : K))
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun b ↦ ?_⟩
  have hle : Submodule.span A (Set.range s) ≤
      (baseSubmodule A 𝓑).comap (d • LinearMap.id) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hint i (Finset.mem_univ i)
    refine ⟨x, Subtype.ext ?_⟩
    simpa using hx
  exact hle (hs ▸ Submodule.mem_top : b ∈ Submodule.span A (Set.range s))

omit [IsDomain A] [IsNoetherianRing A] [IsFractionRing A K] in
/-- For a maximal ideal `𝔪` of `B`, `ℓ_A(B/𝔪) = [κ(𝔪) : κ]`. -/
theorem length_quotient_isMaximal [Module.Finite A 𝓑] (m : Ideal 𝓑) [m.IsMaximal] :
    Module.length A (𝓑 ⧸ m) = m.inertiaDeg A := by
  have : m.LiesOver (maximalIdeal A) := ⟨(comap_eq_maximalIdeal K m).symm⟩
  let := Ideal.Quotient.field (maximalIdeal A)
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) m,
    Module.length_eq_of_surjective (R := A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]

/-- For a prime element `p` of `B`, `ℓ_A(B/pB) = ∑_𝔪 ord_{B_𝔪}(p) [κ(𝔪) : κ]`: only `𝔪 = pB`
contributes, with order one. -/
theorem length_quotient_span_prime (hA : ringKrullDim A = 1) [Module.Finite A 𝓑]
    [Fintype (MaximalSpectrum 𝓑)] {p : 𝓑} (hp : Prime p) :
    Module.length A (𝓑 ⧸ Ideal.span {p}) =
      ∑ m : MaximalSpectrum 𝓑, Ring.ord (Localization.AtPrime m.asIdeal)
        (algebraMap 𝓑 _ p) * (m.asIdeal.inertiaDeg A : ℕ∞) := by
  have := isDedekindDomain_integralClosure K hA
  have hmax : (Ideal.span {p}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  let M0 : MaximalSpectrum 𝓑 := ⟨Ideal.span {p}, hmax⟩
  rw [Finset.sum_eq_single M0]
  · have := isDiscreteValuationRing_localization K hA M0.asIdeal
    have hirr : Irreducible (algebraMap 𝓑 (Localization.AtPrime M0.asIdeal) p) := by
      rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
        ← Localization.AtPrime.map_eq_maximalIdeal]
      change Ideal.map _ (Ideal.span {p}) = _
      rw [Ideal.map_span, Set.image_singleton]
    rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_uniformizer hirr, one_mul]
    exact length_quotient_isMaximal K M0.asIdeal
  · intro m _ hm
    have hpm : p ∉ m.asIdeal := by
      intro h
      apply hm
      refine MaximalSpectrum.ext (hmax.eq_of_le m.isMaximal.ne_top ?_).symm
      exact (Ideal.span_singleton_le_iff_mem _).mpr h
    have hu : IsUnit (algebraMap 𝓑 (Localization.AtPrime m.asIdeal) p) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ m.asIdeal p).mpr hpm
    rw [Ring.ord_of_isUnit hu, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ M0) h

/-- **Orders via the normalization are lengths.** Let `A` be a one-dimensional Noetherian local
domain with fraction field `K` whose integral closure `B` in `K` is a finite `A`-module. For
every nonzero `a ∈ A`, `ℓ_A(A/aA) = ∑_𝔪 ord_{B_𝔪}(a) [κ(𝔪) : κ]`, the sum running over the
(finitely many) maximal ideals `𝔪` of `B`. -/
theorem length_quotient_eq_finsum_ord_mul_inertiaDeg (hA : ringKrullDim A = 1)
    [Module.Finite A 𝓑] {a : A} (ha : a ≠ 0) :
    Module.length A (A ⧸ Ideal.span {a}) =
      ∑ᶠ m : MaximalSpectrum 𝓑, Ring.ord (Localization.AtPrime m.asIdeal)
        (algebraMap 𝓑 _ (algebraMap A 𝓑 a)) * (m.asIdeal.inertiaDeg A : ℕ∞) := by
  have := isDedekindDomain_integralClosure K hA
  have hfinmax := finite_setOf_isMaximal_integralClosure K (A := A)
  have : IsPrincipalIdealRing 𝓑 := IsPrincipalIdealRing.of_finite_maximals hfinmax
  have : Finite (MaximalSpectrum 𝓑) := by
    have := hfinmax.to_subtype
    exact Finite.of_injective (fun m : MaximalSpectrum 𝓑 ↦
      (⟨m.asIdeal, m.isMaximal⟩ : {m : Ideal 𝓑 | m.IsMaximal}))
      fun m m' h ↦ MaximalSpectrum.ext (congrArg Subtype.val h)
  let := Fintype.ofFinite (MaximalSpectrum 𝓑)
  have : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, hA]
    simp
  rw [finsum_eq_sum_of_fintype]
  obtain ⟨d, hd, hdB⟩ := exists_smul_mem_baseSubmodule K (A := A)
  rw [length_quotient_span_eq_length_quotient_span_algebraMap ha
    (length_quotient_baseSubmodule_ne_top hd hdB)]
  have ha' : algebraMap A 𝓑 a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A 𝓑)).mpr ha
  generalize algebraMap A 𝓑 a = b at ha' ⊢
  induction b using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl ha'
  | h₂ x hx =>
    rw [length_quotient_span_unit hx]
    symm
    refine Finset.sum_eq_zero fun m _ ↦ ?_
    rw [Ring.ord_of_isUnit (hx.map _), zero_mul]
  | h₃ b p hb hp ih =>
    rw [length_quotient_span_mul b hp.ne_zero, ih hb, length_quotient_span_prime K hA hp,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    have hinj : Function.Injective (algebraMap 𝓑 (Localization.AtPrime m.asIdeal)) :=
      IsLocalization.injective _ m.asIdeal.primeCompl_le_nonZeroDivisors
    have hp' : algebraMap 𝓑 (Localization.AtPrime m.asIdeal) p ∈ nonZeroDivisors _ :=
      mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr hp.ne_zero)
    rw [map_mul, Ring.ord_mul' _ hp', add_mul, add_comm]

end Hartshorne.NormalizationOrderLength
