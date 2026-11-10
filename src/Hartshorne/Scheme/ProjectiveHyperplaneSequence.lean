/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjTwistPullback
import Hartshorne.Scheme.ProjSurjectionClosedImmersion
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The degreewise hyperplane sequence on projective space

Hartshorne, *Algebraic Geometry*, III.5, proof of Theorem 5.1(b) (p. 227).

Let `x ∈ S_1` and let `f : S → T` be a surjective graded ring map with `f(x) = 0` and kernel `(x)`,
with `x` a non-zero-divisor. Multiplication by `x` is a map of graded modules `S(n-1) → S(n)`,
giving `𝒪(n-1) ⟶ 𝒪(n)` (`mulSection`). With the restriction
`𝒪_{Proj S}(n) ⟶ f_*(𝒪_{Proj T}(n)|_U)` of the partial Proj morphism (`ProjTwistPullback.psi`),
this gives a short exact sequence `0 → 𝒪(n-1) → 𝒪(n) → f_* 𝒪_{Proj T}(n) → 0` (`shortExact`):

* `mono_mulSection`: `x` is a non-zero-divisor on the fibers;
* `isLimitMulSection`: a section killed by `psi` is, near a point `p`, a fraction `m / g` with
  `u m ∈ (x)` for some homogeneous `u ∉ p` (`exists_local_preimage`);
* `epi_psi`: `psi` is locally surjective, by lifting local fractions on `Proj T`.

For `X = ℙ^{m+1}_A = Proj A[x_0, …, x_{m+1}]` and `H = V₊(x_{m+1})`, `hyperplaneHom` is the
surjective graded map `A[x_0, …, x_{m+1}] → A[x_0, …, x_m]` with `x_{m+1} ↦ 0`. Its partial Proj
morphism `i : ℙ^m_A ⟶ X` is defined on all of `ℙ^m_A` and is a closed immersion. The sequence
`0 → 𝒪_X(n-1) → 𝒪_X(n) → i_* 𝒪_H(n) → 0` is short exact (`hyperplane_shortExact`).

The graded form `⊕_n` and the statement about the induced cohomology map under the graded Čech
identifications are not treated here.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne.HyperplaneSequence

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
  ProjGradedModuleSheaf ProjTwistMap

section General

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
theorem mem_of_map_mem (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (p : ProjectiveSpectrum 𝒜)
    (hp : ∀ a, f a = 0 → a ∈ p.asHomogeneousIdeal) {a : A}
    (h : f a ∈ p.asHomogeneousIdeal.toIdeal.map f) : a ∈ p.asHomogeneousIdeal := by
  have : a ∈ (p.asHomogeneousIdeal.toIdeal.map f).comap f := h
  rw [Ideal.comap_map_of_surjective _ hf, sup_eq_left.2 fun b hb => hp b (by simpa using hb)]
    at this
  exact this

/-- The point of `Proj T` over a point `p ⊇ ker f` of `Proj S`, for `f` surjective. -/
def liftPoint (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (p : ProjectiveSpectrum 𝒜)
    (hp : ∀ a, f a = 0 → a ∈ p.asHomogeneousIdeal) : ProjectiveSpectrum ℬ where
  asHomogeneousIdeal := p.asHomogeneousIdeal.map f
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_map]
    exact Ideal.map_isPrime_of_surjective hf fun a ha => hp a ha
  not_irrelevant_le h := by
    refine p.not_irrelevant_le fun a ha => ?_
    have hfa : f a ∈ HomogeneousIdeal.irrelevant ℬ := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        ← GradedRingHom.map_directSumDecompose]
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha
      rw [ha, map_zero]
    exact mem_of_map_mem f hf p hp (h hfa)

theorem mem_liftPoint_iff (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (p : ProjectiveSpectrum 𝒜)
    (hp : ∀ a, f a = 0 → a ∈ p.asHomogeneousIdeal) (a : A) :
    f a ∈ (liftPoint f hf p hp).asHomogeneousIdeal ↔ a ∈ p.asHomogeneousIdeal :=
  ⟨mem_of_map_mem f hf p hp, fun h => Ideal.mem_map_of_mem _ h⟩

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- Homogeneous elements of the kernel are multiples of `x` by homogeneous elements. -/
theorem exists_mem_eq_mul {x : A} (hx : x ∈ 𝒜 1) (f : 𝒜 →+*ᵍ ℬ)
    (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {e : ℕ} {a : A} (ha : a ∈ 𝒜 (1 + e)) (hfa : f a = 0) :
    ∃ b ∈ 𝒜 e, a = x * b := by
  obtain ⟨b, rfl⟩ := hker a hfa
  refine ⟨DirectSum.decompose 𝒜 b e, SetLike.coe_mem _, ?_⟩
  rw [← DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hx, DirectSum.decompose_of_mem_same _ ha]

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
theorem eq_zero_of_mem_zero {x : A} (hx : x ∈ 𝒜 1) (f : 𝒜 →+*ᵍ ℬ)
    (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {a : A} (ha : a ∈ 𝒜 0) (hfa : f a = 0) : a = 0 := by
  obtain ⟨b, rfl⟩ := hker a hfa
  rw [← DirectSum.decompose_of_mem_same _ ha,
    DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 hx (by omega)]

/-- If `u c = 0` with `c` homogeneous and `u ∉ z`, some homogeneous component of `u` is not in
`z` and kills `c`. -/
theorem exists_homogeneous_mul_eq_zero (z : ProjectiveSpectrum ℬ) {u c : B} {j : ℕ}
    (hc : c ∈ ℬ j) (huc : u * c = 0) (hu : u ∉ z.asHomogeneousIdeal) :
    ∃ i, (DirectSum.decompose ℬ u i : B) ∉ z.asHomogeneousIdeal ∧
      (DirectSum.decompose ℬ u i : B) * c = 0 := by
  have hall : ∀ i, (DirectSum.decompose ℬ u i : B) * c = 0 := fun i => by
    rw [← DirectSum.coe_decompose_mul_add_of_right_mem ℬ hc, huc]
    simp
  obtain ⟨i, hi⟩ : ∃ i, (DirectSum.decompose ℬ u i : B) ∉ z.asHomogeneousIdeal := by
    by_contra! h
    exact hu ((z.asHomogeneousIdeal.isHomogeneous.mem_iff ℬ).2 h)
  exact ⟨i, hi, hall i⟩

/-- Multiplication by a degree-one element maps `S(n-1)_i` into `S(n)_i`. -/
theorem mul_mem_gradedTwist {x : A} (hx : x ∈ 𝒜 1) (n : ℤ) {i : ℤ} {m : A}
    (hm : m ∈ gradedTwist 𝒜 (n - 1) i) : x * m ∈ gradedTwist 𝒜 n i := by
  obtain ⟨hm1, hm2⟩ := hm
  by_cases h : n - 1 + i < 0
  · rw [hm2 h, mul_zero]
    exact zero_mem _
  · exact (mem_gradedTwist_of_eq (k := 1 + (n - 1 + i).toNat) (by omega)).2
      (SetLike.GradedMul.mul_mem hx hm1)

variable {x : A} (hx : x ∈ 𝒜 1) (n : ℤ)

/-- Multiplication by `x ∈ S_1`, `𝒪_{Proj S}(n-1) ⟶ 𝒪_{Proj S}(n)`. -/
def mulSection : projTwistingSheaf 𝒜 (n - 1) ⟶ projTwistingSheaf 𝒜 n :=
  projGradedModuleSheafMap (ℳ := gradedTwist 𝒜 (n - 1)) (𝒩 := gradedTwist 𝒜 n)
    (LinearMap.mulLeft A x) fun _ _ hm => mul_mem_gradedTwist hx n hm

/-- On fibers, multiplication by `x` followed by `φ` is zero when `φ(x) = 0`. -/
theorem twistFiber_gradedLocMap_mul (f : 𝒜 →+*ᵍ ℬ) (hfx : f x = 0) {P : Submonoid A}
    {Q : Submonoid B} (h : P ≤ Q.comap f)
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 (n - 1)) P) :
    twistFiber f n h (gradedLocMap (ℳ := gradedTwist 𝒜 (n - 1)) (𝒩 := gradedTwist 𝒜 n)
      (LinearMap.mulLeft A x) (fun _ _ hm => mul_mem_gradedTwist hx n hm) P y) = 0 := by
  obtain ⟨k, m, hm, t, ht, htP, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
  apply HomogeneousLocalizedModule.ext
  rw [val_twistFiber]
  change locMap f h (IsLocalizedModule.map P (LocalizedModule.mkLinearMap P A)
    (LocalizedModule.mkLinearMap P A) (LinearMap.mulLeft A x)
    (HomogeneousLocalizedModule.mk k m hm t ht htP).val) = 0
  rw [HomogeneousLocalizedModule.val_mk, IsLocalizedModule.map_LocalizedModules, locMap_mk]
  simp [map_mul, hfx]

/-- Multiplication by `x` followed by the restriction to `Proj T` is zero when `φ(x) = 0`. -/
theorem mulSection_psi (f : 𝒜 →+*ᵍ ℬ) (hfx : f x = 0) :
    mulSection hx n ≫ ProjTwistPullback.psi f n = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  refine Subtype.ext (funext fun z => ?_)
  exact twistFiber_gradedLocMap_mul hx n f hfx _ _

/-- If `x` is a non-zero-divisor, multiplication by `x` is injective on fibers. -/
theorem gradedLocMap_mul_injective (hinj : Function.Injective (x * ·)) (P : Submonoid A) :
    Function.Injective (gradedLocMap (𝒜 := 𝒜) (ℳ := gradedTwist 𝒜 (n - 1)) (𝒩 := gradedTwist 𝒜 n)
      (LinearMap.mulLeft A x) (fun _ _ hm => mul_mem_gradedTwist hx n hm) P) := by
  intro y z h
  apply HomogeneousLocalizedModule.ext
  exact IsLocalizedModule.map_injective P (LocalizedModule.mkLinearMap P A)
    (LocalizedModule.mkLinearMap P A) (LinearMap.mulLeft A x) hinj (congrArg (·.val) h)

theorem mulSection_app_injective (hinj : Function.Injective (x * ·))
    (U : (Proj 𝒜).Opensᵒᵖ) : Function.Injective ((mulSection hx n).val.app U) := by
  intro s t h
  refine Subtype.ext (funext fun p => ?_)
  exact gradedLocMap_mul_injective hx n hinj _ (congrFun (congrArg Subtype.val h) p)

/-- If `x` is a non-zero-divisor, multiplication by `x` is a monomorphism. -/
theorem mono_mulSection (hinj : Function.Injective (x * ·)) : Mono (mulSection hx n) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective fun U => mulSection_app_injective hx n hinj U

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- Elements of `S(n)_d` killed by `f` are `x` times elements of `S(n-1)_d`. -/
theorem exists_gradedTwist_eq_mul (hx : x ∈ 𝒜 1) (f : 𝒜 →+*ᵍ ℬ)
    (hker : ∀ a, f a = 0 → ∃ b, a = x * b)
    {d : ℤ} {a : A} (ha : a ∈ gradedTwist 𝒜 n d) (hfa : f a = 0) :
    ∃ b ∈ gradedTwist 𝒜 (n - 1) d, a = x * b := by
  obtain ⟨ha1, ha2⟩ := ha
  by_cases h : n + d < 0
  · exact ⟨0, zero_mem _, by rw [ha2 h, mul_zero]⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, (n + d).toNat = e := ⟨_, rfl⟩
  rw [he] at ha1
  cases e with
  | zero => exact ⟨0, zero_mem _, by rw [eq_zero_of_mem_zero hx f hker ha1 hfa, mul_zero]⟩
  | succ e =>
    rw [show e + 1 = 1 + e by omega] at ha1
    obtain ⟨b, hb, rfl⟩ := exists_mem_eq_mul hx f hker ha1 hfa
    exact ⟨b, (mem_gradedTwist_of_eq (by omega)).2 hb, rfl⟩

/-- The fiber of multiplication by `x` at `P`. -/
abbrev mulFiber (P : Submonoid A) :=
  gradedLocMap (𝒜 := 𝒜) (ℳ := gradedTwist 𝒜 (n - 1)) (𝒩 := gradedTwist 𝒜 n)
    (LinearMap.mulLeft A x) (fun _ _ hm => mul_mem_gradedTwist hx n hm) P

omit [AddSubgroupClass τ B] [GradedRing ℬ] in
/-- If `x b = u m`, then `x · (b / (u g)) = m / g`. -/
theorem mulFiber_mk {P : Submonoid A} {k i : ℕ} {m b u g : A} (hm : m ∈ gradedTwist 𝒜 n k)
    (hb : b ∈ gradedTwist 𝒜 (n - 1) ((i + k : ℕ) : ℤ)) (hg : g ∈ 𝒜 k) (hu : u ∈ 𝒜 i)
    (hgP : g ∈ P) (hugP : u * g ∈ P) (hxb : x * b = u * m) :
    mulFiber hx n P (HomogeneousLocalizedModule.mk (i + k) b hb (u * g)
      (SetLike.GradedMul.mul_mem hu hg) hugP) = HomogeneousLocalizedModule.mk k m hm g hg hgP := by
  apply HomogeneousLocalizedModule.ext
  change IsLocalizedModule.map P (LocalizedModule.mkLinearMap P A)
    (LocalizedModule.mkLinearMap P A) (LinearMap.mulLeft A x)
    (LocalizedModule.mk b ⟨u * g, hugP⟩) = LocalizedModule.mk m ⟨g, hgP⟩
  rw [IsLocalizedModule.map_LocalizedModules, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_eq_mul, LinearMap.mulLeft_apply]
  rw [hxb]
  ring

omit [AddSubgroupClass τ B] [GradedRing ℬ] [GradedRing 𝒜] in
theorem mem_gradedTwist_pred {k : ℕ} {m : A} (hm : m ∈ gradedTwist 𝒜 n k) :
    m ∈ gradedTwist 𝒜 (n - 1) ((1 + k : ℕ) : ℤ) := by
  obtain ⟨hm1, hm2⟩ := hm
  have e : n - 1 + ((1 + k : ℕ) : ℤ) = n + (k : ℤ) := by push_cast; ring
  show m ∈ 𝒜 (n - 1 + ((1 + k : ℕ) : ℤ)).toNat ∧ (n - 1 + ((1 + k : ℕ) : ℤ) < 0 → m = 0)
  rw [e]
  exact ⟨hm1, hm2⟩

/-- **Local preimages.** A section `t` of `𝒪(n)` killed by `psi` is, near each point, `x` times
a fraction `b / g` with `b ∈ S(n-1)`. -/
theorem exists_local_preimage (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {V : (Proj 𝒜).Opens}
    (t : (sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj (op V))
    (ht : ProjTwistPullback.psiSections f n V t = 0) (p : V) :
    ∃ (W : Opens (ProjectiveSpectrum.top 𝒜)) (_ : p.1 ∈ W) (iWV : W ⟶ V) (k : ℕ) (b : A)
      (hb : b ∈ gradedTwist 𝒜 (n - 1) k) (g : A) (hg : g ∈ 𝒜 k)
      (g_nin : ∀ y : W, g ∉ y.1.asHomogeneousIdeal),
      ∀ y : W, mulFiber hx n _ (HomogeneousLocalizedModule.mk k b hb g hg (g_nin y)) =
        t.1 (iWV y) := by
  obtain ⟨W, hpW, iWV, k, m, hm, g, hg, g_nin, w⟩ := t.2 p
  obtain ⟨i, u, hu, hup, b, hb, hxb⟩ : ∃ (i : ℕ) (u : A) (_ : u ∈ 𝒜 i),
      u ∉ p.1.asHomogeneousIdeal ∧
        ∃ b ∈ gradedTwist 𝒜 (n - 1) ((i + k : ℕ) : ℤ), x * b = u * m := by
    by_cases hxp : x ∈ p.1.asHomogeneousIdeal
    · have hp' : ∀ a, f a = 0 → a ∈ p.1.asHomogeneousIdeal := fun a ha => by
        obtain ⟨c, rfl⟩ := hker a ha
        exact Ideal.mul_mem_right _ _ hxp
      have hzD : liftPoint f hf p.1 hp' ∈ projPartialDomain f := by
        refine (mem_projPartialDomain_iff f _).2 fun hsub => ?_
        refine p.1.not_irrelevant_le fun a ha => ?_
        exact (mem_liftPoint_iff f hf p.1 hp' a).1 (hsub ⟨a, ha, rfl⟩)
      have hcomap : projPartialComapPoint f (liftPoint f hf p.1 hp') hzD = p.1 := by
        apply ProjectiveSpectrum.ext
        apply HomogeneousIdeal.ext
        ext a
        exact mem_liftPoint_iff f hf p.1 hp' a
      have hzV : liftPoint f hf p.1 hp' ∈
          (projPartialDomain f).ι ''ᵁ (projPartialMap f ⁻¹ᵁ V) := by
        refine ⟨⟨_, hzD⟩, ?_, rfl⟩
        change projPartialMap f ⟨_, hzD⟩ ∈ V
        rw [projPartialMap_apply]
        have := p.2
        rw [← hcomap] at this
        exact this
      have h0 := congrFun (congrArg Subtype.val ht) ⟨_, hzV⟩
      have hW : projPartialComapPoint f (liftPoint f hf p.1 hp') hzD ∈ W := by
        rw [hcomap]
        exact hpW
      have h1 := w ⟨_, hW⟩
      have h2 : twistFiber f n (ProjTwistPullback.primeCompl_le_comap_point f _ hzD)
          (HomogeneousLocalizedModule.mk k m hm g hg (g_nin ⟨_, hW⟩)) = 0 := by
        rw [← h1]
        exact h0
      rw [twistFiber_mk] at h2
      have h3 := congrArg HomogeneousLocalizedModule.val h2
      rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_zero,
        ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h3
      obtain ⟨c, hc⟩ := h3
      simp only [one_smul, smul_zero, Submonoid.smul_def, smul_eq_mul] at hc
      obtain ⟨j, hj, hjm⟩ := exists_homogeneous_mul_eq_zero (liftPoint f hf p.1 hp')
        (map_mem_gradedTwist f hm).1 hc c.2
      obtain ⟨u, hu, hfu⟩ := ProjSurjection.exists_homogeneous_preimage hf
        (SetLike.coe_mem (DirectSum.decompose ℬ (c : B) j))
      have hup : u ∉ p.1.asHomogeneousIdeal := fun h =>
        hj (hfu ▸ (mem_liftPoint_iff f hf p.1 hp' u).2 h)
      have hum : u * m ∈ gradedTwist 𝒜 n ((j + k : ℕ) : ℤ) := by
        have := smul_mem_graded_nat 𝒜 (gradedTwist 𝒜 n) hu hm
        rwa [smul_eq_mul, show ((j : ℕ) : ℤ) + (k : ℤ) = ((j + k : ℕ) : ℤ) by push_cast; ring]
          at this
      have hfum : f (u * m) = 0 := by rw [map_mul, hfu, hjm]
      obtain ⟨b, hb, hb'⟩ := exists_gradedTwist_eq_mul n hx f hker hum hfum
      exact ⟨j, u, hu, hup, b, hb, hb'.symm⟩
    · exact ⟨1, x, hx, hxp, m, mem_gradedTwist_pred n hm, rfl⟩
  refine ⟨W ⊓ ProjectiveSpectrum.basicOpen 𝒜 u,
    ⟨hpW, (ProjectiveSpectrum.mem_basicOpen 𝒜 _ _).2 hup⟩, Opens.infLELeft _ _ ≫ iWV, i + k, b,
    hb, u * g, SetLike.GradedMul.mul_mem hu hg, fun y h => ?_, fun y => ?_⟩
  · rcases y.1.isPrime.mem_or_mem h with h' | h'
    · exact (ProjectiveSpectrum.mem_basicOpen 𝒜 _ _).1 y.2.2 h'
    · exact g_nin ⟨y.1, y.2.1⟩ h'
  · rw [mulFiber_mk hx n hm hb hg hu (g_nin ⟨y.1, y.2.1⟩) _ hxb]
    exact (w ⟨y.1, y.2.1⟩).symm

/-- **Exactness at `𝒪(n)` on sections.** If `x` is a non-zero-divisor and `ker f = (x)`, every
section of `𝒪(n)` killed by `psi` is `x` times a section of `𝒪(n-1)`. -/
theorem exists_mulSection_preimage (hinj : Function.Injective (x * ·)) (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {V : (Proj 𝒜).Opens}
    (t : (sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj (op V))
    (ht : ProjTwistPullback.psiSections f n V t = 0) :
    ∃ s, gradedSheafSections (ℳ := gradedTwist 𝒜 (n - 1)) (𝒩 := gradedTwist 𝒜 n)
      (LinearMap.mulLeft A x) (fun _ _ hm => mul_mem_gradedTwist hx n hm) V s = t := by
  have hloc := exists_local_preimage hx n f hf hker t ht
  have hex : ∀ q : V, ∃ y, mulFiber hx n _ y = t.1 q := fun q => by
    obtain ⟨W, hqW, iWV, k, b, hb, g, hg, g_nin, w⟩ := hloc q
    exact ⟨_, w ⟨q.1, hqW⟩⟩
  choose sf hsf using hex
  refine ⟨⟨sf, fun q => ?_⟩, Subtype.ext (funext fun q => hsf q)⟩
  obtain ⟨W, hqW, iWV, k, b, hb, g, hg, g_nin, w⟩ := hloc q
  exact ⟨W, hqW, iWV, k, b, hb, g, hg, g_nin, fun y =>
    gradedLocMap_mul_injective hx n hinj _ ((hsf _).trans (w y).symm)⟩

/-- A morphism equal to zero is zero on sections. -/
theorem app_eq_zero_of_comp_eq_zero {X : Scheme.{u}} {M N : X.Modules} {g : M ⟶ N} (hg : g = 0)
    (U : X.Opensᵒᵖ) (s : M.val.obj U) : g.val.app U s = 0 := by
  subst hg
  rfl

/-- The lift through multiplication by `x` of a map into the kernel of `psi`, sectionwise. -/
def liftFun (hinj : Function.Injective (x * ·)) (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {Z : (Proj 𝒜).Modules}
    (k : Z ⟶ projTwistingSheaf 𝒜 n) (hk : k ≫ ProjTwistPullback.psi f n = 0)
    (U : (Proj 𝒜).Opensᵒᵖ) (t : Z.val.obj U) : (projTwistingSheaf 𝒜 (n - 1)).val.obj U :=
  (exists_mulSection_preimage hx n hinj f hf hker (V := U.unop) (k.val.app U t)
    (app_eq_zero_of_comp_eq_zero hk U t)).choose

theorem mulSection_liftFun (hinj : Function.Injective (x * ·)) (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {Z : (Proj 𝒜).Modules}
    (k : Z ⟶ projTwistingSheaf 𝒜 n) (hk : k ≫ ProjTwistPullback.psi f n = 0)
    (U : (Proj 𝒜).Opensᵒᵖ) (t : Z.val.obj U) :
    (mulSection hx n).val.app U (liftFun hx n hinj f hf hker k hk U t) = k.val.app U t :=
  (exists_mulSection_preimage hx n hinj f hf hker (V := U.unop) (k.val.app U t)
    (app_eq_zero_of_comp_eq_zero hk U t)).choose_spec

/-- The lift through multiplication by `x` of a map into the kernel of `psi`. -/
def lift (hinj : Function.Injective (x * ·)) (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {Z : (Proj 𝒜).Modules}
    (k : Z ⟶ projTwistingSheaf 𝒜 n) (hk : k ≫ ProjTwistPullback.psi f n = 0) :
    Z ⟶ projTwistingSheaf 𝒜 (n - 1) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := liftFun hx n hinj f hf hker k hk U
          map_zero' := mulSection_app_injective hx n hinj U (by
            rw [mulSection_liftFun, map_zero, map_zero])
          map_add' t t' := mulSection_app_injective hx n hinj U (by
            rw [mulSection_liftFun, map_add, map_add, mulSection_liftFun, mulSection_liftFun]) }
      naturality := fun U V g => by
        ext t
        exact mulSection_app_injective hx n hinj V (by
          change (mulSection hx n).val.app V (liftFun hx n hinj f hf hker k hk V (Z.val.map g t)) =
            (mulSection hx n).val.app V ((projTwistingSheaf 𝒜 (n - 1)).val.map g
              (liftFun hx n hinj f hf hker k hk U t))
          rw [mulSection_liftFun, PresheafOfModules.naturality_apply k.val,
            PresheafOfModules.naturality_apply (mulSection hx n).val, mulSection_liftFun]) }
    (fun U r t => mulSection_app_injective hx n hinj U (by
      change (mulSection hx n).val.app U (liftFun hx n hinj f hf hker k hk U (r • t)) =
        (mulSection hx n).val.app U (r • liftFun hx n hinj f hf hker k hk U t)
      rw [mulSection_liftFun, map_smul, map_smul, mulSection_liftFun]))

theorem lift_mulSection (hinj : Function.Injective (x * ·)) (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (hker : ∀ a, f a = 0 → ∃ b, a = x * b) {Z : (Proj 𝒜).Modules}
    (k : Z ⟶ projTwistingSheaf 𝒜 n) (hk : k ≫ ProjTwistPullback.psi f n = 0) :
    lift hx n hinj f hf hker k hk ≫ mulSection hx n = k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro t
  exact mulSection_liftFun hx n hinj f hf hker k hk U t

/-- **Exactness at `𝒪(n)`.** Multiplication by `x` is a kernel of `psi`. -/
def isLimitMulSection (hinj : Function.Injective (x * ·)) (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (hfx : f x = 0) (hker : ∀ a, f a = 0 → ∃ b, a = x * b) :
    Limits.IsLimit (Limits.KernelFork.ofι (mulSection hx n) (mulSection_psi hx n f hfx)) :=
  haveI := mono_mulSection hx n hinj
  Limits.KernelFork.IsLimit.ofι' _ _ fun k hk =>
    ⟨lift hx n hinj f hf hker k hk, lift_mulSection hx n hinj f hf hker k hk⟩

/-- Elements of `T(n)_d` have preimages in `S(n)_d` under a surjective graded map. -/
theorem exists_gradedTwist_preimage (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) {n d : ℤ}
    {b : B} (hb : b ∈ gradedTwist ℬ n d) : ∃ a ∈ gradedTwist 𝒜 n d, f a = b := by
  obtain ⟨hb1, hb2⟩ := hb
  by_cases h : n + d < 0
  · exact ⟨0, zero_mem _, by rw [hb2 h, map_zero]⟩
  obtain ⟨a, ha, rfl⟩ := ProjSurjection.exists_homogeneous_preimage hf hb1
  exact ⟨a, ⟨ha, fun h' => absurd h' h⟩, rfl⟩

/-- **The restriction `𝒪_{Proj S}(n) ⟶ f_*(𝒪_{Proj T}(n))` is an epimorphism** for a surjective
graded map `f`. -/
theorem epi_psi (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (n : ℤ) :
    Epi (ProjTwistPullback.psi f n) := by
  have h1 : Epi ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map
      (ProjTwistPullback.psi f n)) := by
    refine (TopCat.Sheaf.isLocallySurjective_iff_epi _).1
      ((TopCat.Presheaf.isLocallySurjective_iff _).2 fun U t p hp => ?_)
    by_cases hker : ∀ a, f a = 0 → a ∈ p.asHomogeneousIdeal
    · have hzD : liftPoint f hf p hker ∈ projPartialDomain f := by
        refine (mem_projPartialDomain_iff f _).2 fun hsub => ?_
        refine p.not_irrelevant_le fun a ha => ?_
        exact (mem_liftPoint_iff f hf p hker a).1 (hsub ⟨a, ha, rfl⟩)
      have hcomap : projPartialComapPoint f (liftPoint f hf p hker) hzD = p := by
        apply ProjectiveSpectrum.ext
        apply HomogeneousIdeal.ext
        ext a
        exact mem_liftPoint_iff f hf p hker a
      have hzU : liftPoint f hf p hker ∈
          (projPartialDomain f).ι ''ᵁ (projPartialMap f ⁻¹ᵁ U) := by
        refine ⟨⟨_, hzD⟩, ?_, rfl⟩
        change projPartialMap f ⟨_, hzD⟩ ∈ U
        rw [projPartialMap_apply]
        have := hp
        rw [← hcomap] at this
        exact this
      obtain ⟨W, hzW, iWD, k, b', hb', g', hg', g_nin, w⟩ := t.2 ⟨_, hzU⟩
      obtain ⟨_, ⟨c', rfl⟩, hzc, hcW⟩ :=
        (ProjectiveSpectrum.isTopologicalBasis_basic_opens (𝒜 := ℬ)).exists_subset_of_mem_open
          hzW W.isOpen
      obtain ⟨c, rfl⟩ := hf c'
      obtain ⟨g, hg, rfl⟩ := ProjSurjection.exists_homogeneous_preimage hf hg'
      obtain ⟨b, hb, rfl⟩ := exists_gradedTwist_preimage f hf hb'
      have hgp : g ∉ p.asHomogeneousIdeal := fun h =>
        g_nin ⟨_, hzW⟩ ((mem_liftPoint_iff f hf p hker g).2 h)
      have hcp : c ∉ p.asHomogeneousIdeal := fun h =>
        (ProjectiveSpectrum.mem_basicOpen ℬ _ _).1 hzc ((mem_liftPoint_iff f hf p hker c).2 h)
      let V : (Proj 𝒜).Opens :=
        U ⊓ ProjectiveSpectrum.basicOpen 𝒜 g ⊓ ProjectiveSpectrum.basicOpen 𝒜 c
      have hgV : ∀ q : V, g ∉ q.1.asHomogeneousIdeal := fun q =>
        (ProjectiveSpectrum.mem_basicOpen 𝒜 _ _).1 q.2.1.2
      let s : (sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj (op V) :=
        ⟨fun q => HomogeneousLocalizedModule.mk k b hb g hg (hgV q), fun q =>
          ⟨V, q.2, 𝟙 V, k, b, hb, g, hg, hgV, fun _ => rfl⟩⟩
      refine ⟨V, fun q hq => hq.1.1, ⟨s, ?_⟩,
        ⟨⟨hp, (ProjectiveSpectrum.mem_basicOpen 𝒜 _ _).2 hgp⟩,
          (ProjectiveSpectrum.mem_basicOpen 𝒜 _ _).2 hcp⟩⟩
      refine Subtype.ext (funext fun z => ?_)
      have hzV := ProjTwistPullback.comap_mem_of_mem_image f z.2
      have hzW' : z.1 ∈ W := hcW ((ProjectiveSpectrum.mem_basicOpen ℬ _ _).2
        fun h => (ProjectiveSpectrum.mem_basicOpen 𝒜 _ _).1 hzV.2 h)
      exact (twistFiber_mk f n _ k b hb g hg _).trans (w ⟨z.1, hzW'⟩).symm
    · push Not at hker
      obtain ⟨a, ha0, ha⟩ := hker
      refine ⟨U ⊓ ProjectiveSpectrum.basicOpen 𝒜 a, inf_le_left, ⟨0, ?_⟩,
        ⟨hp, (ProjectiveSpectrum.mem_basicOpen 𝒜 _ _).2 ha⟩⟩
      refine Subtype.ext (funext fun z => ?_)
      exfalso
      have hz := ProjTwistPullback.comap_mem_of_mem_image f z.2
      exact (ProjectiveSpectrum.mem_basicOpen 𝒜 _ _).1 hz.2
        (show f a ∈ z.1.asHomogeneousIdeal by rw [ha0]; exact zero_mem _)
  exact (SheafOfModules.toSheaf _).epi_of_epi_map h1

/-- **The degreewise hyperplane sequence** `0 → 𝒪(n-1) → 𝒪(n) → f_* 𝒪_{Proj T}(n) → 0` is short
exact, for `x ∈ S_1` a non-zero-divisor and `f` surjective with kernel `(x)`. -/
theorem shortExact (hx : x ∈ 𝒜 1) (n : ℤ) (hinj : Function.Injective (x * ·))
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (hfx : f x = 0)
    (hker : ∀ a, f a = 0 → ∃ b, a = x * b) :
    (ShortComplex.mk (mulSection hx n) (ProjTwistPullback.psi f n)
      (mulSection_psi hx n f hfx)).ShortExact :=
  haveI := epi_psi f hf n
  haveI := mono_mulSection hx n hinj
  { exact := ShortComplex.exact_of_f_is_kernel _ (isLimitMulSection hx n hinj f hf hfx hker) }

end General

section ProjectiveSpace

variable (A : Type u) [CommRing A] (m : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate substitution `x_i ↦ x_i` (`i ≤ m`), `x_{m+1} ↦ 0`. -/
abbrev hyperplaneSubst : Fin (m + 2) → MvPolynomial (Fin (m + 1)) A :=
  Fin.lastCases 0 MvPolynomial.X

/-- **The hyperplane restriction** `A[x_0, …, x_{m+1}] → A[x_0, …, x_m]`, `x_{m+1} ↦ 0`, as a
graded ring map. -/
def hyperplaneHom :
    MvPolynomial.homogeneousSubmodule (Fin (m + 2)) A →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A where
  toRingHom := (MvPolynomial.aeval (hyperplaneSubst A m)).toRingHom
  map_mem {k} φ hφ := by
    have h := (MvPolynomial.mem_homogeneousSubmodule k φ).1 hφ
    refine (MvPolynomial.mem_homogeneousSubmodule k _).2 ?_
    have := h.eval₂ (algebraMap A (MvPolynomial (Fin (m + 1)) A)) (hyperplaneSubst A m)
      (fun r => MvPolynomial.isHomogeneous_C _ r) (n := 1) (fun i => by
        induction i using Fin.lastCases with
        | last => simpa using MvPolynomial.isHomogeneous_zero _ _ 1
        | cast i => simpa using MvPolynomial.isHomogeneous_X A i)
    rw [one_mul] at this
    exact this

theorem hyperplaneHom_apply (φ : MvPolynomial (Fin (m + 2)) A) :
    hyperplaneHom A m φ = MvPolynomial.aeval (hyperplaneSubst A m) φ :=
  rfl

theorem hyperplaneHom_X_last : hyperplaneHom A m (MvPolynomial.X (Fin.last (m + 1))) = 0 := by
  simp [hyperplaneHom_apply]

theorem hyperplaneHom_surjective : Function.Surjective (hyperplaneHom A m) := by
  intro ψ
  induction ψ using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, by simp [hyperplaneHom_apply]⟩
  | add p q hp hq =>
    obtain ⟨p', rfl⟩ := hp
    obtain ⟨q', rfl⟩ := hq
    exact ⟨p' + q', map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨p', rfl⟩ := hp
    exact ⟨p' * MvPolynomial.X i.castSucc, by simp [hyperplaneHom_apply]⟩

theorem x_last_mem : (MvPolynomial.X (Fin.last (m + 1)) : MvPolynomial (Fin (m + 2)) A) ∈
    MvPolynomial.homogeneousSubmodule (Fin (m + 2)) A 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X A _)

/-- The hyperplane `H = V₊(x_{m+1}) ≅ ℙ^m_A` maps to `ℙ^{m+1}_A` by a closed immersion. -/
theorem isClosedImmersion_hyperplane :
    IsClosedImmersion (projPartialMap (hyperplaneHom A m)) :=
  isClosedImmersion_projPartialMap_of_surjective (hyperplaneHom_surjective A m)

/-- **Multiplication by `x_{m+1}` followed by restriction to the hyperplane is zero**:
`𝒪_X(n-1) ⟶ 𝒪_X(n) ⟶ i_* 𝒪_H(n)`. -/
theorem mulSection_psi_hyperplane (n : ℤ) :
    mulSection (x_last_mem A m) n ≫ ProjTwistPullback.psi (hyperplaneHom A m) n = 0 :=
  mulSection_psi _ n _ (hyperplaneHom_X_last A m)

/-- **Multiplication by `x_{m+1}` is injective**: `𝒪_X(n-1) ⟶ 𝒪_X(n)` is a monomorphism. -/
instance mono_mulSection_hyperplane (n : ℤ) : Mono (mulSection (x_last_mem A m) n) :=
  mono_mulSection _ n MvPolynomial.isRegular_X.left

/-- `x_{m+1}` divides `a - a(x_0, …, x_m, 0)`. -/
theorem X_last_dvd_sub (a : MvPolynomial (Fin (m + 2)) A) :
    MvPolynomial.X (Fin.last (m + 1)) ∣
      a - MvPolynomial.rename Fin.castSucc (hyperplaneHom A m a) := by
  induction a using MvPolynomial.induction_on with
  | C c => simp [hyperplaneHom_apply]
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    induction i using Fin.lastCases with
    | last => simp [hyperplaneHom_apply]
    | cast j =>
      have e : p * MvPolynomial.X j.castSucc -
          MvPolynomial.rename Fin.castSucc (hyperplaneHom A m (p * MvPolynomial.X j.castSucc)) =
          (p - MvPolynomial.rename Fin.castSucc (hyperplaneHom A m p)) *
            MvPolynomial.X j.castSucc := by
        simp [hyperplaneHom_apply, sub_mul]
      rw [e]
      exact dvd_mul_of_dvd_left hp _

/-- The kernel of `hyperplaneHom` is generated by `x_{m+1}`. -/
theorem exists_eq_X_last_mul {a : MvPolynomial (Fin (m + 2)) A} (ha : hyperplaneHom A m a = 0) :
    ∃ b, a = MvPolynomial.X (Fin.last (m + 1)) * b := by
  obtain ⟨b, hb⟩ := X_last_dvd_sub A m a
  rw [ha, map_zero, sub_zero] at hb
  exact ⟨b, hb⟩

/-- **Exactness at `𝒪_X(n)`** on `ℙ^{m+1}_A`: multiplication by `x_{m+1}` is a kernel of the
restriction `𝒪_X(n) ⟶ i_* 𝒪_H(n)`. -/
def isLimitMulSection_hyperplane (n : ℤ) :
    Limits.IsLimit (Limits.KernelFork.ofι (mulSection (x_last_mem A m) n)
      (mulSection_psi_hyperplane A m n)) :=
  isLimitMulSection _ n MvPolynomial.isRegular_X.left _ (hyperplaneHom_surjective A m)
    (hyperplaneHom_X_last A m) fun _ ha => exists_eq_X_last_mul A m ha

/-- **The hyperplane sequence on `ℙ^{m+1}_A`**, degreewise: for `H = V₊(x_{m+1}) ≅ ℙ^m_A` and
`i : H ⟶ ℙ^{m+1}_A`,
`0 → 𝒪_X(n-1) → 𝒪_X(n) → i_* 𝒪_H(n) → 0`, with first map multiplication by `x_{m+1}`, is short
exact. -/
theorem hyperplane_shortExact (n : ℤ) :
    (ShortComplex.mk (mulSection (x_last_mem A m) n)
      (ProjTwistPullback.psi (hyperplaneHom A m) n) (mulSection_psi_hyperplane A m n)).ShortExact :=
  shortExact _ n MvPolynomial.isRegular_X.left _ (hyperplaneHom_surjective A m)
    (hyperplaneHom_X_last A m) fun _ ha => exists_eq_X_last_mul A m ha

end ProjectiveSpace

end Hartshorne.HyperplaneSequence
