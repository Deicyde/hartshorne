/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjTwistingSheaf
import Hartshorne.Scheme.RelativeProj

/-!
# Twisting sheaves under graded ring maps and localization on degree zero

Let `φ : A → B` be a map of `ℕ`-graded rings with `B₊ ⊆ φ(A₊) B`, so that it induces
`f = Proj.map φ : Proj B ⟶ Proj A`, and let `n ∈ ℤ`. At a point `𝔮` of `Proj B` with image
`𝔭 = φ⁻¹ 𝔮`, the fraction map `A(n)_(𝔭) → B(n)_(𝔮)`, `m / t ↦ φ m / φ t`, is compatible with the
local ring map `A_(𝔭) → B_(𝔮)` and preserves locally fractional sections; it gives a morphism of
sheaves of modules `𝒪_{Proj A}(n) ⟶ f_* 𝒪_{Proj B}(n)`.

If `B = A[1/s]` with `s` of degree zero, `f` is an open immersion onto `D₊(s)` and the fiber maps
are bijective, so the adjoint morphism `f^* 𝒪_{Proj A}(n) = 𝒪_{Proj A}(n)|_{Proj B} ⟶
𝒪_{Proj B}(n)` is an isomorphism: twisting sheaves are compatible with localization on the
degree-zero part. The fiber maps are functorial, which gives the cocycle compatibility needed to
glue the twisting sheaves of the affine pieces of a relative `Proj`.

## Main definitions and results

* `Hartshorne.ProjTwistMap.twistFiber`: the fiber map `A(n)_(P) → B(n)_(Q)` for `P ⊆ φ⁻¹ Q`.
* `Hartshorne.ProjTwistMap.twistFiber_comp`: functoriality of the fiber maps.
* `Hartshorne.ProjTwistMap.twistHom`: `𝒪_{Proj A}(n) ⟶ f_* 𝒪_{Proj B}(n)`.
* `Hartshorne.ProjTwistMap.twistRestrictHom`: the adjoint `𝒪_{Proj A}(n)|_{Proj B} ⟶
  𝒪_{Proj B}(n)` when `f` is an open immersion.
* `Hartshorne.ProjTwistMap.isIso_twistRestrictHom`, `twistRestrictIso`: for `B = A[1/s]` with
  `s ∈ A₀`, `𝒪_{Proj A}(n)|_{Proj B} ≅ 𝒪_{Proj B}(n)`.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

namespace ProjTwistMap

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite HomogeneousLocalization Graded
  HomogeneousIdeal

variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (φ : 𝒜 →+*ᵍ ℬ)

/-! ### Fiber maps -/

omit [GradedRing 𝒜] [GradedRing ℬ] in
/-- A graded ring map preserves the components of the twists: `φ(A(n)_d) ⊆ B(n)_d`. -/
theorem map_mem_gradedTwist {n d : ℤ} {a : A} (ha : a ∈ gradedTwist 𝒜 n d) :
    φ a ∈ gradedTwist ℬ n d :=
  ⟨map_mem φ ha.1, fun h => by rw [ha.2 h, map_zero]⟩

variable {P : Submonoid A} {Q : Submonoid B}

/-- The map `P⁻¹ A → Q⁻¹ B`, `m / t ↦ φ m / φ t`, for submonoids with `P ⊆ φ⁻¹ Q`. -/
def locMap (h : P ≤ Q.comap φ) : LocalizedModule P A →+ LocalizedModule Q B where
  toFun y := y.liftOn (fun p => LocalizedModule.mk (φ p.1) ⟨φ p.2, h p.2.2⟩)
    fun p p' e => by
      obtain ⟨u, hu⟩ := e
      refine (LocalizedModule.mk_eq (M := B) (S := Q)).2 ⟨⟨φ u, h u.2⟩, ?_⟩
      have := congrArg φ hu
      simpa [Submonoid.smul_def, smul_eq_mul, map_mul] using this
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.liftOn_mk]
    simp
  map_add' y z := by
    induction y, z using LocalizedModule.induction_on₂ with
    | h m m' t t' =>
      rw [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk,
        LocalizedModule.liftOn_mk, LocalizedModule.mk_add_mk]
      simp only [Submonoid.smul_def, smul_eq_mul, map_mul, map_add]
      congr 1
      ext
      simp [map_mul]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
theorem locMap_mk (h : P ≤ Q.comap φ) (m : A) (t : P) :
    locMap φ h (LocalizedModule.mk m t) = LocalizedModule.mk (φ m) ⟨φ t, h t.2⟩ := by
  rw [locMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LocalizedModule.liftOn_mk]

/-- **The fiber map** `A(n)_(P) → B(n)_(Q)`, `m / t ↦ φ m / φ t`, for submonoids with
`P ⊆ φ⁻¹ Q`. -/
def twistFiber (n : ℤ) (h : P ≤ Q.comap φ) :
    HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 n) P →+
      HomogeneousLocalizedModule ℬ (gradedTwist ℬ n) Q where
  toFun y := ⟨locMap φ h y.val, by
    obtain ⟨k, m, hm, t, ht, htx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
    exact ⟨k, φ m, φ t, map_mem_gradedTwist φ hm, map_mem φ ht, h htx, by
      rw [HomogeneousLocalizedModule.val_mk, locMap_mk]⟩⟩
  map_zero' := by
    ext
    exact map_zero (locMap φ h)
  map_add' y z := by
    ext
    exact map_add (locMap φ h) y.val z.val

theorem val_twistFiber (n : ℤ) (h : P ≤ Q.comap φ)
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 n) P) :
    (twistFiber φ n h y).val = locMap φ h y.val :=
  rfl

theorem twistFiber_mk (n : ℤ) (h : P ≤ Q.comap φ) (k : ℕ) (m : A)
    (hm : m ∈ gradedTwist 𝒜 n k) (t : A) (ht : t ∈ 𝒜 k) (htx : t ∈ P) :
    twistFiber φ n h (HomogeneousLocalizedModule.mk k m hm t ht htx) =
      HomogeneousLocalizedModule.mk k (φ m) (map_mem_gradedTwist φ hm) (φ t) (map_mem φ ht)
        (h htx) := by
  ext
  rw [val_twistFiber, HomogeneousLocalizedModule.val_mk, locMap_mk,
    HomogeneousLocalizedModule.val_mk]

theorem twistFiber_smul (n : ℤ) (h : P ≤ Q.comap φ) (c : HomogeneousLocalization 𝒜 P)
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 n) P) :
    twistFiber φ n h (c • y) = HomogeneousLocalization.map φ h c • twistFiber φ n h y := by
  obtain ⟨⟨i, ⟨a, ha⟩, ⟨b, hb⟩, hbx⟩, rfl⟩ := HomogeneousLocalization.mk_surjective c
  obtain ⟨k, m, hm, t, ht, htx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
  ext
  rw [HomogeneousLocalizedModule.val_smul, val_twistFiber, HomogeneousLocalizedModule.val_smul,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalizedModule.val_mk, val_twistFiber,
    HomogeneousLocalizedModule.val_mk, LocalizedModule.mk_smul_mk, locMap_mk, locMap_mk,
    LocalizedModule.mk_smul_mk]
  simp only [smul_eq_mul, map_mul, Submonoid.mk_mul_mk]

/-- **Functoriality of the fiber maps**: the fiber map of a composite is the composite of the
fiber maps. -/
theorem twistFiber_comp (φ' : ℬ →+*ᵍ 𝒞) (φ'' : 𝒜 →+*ᵍ 𝒞) (hcomp : ∀ a, φ'' a = φ' (φ a))
    {R : Submonoid C} (n : ℤ) (h : P ≤ Q.comap φ) (h' : Q ≤ R.comap φ') (h'' : P ≤ R.comap φ'')
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 n) P) :
    twistFiber φ'' n h'' y = twistFiber φ' n h' (twistFiber φ n h y) := by
  obtain ⟨k, m, hm, t, ht, htx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
  rw [twistFiber_mk, twistFiber_mk, twistFiber_mk]
  ext
  simp only [HomogeneousLocalizedModule.val_mk, hcomp]

/-- The fiber map of a graded ring map which is the identity is the identity. -/
theorem twistFiber_id (φ : 𝒜 →+*ᵍ 𝒜) (hid : ∀ a, φ a = a) (n : ℤ) (h : P ≤ P.comap φ)
    (y : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 n) P) :
    twistFiber φ n h y = y := by
  obtain ⟨k, m, hm, t, ht, htx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
  rw [twistFiber_mk]
  ext
  simp only [HomogeneousLocalizedModule.val_mk, hid]

/-! ### The morphism of twisting sheaves -/

variable (hf : ℬ₊ ≤ 𝒜₊.map φ) (n : ℤ)

theorem primeCompl_le_comap (y : ProjectiveSpectrum ℬ) :
    (ProjectiveSpectrum.comap φ hf y).asHomogeneousIdeal.toIdeal.primeCompl ≤
      y.asHomogeneousIdeal.toIdeal.primeCompl.comap φ :=
  fun _ ha => ha

/-- The map on sections over `U` of `𝒪_{Proj A}(n) ⟶ f_* 𝒪_{Proj B}(n)`: a section `s` goes to
`𝔮 ↦ s(φ⁻¹ 𝔮)`, through the fiber maps. -/
def twistSections (U : (Proj 𝒜).Opens) :
    (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj (op U) →+
      (ProjGradedModuleSheaf.sheafInType ℬ (gradedTwist ℬ n)).1.obj
        (op (Proj.map φ hf ⁻¹ᵁ U)) where
  toFun s := ⟨fun y => twistFiber φ n (primeCompl_le_comap φ hf y.1)
      (s.1 ⟨ProjectiveSpectrum.comap φ hf y.1, y.2⟩), by
    intro y
    obtain ⟨W, hyW, iWU, k, m, hm, t, ht, t_nin, w⟩ :=
      s.2 ⟨ProjectiveSpectrum.comap φ hf y.1, y.2⟩
    refine ⟨Proj.map φ hf ⁻¹ᵁ W, hyW, homOfLE fun z hz => iWU.le hz, k, φ m,
      map_mem_gradedTwist φ hm, φ t, map_mem φ ht,
      fun z => t_nin ⟨ProjectiveSpectrum.comap φ hf z.1, z.2⟩, fun z => ?_⟩
    exact (congrArg (twistFiber φ n _) (w ⟨_, z.2⟩)).trans (twistFiber_mk _ _ _ _ _ _ _ _ _)⟩
  map_zero' := Subtype.ext <| funext fun _ => map_zero (twistFiber φ n _)
  map_add' _ _ := Subtype.ext <| funext fun _ => map_add (twistFiber φ n _) _ _

/-- The morphism of underlying abelian presheaves. -/
def twistPresheafHom :
    (projTwistingSheaf 𝒜 n).presheaf ⟶
      ((Scheme.Modules.pushforward (Proj.map φ hf)).obj (projTwistingSheaf ℬ n)).presheaf where
  app U := AddCommGrpCat.ofHom (twistSections φ hf n U.unop)
  naturality _ _ _ := rfl

/-- **The morphism `𝒪_{Proj A}(n) ⟶ f_* 𝒪_{Proj B}(n)`** of sheaves of modules on `Proj A`
induced by a graded ring map `φ : A → B`, where `f = Proj.map φ`. -/
def twistHom :
    projTwistingSheaf 𝒜 n ⟶ (Scheme.Modules.pushforward (Proj.map φ hf)).obj
      (projTwistingSheaf ℬ n) :=
  ⟨PresheafOfModules.homMk (twistPresheafHom φ hf n) fun _ _ _ => Subtype.ext <| funext fun _ =>
    twistFiber_smul _ _ _ _ _⟩

/-- When `f = Proj.map φ` is an open immersion, the morphism `𝒪_{Proj A}(n)|_{Proj B} ⟶
𝒪_{Proj B}(n)` adjoint to `twistHom`. -/
def twistRestrictHom [IsOpenImmersion (Proj.map φ hf)] :
    (projTwistingSheaf 𝒜 n).restrict (Proj.map φ hf) ⟶ projTwistingSheaf ℬ n :=
  ((Scheme.Modules.restrictAdjunction (Proj.map φ hf)).homEquiv _ _).symm (twistHom φ hf n)

theorem twistRestrictHom_app_apply [IsOpenImmersion (Proj.map φ hf)] (W : (Proj ℬ).Opens)
    (t : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj
      (op (Proj.map φ hf ''ᵁ W))) (y : W) :
    ((twistRestrictHom φ hf n).app W t :
        (ProjGradedModuleSheaf.sheafInType ℬ (gradedTwist ℬ n)).1.obj (op W)).1 y =
      twistFiber φ n (primeCompl_le_comap φ hf y.1) (t.1 ⟨_, y.1, y.2, rfl⟩) :=
  rfl

/-! ### Localization on the degree-zero part -/

section Localization

variable {s : A} (hs : s ∈ 𝒜 0) [Algebra A B] [IsLocalization.Away s B]
  (hφ : ∀ a, φ a = algebraMap A B a)

include hs hφ in
/-- If `B = A[1/s]` with `s` of degree zero, every element of `B(n)_k` is the image of an
element of `A(n)_k` divided by a power of `s`. -/
theorem exists_mem_gradedTwist_mul_pow_eq {k : ℤ} {b : B} (hb : b ∈ gradedTwist ℬ n k) :
    ∃ a ∈ gradedTwist 𝒜 n k, ∃ i : ℕ, b * φ s ^ i = φ a := by
  by_cases hnk : n + k < 0
  · refine ⟨0, zero_mem _, 0, ?_⟩
    rw [eq_zero_of_mem_gradedTwist hb hnk, zero_mul, map_zero]
  · obtain ⟨a, ha, i, h⟩ := exists_mem_mul_pow_eq_of_isLocalizationAway φ hs hφ
      (mem_of_mem_gradedTwist hb)
    exact ⟨a, (mem_gradedTwist_of_eq (by omega)).2 ha, i, h⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
include hφ in
theorem map_notMem_of_isLocalizationAway (y : ProjectiveSpectrum ℬ) :
    φ s ∉ y.asHomogeneousIdeal := fun h =>
  y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
    (by rw [hφ s]; exact IsLocalization.Away.algebraMap_isUnit s))

include s hφ in
/-- If `B = A[1/s]` with `s` of degree zero, the fiber maps at the points of `Proj B` are
injective. -/
theorem twistFiber_injective (y : ProjectiveSpectrum ℬ) :
    Function.Injective (twistFiber φ n (primeCompl_le_comap φ hf y)) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨k, m, hm, t, ht, htx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective z
  rw [twistFiber_mk] at hz
  have e := congrArg HomogeneousLocalizedModule.val hz
  rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_zero,
    ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at e
  obtain ⟨⟨u, hu⟩, e⟩ := e
  simp only [Submonoid.smul_def, smul_eq_mul, one_mul, mul_zero, Submonoid.coe_one] at e
  obtain ⟨⟨a, ⟨_, j, rfl⟩⟩, hj⟩ := IsLocalization.surj (Submonoid.powers s) u
  simp only at hj
  have hzero : algebraMap A B (a * m) = 0 := by
    have : algebraMap A B (a * m) = u * φ m * φ (s ^ j) := by
      rw [map_mul, ← hj, ← hφ, ← hφ]; ring
    rw [this, e, zero_mul]
  obtain ⟨⟨_, i, rfl⟩, hi⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) B _).1 hzero
  have hmem : s ^ i * a ∈ (ProjectiveSpectrum.comap φ hf y).asHomogeneousIdeal.toIdeal.primeCompl
      := by
    change φ (s ^ i * a) ∉ y.asHomogeneousIdeal
    have hs' := map_notMem_of_isLocalizationAway φ (s := s) hφ y
    have ha : φ a = u * φ s ^ j := by rw [hφ, hφ, ← map_pow, hj]
    rw [map_mul, map_pow, ha]
    exact y.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (pow_mem (S := y.asHomogeneousIdeal.toIdeal.primeCompl) hs' _)
      (y.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hu
        (pow_mem (S := y.asHomogeneousIdeal.toIdeal.primeCompl) hs' _))
  ext
  rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_zero,
    ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
  refine ⟨⟨_, hmem⟩, ?_⟩
  simp only [Submonoid.smul_def, smul_eq_mul, one_mul, mul_zero, Submonoid.coe_one]
  rw [mul_assoc]
  exact hi

include hs hφ in
/-- The explicit preimage under the fiber map: if `b φ(s)^i = φ a` and `c φ(s)^j = φ c'`, the
fraction `s^j a / s^i c'` maps to `b / c`. -/
theorem twistFiber_mk_eq (y : ProjectiveSpectrum ℬ) {k : ℕ} {b c : B} {a' c'' : A}
    (hb : b ∈ gradedTwist ℬ n k) (hc : c ∈ ℬ k) (hcy : c ∉ y.asHomogeneousIdeal)
    (ha' : a' ∈ gradedTwist 𝒜 n k) (hc'' : c'' ∈ 𝒜 k) {i j : ℕ}
    (hi : b * φ s ^ i = φ a') (hj : c * φ s ^ j = φ c'') :
    ∃ (hm : s ^ j * a' ∈ gradedTwist 𝒜 n k) (ht : s ^ i * c'' ∈ 𝒜 k)
      (htx : s ^ i * c'' ∈
        (ProjectiveSpectrum.comap φ hf y).asHomogeneousIdeal.toIdeal.primeCompl),
      twistFiber φ n (primeCompl_le_comap φ hf y)
          (HomogeneousLocalizedModule.mk k (s ^ j * a') hm (s ^ i * c'') ht htx) =
        HomogeneousLocalizedModule.mk k b hb c hc hcy := by
  have hs' := map_notMem_of_isLocalizationAway φ (s := s) hφ y
  have hm : s ^ j * a' ∈ gradedTwist 𝒜 n k := by
    simpa using smul_mem_graded_nat 𝒜 (gradedTwist 𝒜 n) (SetLike.pow_mem_graded j hs) ha'
  have ht : s ^ i * c'' ∈ 𝒜 k := by
    simpa using SetLike.mul_mem_graded (SetLike.pow_mem_graded i hs) hc''
  have htx : s ^ i * c'' ∈
      (ProjectiveSpectrum.comap φ hf y).asHomogeneousIdeal.toIdeal.primeCompl := by
    change φ (s ^ i * c'') ∉ y.asHomogeneousIdeal
    rw [map_mul, map_pow, ← hj]
    exact y.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (pow_mem (S := y.asHomogeneousIdeal.toIdeal.primeCompl) hs' _)
      (y.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hcy
        (pow_mem (S := y.asHomogeneousIdeal.toIdeal.primeCompl) hs' _))
  refine ⟨hm, ht, htx, ?_⟩
  rw [twistFiber_mk]
  ext
  rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_mk,
    LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, smul_eq_mul, one_mul, Submonoid.coe_one, map_mul, map_pow,
    ← hi, ← hj]
  ring

include hs hφ in
/-- If `B = A[1/s]` with `s` of degree zero, the fiber maps at the points of `Proj B` are
surjective. -/
theorem twistFiber_surjective (y : ProjectiveSpectrum ℬ) :
    Function.Surjective (twistFiber φ n (primeCompl_le_comap φ hf y)) := by
  intro z
  obtain ⟨k, b, hb, c, hc, hcy, rfl⟩ := HomogeneousLocalizedModule.mk_surjective z
  obtain ⟨a', ha', i, hi⟩ := exists_mem_gradedTwist_mul_pow_eq φ n hs hφ hb
  obtain ⟨c'', hc'', j, hj⟩ := exists_mem_mul_pow_eq_of_isLocalizationAway φ hs hφ hc
  obtain ⟨hm, ht, htx, e⟩ := twistFiber_mk_eq φ hf n hs hφ y hb hc hcy ha' hc'' hi hj
  exact ⟨_, e⟩

/-- If `B = A[1/s]` with `s` of degree zero, the fiber map at a point `𝔮` of `Proj B` with
`𝔭 = φ⁻¹ 𝔮` is an isomorphism `A(n)_(𝔭) ≅ B(n)_(𝔮)`. -/
def fiberEquiv (x : ProjectiveSpectrum 𝒜) (y : ProjectiveSpectrum ℬ)
    (hxy : ProjectiveSpectrum.comap φ hf y = x) :
    HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 n) x.asHomogeneousIdeal.toIdeal.primeCompl ≃+
      HomogeneousLocalizedModule ℬ (gradedTwist ℬ n) y.asHomogeneousIdeal.toIdeal.primeCompl :=
  AddEquiv.ofBijective (twistFiber φ n (hxy ▸ primeCompl_le_comap φ hf y)) (by
    subst hxy
    exact ⟨twistFiber_injective φ hf n (s := s) hφ y, twistFiber_surjective φ hf n hs hφ y⟩)

theorem fiberEquiv_apply (x : ProjectiveSpectrum 𝒜) (y : ProjectiveSpectrum ℬ)
    (hxy : ProjectiveSpectrum.comap φ hf y = x)
    (z : HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 n)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    fiberEquiv φ hf n hs hφ x y hxy z = twistFiber φ n (hxy ▸ primeCompl_le_comap φ hf y) z :=
  rfl

variable [IsOpenImmersion (Proj.map φ hf)]

/-- The map on sections over `W ⊆ Proj B` of `𝒪_{Proj A}(n)|_{Proj B} ⟶ 𝒪_{Proj B}(n)`:
a section `t` over `f(W)` goes to `𝔮 ↦ t(φ⁻¹ 𝔮)`, through the fiber maps. -/
def restrictSections (W : (Proj ℬ).Opens) :
    (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj
        (op (Proj.map φ hf ''ᵁ W)) →+
      (ProjGradedModuleSheaf.sheafInType ℬ (gradedTwist ℬ n)).1.obj (op W) :=
  ((ProjGradedModuleSheaf.presheafInAb ℬ (gradedTwist ℬ n)).map
    (homOfLE ((Proj.map φ hf).preimage_image_eq W).ge).op).hom.comp
      (twistSections φ hf n (Proj.map φ hf ''ᵁ W))

omit [Algebra A B] in
theorem twistRestrictHom_app (W : (Proj ℬ).Opens) :
    (twistRestrictHom φ hf n).app W = AddCommGrpCat.ofHom (restrictSections φ hf n W) :=
  rfl

/-- The candidate preimage section: its value at `x` is the preimage under the fiber map of the
value of `t` at a point `y` over `x`. -/
def preimageValue (W : (Proj ℬ).Opens)
    (t : (ProjGradedModuleSheaf.sheafInType ℬ (gradedTwist ℬ n)).1.obj (op W))
    (x : ProjectiveSpectrum 𝒜) (y : ProjectiveSpectrum ℬ) (hy : y ∈ W)
    (hxy : ProjectiveSpectrum.comap φ hf y = x) :
    HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 n) x.asHomogeneousIdeal.toIdeal.primeCompl :=
  (fiberEquiv φ hf n hs hφ x y hxy).symm (t.1 ⟨y, hy⟩)

omit [IsOpenImmersion (Proj.map φ hf)] in
theorem preimageValue_congr (W : (Proj ℬ).Opens)
    (t : (ProjGradedModuleSheaf.sheafInType ℬ (gradedTwist ℬ n)).1.obj (op W))
    (x : ProjectiveSpectrum 𝒜) {y y' : ProjectiveSpectrum ℬ} (hy : y ∈ W) (hy' : y' ∈ W)
    (hxy : ProjectiveSpectrum.comap φ hf y = x) (hxy' : ProjectiveSpectrum.comap φ hf y' = x)
    (h : y = y') :
    preimageValue φ hf n hs hφ W t x y hy hxy = preimageValue φ hf n hs hφ W t x y' hy' hxy' := by
  subst h
  rfl

omit [Algebra A B] in
theorem exists_preimage (W : (Proj ℬ).Opens) {x : ProjectiveSpectrum 𝒜}
    (hx : x ∈ Proj.map φ hf ''ᵁ W) :
    ∃ y : ProjectiveSpectrum ℬ, y ∈ W ∧ ProjectiveSpectrum.comap φ hf y = x :=
  hx

include s hφ in
theorem restrictSections_injective (W : (Proj ℬ).Opens) :
    Function.Injective (restrictSections φ hf n W) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  apply Subtype.ext
  funext x
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := exists_preimage φ hf W hx
  have := congrArg (fun u => u.1 ⟨y, hy⟩) ht
  exact twistFiber_injective φ hf n (s := s) hφ y (this.trans (map_zero _).symm)

include hs hφ in
theorem restrictSections_surjective (W : (Proj ℬ).Opens) :
    Function.Surjective (restrictSections φ hf n W) := by
  have hinj : ∀ {y y' : ProjectiveSpectrum ℬ},
      ProjectiveSpectrum.comap φ hf y = ProjectiveSpectrum.comap φ hf y' → y = y' :=
    fun e => (Proj.map φ hf).isOpenEmbedding.injective e
  intro t
  refine ⟨⟨fun x => preimageValue φ hf n hs hφ W t x.1 (exists_preimage φ hf W x.2).choose
    (exists_preimage φ hf W x.2).choose_spec.1 (exists_preimage φ hf W x.2).choose_spec.2, ?_⟩,
    ?_⟩
  · intro x
    obtain ⟨hyW, hyx⟩ := (exists_preimage φ hf W x.2).choose_spec
    set y := (exists_preimage φ hf W x.2).choose
    obtain ⟨W', hW', iW', k, b, hb, c, hc, c_nin, w⟩ := t.2 ⟨y, hyW⟩
    obtain ⟨a', ha', i, hi⟩ := exists_mem_gradedTwist_mul_pow_eq φ n hs hφ hb
    obtain ⟨c'', hc'', j, hj⟩ := exists_mem_mul_pow_eq_of_isLocalizationAway φ hs hφ hc
    have hs' := fun z => map_notMem_of_isLocalizationAway φ (s := s) hφ z
    refine ⟨Proj.map φ hf ''ᵁ W', ⟨y, hW', hyx⟩,
      homOfLE (Scheme.Hom.image_mono _ iW'.le), k, s ^ j * a', ?_, s ^ i * c'', ?_, ?_, ?_⟩
    · simpa using smul_mem_graded_nat 𝒜 (gradedTwist 𝒜 n) (SetLike.pow_mem_graded j hs) ha'
    · simpa using SetLike.mul_mem_graded (SetLike.pow_mem_graded i hs) hc''
    · rintro ⟨_, z, hz, rfl⟩
      change φ (s ^ i * c'') ∉ z.asHomogeneousIdeal
      rw [map_mul, map_pow, ← hj]
      exact z.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
        (pow_mem (S := z.asHomogeneousIdeal.toIdeal.primeCompl) (hs' z) _)
        (z.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (c_nin ⟨z, hz⟩)
          (pow_mem (S := z.asHomogeneousIdeal.toIdeal.primeCompl) (hs' z) _))
    · rintro ⟨x', hx'⟩
      obtain ⟨z, hz, rfl⟩ := exists_preimage φ hf W' hx'
      refine (preimageValue_congr φ hf n hs hφ W t (ProjectiveSpectrum.comap φ hf z) _
        (iW'.le hz) _ rfl (hinj (exists_preimage φ hf W
          (x := ProjectiveSpectrum.comap φ hf z) ⟨z, iW'.le hz, rfl⟩).choose_spec.2)).trans ?_
      rw [preimageValue, AddEquiv.symm_apply_eq, fiberEquiv_apply]
      obtain ⟨hm, ht, htx, e⟩ :=
        twistFiber_mk_eq φ hf n hs hφ z hb hc (c_nin ⟨z, hz⟩) ha' hc'' hi hj
      exact (w ⟨z, hz⟩).trans e.symm
  · apply Subtype.ext
    funext y
    obtain ⟨y, hy⟩ := y
    change twistFiber φ n _ (preimageValue φ hf n hs hφ W t (ProjectiveSpectrum.comap φ hf y)
      _ _ _) = t.1 ⟨y, hy⟩
    rw [preimageValue_congr φ hf n hs hφ W t _ _ hy _ rfl
      (hinj (exists_preimage φ hf W (x := ProjectiveSpectrum.comap φ hf y)
        ⟨y, hy, rfl⟩).choose_spec.2), preimageValue, ← fiberEquiv_apply φ hf n hs hφ,
      AddEquiv.apply_symm_apply]
    rfl

include hs hφ in
/-- **Twisting sheaves are compatible with localization on the degree-zero part.** If
`B = A[1/s]` with `s` of degree zero, so that `f = Proj.map φ : Proj B ⟶ Proj A` is an open
immersion (onto `D₊(s)`), the morphism `𝒪_{Proj A}(n)|_{Proj B} ⟶ 𝒪_{Proj B}(n)` is an
isomorphism. -/
theorem isIso_twistRestrictHom :
    IsIso (twistRestrictHom φ hf n) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [twistRestrictHom_app, ConcreteCategory.isIso_iff_bijective]
  exact ⟨restrictSections_injective φ hf n (s := s) hφ W,
    restrictSections_surjective φ hf n hs hφ W⟩

/-- **Twisting sheaves are compatible with localization on the degree-zero part.** If
`B = A[1/s]` with `s` of degree zero and `f = Proj.map φ : Proj B ⟶ Proj A`, then
`𝒪_{Proj A}(n)|_{Proj B} ≅ 𝒪_{Proj B}(n)`. -/
def twistRestrictIso :
    (projTwistingSheaf 𝒜 n).restrict (Proj.map φ hf) ≅ projTwistingSheaf ℬ n :=
  haveI := isIso_twistRestrictHom φ hf n hs hφ
  asIso (twistRestrictHom φ hf n)

theorem twistRestrictIso_hom :
    (twistRestrictIso φ hf n hs hφ).hom = twistRestrictHom φ hf n :=
  rfl

end Localization

end ProjTwistMap

end Hartshorne
