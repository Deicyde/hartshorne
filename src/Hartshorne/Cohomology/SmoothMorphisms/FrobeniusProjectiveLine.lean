/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.ProjectiveSpaceSmooth
import Hartshorne.Scheme.Differentials.RelativeDifferentialsFibreRank
import Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity
import Hartshorne.Weil.FiniteFieldFrobenius
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Frobenius on the projective line is nowhere smooth

Hartshorne, *Algebraic Geometry*, III.10, Example 10.5.1 (p. 272).

Let `k` be an algebraically closed field of characteristic `p > 0`, and let
`F : ℙ¹_k ⟶ ℙ¹_k` be the Frobenius morphism, here the absolute Frobenius: the identity on points
and `s ↦ s ^ p` on local sections. Since `k` is perfect, it differs from the `k`-linear Frobenius
only by an automorphism of the scheme `ℙ¹_k`, which does not affect any of the properties below.

* Every scheme-theoretic fibre of `F` is a single point, so `F` has relative dimension zero.
* The first map `F^*Ω_{ℙ¹/ℤ} ⟶ Ω_{ℙ¹/ℤ}` of the transitivity sequence is zero, since
  `d(a ^ p) = p a ^ (p - 1) da = 0`.
* Hence `Ω_{ℙ¹/ℤ} ⟶ Ω_{ℙ¹/F}` is an isomorphism; as `k` is perfect, the same argument for
  `ℙ¹_k ⟶ Spec k ⟶ Spec ℤ` identifies `Ω_{ℙ¹/ℤ}` with `Ω_{ℙ¹_k/k}`, which is locally free of
  rank one because `ℙ¹_k` is smooth of relative dimension one over `k`.
* `F` is smooth on no nonempty open: on affine charts `A → B` of a smooth restriction, the map
  `B ⊗_A Ω_{A/ℤ} ⟶ Ω_{B/ℤ}` would be injective (as `H₁(L_{B/A}) = 0`), but it is zero, while its
  source surjects onto `B` because `Ω_{A/k}` is free of rank one on a standard smooth chart.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace PresheafOfModules.Derivation

variable {C : Type*} [Category C] {D : Type*} [Category D]
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {φ : S ⟶ F.op ⋙ R}

/-- The Leibniz rule for powers: `d(a ^ (n + 1)) = (n + 1) a ^ n · d a`. -/
theorem d_pow_succ (d : M.Derivation φ) {X : Dᵒᵖ} (a : R.obj X) (n : ℕ) :
    d.d (a ^ (n + 1)) = (((n + 1 : ℕ) : R.obj X) * a ^ n) • d.d a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, d.d_mul, ih, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- A derivation kills `p`-th powers where the prime `p` vanishes. -/
theorem d_pow_eq_zero (d : M.Derivation φ) {X : Dᵒᵖ} (a : R.obj X) {p : ℕ} [Fact p.Prime]
    (hp : ((p : ℕ) : R.obj X) = 0) : d.d (a ^ p) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 :=
    ⟨p - 1, (Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos).symm⟩
  rw [d_pow_succ, hp, zero_mul, zero_smul]

end PresheafOfModules.Derivation

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- If `d_{X/Z}` kills `f^♯ b` for every local section `b` of `𝒪_Y`, then the first map
`f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` of the transitivity sequence vanishes. -/
theorem pullbackRelativeDifferentialsToComp_eq_zero_of_d (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : ∀ (V : Y.Opensᵒᵖ) (b : Y.presheaf.obj V),
      (relativeDifferentialsDerivation (f ≫ g)).d (f.c.app V b) = 0) :
    pullbackRelativeDifferentialsToComp f g = 0 := by
  apply ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [pullbackRelativeDifferentialsToComp_homEquiv, Adjunction.homEquiv_unit, Functor.map_zero,
    comp_zero]
  apply (relativeDifferentialsHomEquiv g _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext V b
  change (relativeDifferentialsToPushforwardComp f g).val.app V
    ((relativeDifferentialsDerivation g).d b) = 0
  exact (relativeDifferentialsToPushforwardComp_d f g V b).trans (h V b)

/-- When the first map of the transitivity sequence vanishes, `Ω_{X/Z} ⟶ Ω_{X/Y}` is an
isomorphism. -/
theorem isIso_relativeDifferentialsCompToLeft_of_eq_zero (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : pullbackRelativeDifferentialsToComp f g = 0) :
    IsIso (relativeDifferentialsCompToLeft f g) := by
  let hc := relativeDifferentialsTransitivityIsColimit f g
  let inv : relativeDifferentials f ⟶ relativeDifferentials (f ≫ g) :=
    hc.desc (CokernelCofork.ofπ (𝟙 _) (by rw [h, zero_comp]))
  have h₁ : relativeDifferentialsCompToLeft f g ≫ inv = 𝟙 _ :=
    hc.fac (CokernelCofork.ofπ (𝟙 _) (by rw [h, zero_comp])) WalkingParallelPair.one
  refine ⟨inv, h₁, ?_⟩
  apply Cofork.IsColimit.hom_ext hc
  change relativeDifferentialsCompToLeft f g ≫ inv ≫ relativeDifferentialsCompToLeft f g =
    relativeDifferentialsCompToLeft f g ≫ 𝟙 _
  rw [← Category.assoc, h₁, Category.id_comp, Category.comp_id]

/-- Locally free of rank `r` is invariant under isomorphism of module sheaves. -/
theorem Modules.isLocallyFreeOfRank_of_iso {M N : X.Modules} (e : M ≅ N) {r : ℕ}
    (h : M.IsLocallyFreeOfRank r) : N.IsLocallyFreeOfRank r := by
  intro x
  obtain ⟨U, hx, ⟨e'⟩⟩ := h x
  exact ⟨U, hx, ⟨(Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ e'⟩⟩

/-- On a scheme over a field of characteristic `p`, the integer `p` vanishes in every ring of
sections. -/
theorem natCast_eq_zero_of_hom_spec {K : Type u} [Field K] {p : ℕ} [CharP K p]
    (s : X ⟶ Spec (.of K)) (U : X.Opens) : ((p : ℕ) : Γ(X, U)) = 0 := by
  have := map_natCast ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)) p
  rw [CharP.cast_eq_zero, map_zero] at this
  exact this.symm

/-- A relative derivation kills `p`-th powers on an open where `p` vanishes. -/
theorem relativeDifferentialsDerivation_d_pow_eq_zero (k : X ⟶ Z) {p : ℕ} [Fact p.Prime]
    {U : X.Opensᵒᵖ} (hp : ((p : ℕ) : Γ(X, U.unop)) = 0) (a : Γ(X, U.unop)) :
    (relativeDifferentialsDerivation k).d (a ^ p) = 0 := by
  exact PresheafOfModules.Derivation.d_pow_eq_zero (relativeDifferentialsDerivation k)
    (X := U) a hp

/-- Every local section of the structure sheaf of the spectrum of a perfect field of
characteristic `p` is a `p`-th power. -/
theorem exists_pow_eq_of_spec_perfectRing (K : Type u) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectRing K p] (V : (Spec (.of K)).Opens) (b : Γ(Spec (.of K), V)) :
    ∃ c, b = c ^ p := by
  by_cases hV : V = ⊥
  · subst hV
    exact ⟨0, Subsingleton.elim _ _⟩
  · have hV' : V = ⊤ := by
      obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty V).mp hV
      ext y
      simp only [Opens.coe_top, Set.mem_univ, iff_true]
      rwa [Subsingleton.elim y x]
    subst hV'
    obtain ⟨c, hc⟩ := surjective_frobenius K p ((Scheme.ΓSpecIso (.of K)).hom b)
    refine ⟨(Scheme.ΓSpecIso (.of K)).inv c, ?_⟩
    rw [← map_pow, ← frobenius_def, hc]
    exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of K)).hom_inv_id b).symm

end AlgebraicGeometry.Scheme

namespace Hartshorne

open AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct

/-- A nonempty subsingleton space has topological Krull dimension zero. -/
theorem topologicalKrullDim_eq_zero_of_subsingleton (T : Type*) [TopologicalSpace T]
    [Subsingleton T] [Nonempty T] : topologicalKrullDim T = 0 := by
  refine le_antisymm (topologicalKrullDim_zero_of_discreteTopology T) ?_
  obtain ⟨x⟩ := ‹Nonempty T›
  have : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

/-- Every scheme-theoretic fibre of the absolute Frobenius is a single point, hence has
dimension zero. -/
theorem absoluteFrobenius_fiber_topologicalKrullDim (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    [X.IsCharP p] (y : X) : topologicalKrullDim ((X.absoluteFrobenius p).fiber y) = 0 := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ ((X.absoluteFrobenius p).fiberHomeo y).isHomeomorph]
  have : Subsingleton ((X.absoluteFrobenius p) ⁻¹' {y}) :=
    ⟨fun a b => Subtype.ext (by
      have ha : X.absoluteFrobenius p a = y := a.2
      have hb : X.absoluteFrobenius p b = y := b.2
      rw [absoluteFrobenius_apply] at ha hb
      rw [ha, hb])⟩
  have : Nonempty ((X.absoluteFrobenius p) ⁻¹' {y}) :=
    ⟨⟨y, by simp⟩⟩
  exact topologicalKrullDim_eq_zero_of_subsingleton _

/-- If `A → B` is formally smooth, `B ≠ 0`, every `d(φ a)` vanishes in `Ω_{B/ℤ}`, and `Ω_{A/ℤ}`
surjects onto `A`, we have a contradiction: `B ⊗_A Ω_{A/ℤ} → Ω_{B/ℤ}` is injective, but it is
zero and its source surjects onto `B`. -/
theorem false_of_formallySmooth_of_kaehlerD_algebraMap_eq_zero {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [Nontrivial B] [Algebra.FormallySmooth A B]
    (hD : ∀ a : A, KaehlerDifferential.D ℤ B (algebraMap A B a) = 0)
    (c : Ω[A⁄ℤ] →ₗ[A] A) (hc : Function.Surjective c) : False := by
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange ℤ A B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange ℤ A B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hmap : KaehlerDifferential.map ℤ ℤ A B = 0 :=
    Derivation.liftKaehlerDifferential_unique _ _ (by ext a; simp [hD])
  have hzero : ∀ x : B ⊗[A] Ω[A⁄ℤ], x = 0 := by
    intro x
    apply hinj
    rw [map_zero]
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul b ω => rw [KaehlerDifferential.mapBaseChange_tmul, hmap, LinearMap.zero_apply,
        smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  obtain ⟨ω, hω⟩ := hc 1
  have h := congrArg (LinearMap.liftBaseChange B ((Algebra.linearMap A B) ∘ₗ c))
    (hzero ((1 : B) ⊗ₜ ω))
  rw [LinearMap.liftBaseChange_tmul, map_zero, LinearMap.comp_apply, hω,
    Algebra.linearMap_apply, map_one, one_smul] at h
  exact one_ne_zero h

section Frobenius

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

instance isCharP_projectiveSpaceOverScheme_spec (n : ℕ) :
    (projectiveSpaceOverScheme n (Spec (.of k))).IsCharP p :=
  isCharP_of_hom_spec (projectiveSpaceOverSchemeProjection n (Spec (.of k)))

/-- The absolute Frobenius acts on the absolute differentials of `ℙⁿ_k` by zero: the first map
`F^*Ω_{ℙⁿ/ℤ} ⟶ Ω_{ℙⁿ/ℤ}` of the transitivity sequence vanishes, since `d(a ^ p) = 0`. -/
theorem pullbackRelativeDifferentialsToComp_absoluteFrobenius_eq_zero (n : ℕ) :
    pullbackRelativeDifferentialsToComp
      ((projectiveSpaceOverScheme n (Spec (.of k))).absoluteFrobenius p)
      (schemeToSpecZ (projectiveSpaceOverScheme n (Spec (.of k)))) = 0 := by
  apply pullbackRelativeDifferentialsToComp_eq_zero_of_d
  intro V b
  exact relativeDifferentialsDerivation_d_pow_eq_zero _
    (natCast_eq_zero_of_hom_spec (projectiveSpaceOverSchemeProjection n (Spec (.of k))) _) b

/-- Over a perfect field, the absolute differentials of `ℙⁿ_k` are its differentials over `k`:
the first map of the transitivity sequence for `ℙⁿ_k ⟶ Spec k ⟶ Spec ℤ` vanishes. -/
theorem pullbackRelativeDifferentialsToComp_projection_eq_zero [PerfectRing k p] (n : ℕ) :
    pullbackRelativeDifferentialsToComp (projectiveSpaceOverSchemeProjection n (Spec (.of k)))
      (schemeToSpecZ (Spec (.of k))) = 0 := by
  apply pullbackRelativeDifferentialsToComp_eq_zero_of_d
  intro V b
  obtain ⟨c, rfl⟩ := exists_pow_eq_of_spec_perfectRing k p V.unop b
  rw [map_pow]
  exact relativeDifferentialsDerivation_d_pow_eq_zero _
    (natCast_eq_zero_of_hom_spec (projectiveSpaceOverSchemeProjection n (Spec (.of k))) _) _

/-- The relative differential sheaf of the absolute Frobenius of `ℙⁿ_k` over a perfect field is
isomorphic to `Ω_{ℙⁿ_k/k}`. -/
def relativeDifferentialsAbsoluteFrobeniusIso [PerfectRing k p] (n : ℕ) :
    relativeDifferentials ((projectiveSpaceOverScheme n (Spec (.of k))).absoluteFrobenius p) ≅
      relativeDifferentials (projectiveSpaceOverSchemeProjection n (Spec (.of k))) :=
  have := isIso_relativeDifferentialsCompToLeft_of_eq_zero _ _
    (pullbackRelativeDifferentialsToComp_absoluteFrobenius_eq_zero k p n)
  have := isIso_relativeDifferentialsCompToLeft_of_eq_zero _ _
    (pullbackRelativeDifferentialsToComp_projection_eq_zero k p n)
  (asIso (relativeDifferentialsCompToLeft
      ((projectiveSpaceOverScheme n (Spec (.of k))).absoluteFrobenius p)
      (schemeToSpecZ (projectiveSpaceOverScheme n (Spec (.of k)))))).symm ≪≫
    relativeDifferentialsCongr (specULiftZIsTerminal.hom_ext _ _) ≪≫
    asIso (relativeDifferentialsCompToLeft (projectiveSpaceOverSchemeProjection n (Spec (.of k)))
      (schemeToSpecZ (Spec (.of k))))

/-- The relative differential sheaf of the absolute Frobenius of `ℙ¹_k` over a perfect field is
locally free of rank one. -/
theorem relativeDifferentials_absoluteFrobenius_isLocallyFreeOfRank_one [PerfectRing k p] :
    (relativeDifferentials
      ((projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p)).IsLocallyFreeOfRank 1 :=
  have := projectiveSpaceOverSchemeProjection_smoothOfRelativeDimension 1 (Spec (.of k))
  Modules.isLocallyFreeOfRank_of_iso (relativeDifferentialsAbsoluteFrobeniusIso k p 1).symm
    (relativeDifferentials_isLocallyFreeOfRank_of_smoothOfRelativeDimension _ 1)

/-- The absolute Frobenius of `ℙ¹_k` is smooth on no nonempty open subset. -/
theorem absoluteFrobenius_not_smooth_on_open
    (U : (projectiveSpaceOverScheme 1 (Spec (.of k))).Opens)
    (hU : (U : Set (projectiveSpaceOverScheme 1 (Spec (.of k)))).Nonempty) :
    ¬ Smooth (U.ι ≫ (projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p) := by
  intro hs
  obtain ⟨x, hx⟩ := hU
  let P := projectiveSpaceOverScheme 1 (Spec (.of k))
  let π := projectiveSpaceOverSchemeProjection 1 (Spec (.of k))
  let F := P.absoluteFrobenius p
  -- A standard smooth chart of `ℙ¹_k ⟶ Spec k` at `x`: `Ω_{A/R₀}` is free of rank one.
  have := projectiveSpaceOverSchemeProjection_smoothOfRelativeDimension 1 (Spec (.of k))
  obtain ⟨U₀, hU₀, V₀, hV₀, hxV₀, e₀, hf₀⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := π) x
  let := (π.appLE U₀ V₀ e₀).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Spec (.of k), U₀) Γ(P, V₀) := hf₀
  have : Algebra.IsStandardSmooth Γ(Spec (.of k), U₀) Γ(P, V₀) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have : Nonempty V₀ := ⟨⟨x, hxV₀⟩⟩
  have hrank := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Spec (.of k), U₀)) (S := Γ(P, V₀)) 1
  let b := Module.Free.chooseBasis Γ(P, V₀) Ω[Γ(P, V₀)⁄Γ(Spec (.of k), U₀)]
  have hne : Nonempty (Module.Free.ChooseBasisIndex Γ(P, V₀)
      Ω[Γ(P, V₀)⁄Γ(Spec (.of k), U₀)]) := by
    rw [← Cardinal.mk_ne_zero_iff, b.mk_eq_rank'', hrank]
    simp
  obtain ⟨i⟩ := hne
  let c : Ω[Γ(P, V₀)⁄ℤ] →ₗ[Γ(P, V₀)] Γ(P, V₀) :=
    b.coord i ∘ₗ KaehlerDifferential.map ℤ Γ(Spec (.of k), U₀) Γ(P, V₀) Γ(P, V₀)
  have hc : Function.Surjective c := by
    intro a
    obtain ⟨ω, hω⟩ := KaehlerDifferential.map_surjective ℤ Γ(Spec (.of k), U₀) Γ(P, V₀)
      (a • b i)
    refine ⟨ω, ?_⟩
    simp [c, hω]
  -- An affine open `W` of `U` around `x` mapping into `V₀`.
  have hxpre : (⟨x, hx⟩ : U) ∈ (U.ι ≫ F) ⁻¹ᵁ V₀ := hxV₀
  obtain ⟨W, hW, hxW, hWle⟩ :=
    (Opens.isBasis_iff_nbhd.mp (U : Scheme).isBasis_affineOpens) hxpre
  have : Nonempty W := ⟨⟨_, hxW⟩⟩
  have hsm := HasRingHomProperty.appLE (P := @Smooth) (U.ι ≫ F) hs ⟨V₀, hV₀⟩ ⟨W, hW⟩ hWle
  let φ := (U.ι ≫ F).appLE V₀ W hWle
  let := φ.hom.toAlgebra
  have : Algebra.Smooth Γ(P, V₀) Γ(U, W) := hsm
  refine false_of_formallySmooth_of_kaehlerD_algebraMap_eq_zero (A := Γ(P, V₀))
    (B := Γ(U, W)) (fun a => ?_) c hc
  have hp : ((p : ℕ) : Γ(U, W)) = 0 := natCast_eq_zero_of_hom_spec (U.ι ≫ π) W
  change KaehlerDifferential.D ℤ Γ(U, W) (φ a) = 0
  have hφ : φ a = (U.ι.appLE (F ⁻¹ᵁ V₀) W hWle a) ^ p := by
    simp only [φ, Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
    exact map_pow _ _ _
  rw [hφ, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul Γ(U, W), hp, zero_smul]

end Frobenius

/-- **Hartshorne III, Example 10.5.1.** Let `k` be an algebraically closed field of
characteristic `p > 0` and let `F : ℙ¹_k ⟶ ℙ¹_k` be the Frobenius morphism. Then
1. `F` has relative dimension zero: every scheme-theoretic fibre has dimension zero;
2. `F` is smooth on no nonempty open subset of `ℙ¹_k`;
3. the map `F^*Ω_{ℙ¹} ⟶ Ω_{ℙ¹}` on absolute differentials is zero; and
4. the relative differential sheaf `Ω_{ℙ¹/F}` is locally free of rank one. -/
theorem frobenius_projectiveLine_nowhere_smooth (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    (∀ y : projectiveSpaceOverScheme 1 (Spec (.of k)), topologicalKrullDim
        (((projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p).fiber y) = 0) ∧
    (∀ U : (projectiveSpaceOverScheme 1 (Spec (.of k))).Opens,
      (U : Set (projectiveSpaceOverScheme 1 (Spec (.of k)))).Nonempty →
        ¬ Smooth (U.ι ≫ (projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p)) ∧
    pullbackRelativeDifferentialsToComp
        ((projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p)
        (schemeToSpecZ (projectiveSpaceOverScheme 1 (Spec (.of k)))) = 0 ∧
    (relativeDifferentials
      ((projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p)).IsLocallyFreeOfRank 1 :=
  ⟨absoluteFrobenius_fiber_topologicalKrullDim _ p, absoluteFrobenius_not_smooth_on_open k p,
    pullbackRelativeDifferentialsToComp_absoluteFrobenius_eq_zero k p 1,
    relativeDifferentials_absoluteFrobenius_isLocallyFreeOfRank_one k p⟩

end Hartshorne
