/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.ProjectiveSpaceSmooth
import Hartshorne.Scheme.Differentials.RelativeDifferentialsFibreRank
import Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity
import Hartshorne.Scheme.Regular
import Hartshorne.Weil.FiniteFieldFrobenius
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Frobenius on the projective line is nowhere smooth

Hartshorne, *Algebraic Geometry*, III.10, Example 10.5.1 (p. 272) and Remark 10.9.3 (p. 275).

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
* The pullback of a closed point `P` (a hyperplane of `ℙ¹_k`), the scheme-theoretic fibre over
  `P`, is nonreduced: on an affine chart `A` around `P` with maximal ideal `q` it is
  `Spec (κ(q) ⊗_{A,F} A)`, in which `1 ⊗ t` is nilpotent and nonzero for any `t ∈ q` outside
  `q² A_q`; such a `t` exists because some derivation of `A` does not preserve `q`. A regular
  scheme with one point is reduced, so these fibres are not regular either.
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

/-- Every scheme-theoretic fibre of the absolute Frobenius has at most one point. -/
instance absoluteFrobenius_fiber_subsingleton (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    [X.IsCharP p] (y : X) : Subsingleton ((X.absoluteFrobenius p).fiber y) := by
  have : Subsingleton ((X.absoluteFrobenius p) ⁻¹' {y}) :=
    ⟨fun a b => Subtype.ext (by
      have ha : X.absoluteFrobenius p a = y := a.2
      have hb : X.absoluteFrobenius p b = y := b.2
      rw [absoluteFrobenius_apply] at ha hb
      rw [ha, hb])⟩
  exact ((X.absoluteFrobenius p).fiberHomeo y).injective.subsingleton

/-- Every scheme-theoretic fibre of the absolute Frobenius is a single point, hence has
dimension zero. -/
theorem absoluteFrobenius_fiber_topologicalKrullDim (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    [X.IsCharP p] (y : X) : topologicalKrullDim ((X.absoluteFrobenius p).fiber y) = 0 := by
  have : Nonempty ((X.absoluteFrobenius p).fiber y) :=
    ⟨((X.absoluteFrobenius p).fiberHomeo y).symm ⟨y, by simp⟩⟩
  exact topologicalKrullDim_eq_zero_of_subsingleton _

/-- A regular scheme with at most one point is reduced: its local rings have dimension zero, so
regularity forces their maximal ideals to vanish. -/
theorem isReduced_of_isRegular_of_subsingleton (X : Scheme.{u}) [Subsingleton X]
    (h : X.IsRegular) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    have hreg : IsRegularLocalRing (X.presheaf.stalk x) := h.2 x
    have hsub : Subsingleton (PrimeSpectrum (X.presheaf.stalk x)) :=
      ⟨fun a b => (X.fromSpecStalk x).isEmbedding.injective (Subsingleton.elim _ _)⟩
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := Ring.krullDimLE_zero_iff.mpr fun I hI => by
      have hI' : (⟨I, hI⟩ : PrimeSpectrum _) =
          ⟨IsLocalRing.maximalIdeal _, inferInstance⟩ := Subsingleton.elim _ _
      rw [show I = IsLocalRing.maximalIdeal _ from congrArg PrimeSpectrum.asIdeal hI']
      exact IsLocalRing.maximalIdeal.isMaximal _
    have hdim : ringKrullDim (X.presheaf.stalk x) = 0 :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mp this
    have hspan := hreg.spanFinrank_maximalIdeal
    rw [hdim] at hspan
    have h0 : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank = 0 := by
      exact_mod_cast hspan
    have hbot := (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0
    let := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot).toField
    infer_instance
  exact isReduced_of_isReduced_stalk X

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

/-- A tensor product `K ⊗_R S` containing `1 ⊗ s` with `s ^ n` the image of an element killed
in `K` is nonreduced, provided some pair of compatible maps to a ring `C` does not kill `s`. -/
theorem not_isReduced_tensor_of_pow_eq_algebraMap {R K S C : Type*} [CommRing R] [CommRing K]
    [CommRing S] [CommRing C] [Algebra R K] [Algebra R S] (ψ : K →+* C) (σ : S →+* C)
    (hcomm : ∀ r, ψ (algebraMap R K r) = σ (algebraMap R S r)) {n : ℕ} (s : S) (t : R)
    (hst : algebraMap R S t = s ^ n) (ht : algebraMap R K t = 0) (hs : σ s ≠ 0) :
    ¬ IsReduced (K ⊗[R] S) := by
  intro hred
  let : Algebra R C := (ψ.comp (algebraMap R K)).toAlgebra
  let ψ' : K →ₐ[R] C := { ψ with commutes' := fun r => rfl }
  let σ' : S →ₐ[R] C := { σ with commutes' := fun r => (hcomm r).symm }
  have hnil : IsNilpotent ((1 : K) ⊗ₜ[R] s) := ⟨n, by
    rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hst, Algebra.algebraMap_eq_smul_one,
      ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, ht, TensorProduct.zero_tmul]⟩
  have h0 := congrArg (Algebra.TensorProduct.lift ψ' σ' (fun _ _ => Commute.all _ _))
    (hred.eq_zero _ hnil)
  rw [Algebra.TensorProduct.lift_tmul, map_zero, map_one, one_mul] at h0
  exact hs h0

/-- Let `R` have characteristic `p`, let `q` be a prime of `R`, and let `S` be an `R`-algebra with
a ring map `ρ : S → R` turning the structure map into the Frobenius. If `t ∈ q` is the image of
`s ∈ S` with `s ^ p` the image of `t`, and `t ∉ q² R_q`, then the fibre ring `κ(q) ⊗_R S` is
nonreduced. -/
theorem not_isReduced_residueField_tensor_of_frobenius {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {p : ℕ} [hp' : Fact p.Prime] (hp : ((p : ℕ) : R) = 0) (q : Ideal R) [q.IsPrime]
    (ρ : S →+* R) (hρ : ∀ r, ρ (algebraMap R S r) = r ^ p) (s : S) (t : R)
    (hst : algebraMap R S t = s ^ p) (hs : ρ s = t) (htq : t ∈ q)
    (ht : algebraMap R (Localization.AtPrime q) t ∉
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ 2) :
    ¬ IsReduced (q.ResidueField ⊗[R] S) := by
  let L := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal L
  have hm2 : m ^ 2 ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal L).ne_top
    (eq_top_iff.mpr (h.symm.le.trans (Ideal.pow_le_self two_ne_zero)))
  have : Nontrivial (L ⧸ m ^ 2) := Ideal.Quotient.nontrivial_iff.mpr hm2
  have hpC : ((p : ℕ) : L ⧸ m ^ 2) = 0 := by
    rw [← map_natCast ((Ideal.Quotient.mk (m ^ 2)).comp (algebraMap R L)), hp, map_zero]
  have : CharP (L ⧸ m ^ 2) p := (CharP.charP_iff_prime_eq_zero hp'.out).mpr hpC
  have : ExpChar (L ⧸ m ^ 2) p := ExpChar.prime hp'.out
  let ψ : q.ResidueField →+* L ⧸ m ^ 2 :=
    Ideal.Quotient.lift m ((frobenius (L ⧸ m ^ 2) p).comp (Ideal.Quotient.mk (m ^ 2)))
      (fun x hx => by
        obtain ⟨n, hn⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := hp'.out.two_le; omega⟩
        rw [RingHom.comp_apply, frobenius_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, hn,
          pow_add]
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hx 2))
  let σ : S →+* L ⧸ m ^ 2 := (Ideal.Quotient.mk (m ^ 2)).comp ((algebraMap R L).comp ρ)
  refine not_isReduced_tensor_of_pow_eq_algebraMap ψ σ (fun r => ?_) s t hst
    (Ideal.algebraMap_residueField_eq_zero.mpr htq) ?_
  · rw [IsScalarTower.algebraMap_apply R L, IsLocalRing.ResidueField.algebraMap_eq]
    change Ideal.Quotient.lift m _ _ (Ideal.Quotient.mk m _) = _
    rw [Ideal.Quotient.lift_mk]
    simp only [σ, RingHom.comp_apply, hρ, map_pow, frobenius_def]
  · simp only [σ, RingHom.comp_apply, hs, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact ht

/-- If a derivation `D` of `R` does not send `t ∈ q` into the prime `q`, then `t` does not lie in
the square of the maximal ideal of `R_q`. -/
theorem algebraMap_not_mem_maximalIdeal_sq_of_derivation {R : Type*} [CommRing R] (q : Ideal R)
    [q.IsPrime] (D : Derivation ℤ R R) (t : R) (htq : t ∈ q) (hDt : D t ∉ q) :
    algebraMap R (Localization.AtPrime q) t ∉
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ 2 := by
  have hDq : ∀ z ∈ q ^ 2, D z ∈ q := by
    intro z hz
    rw [sq] at hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact q.add_mem (q.mul_mem_right _ ha) (q.mul_mem_right _ hb)
    · rw [map_add]
      exact q.add_mem hx hy
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  intro h
  obtain ⟨⟨x, u⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff q.primeCompl _).mp h
  simp only at hx
  rw [← map_mul, IsLocalization.eq_iff_exists q.primeCompl] at hx
  obtain ⟨c, hc⟩ := hx
  have hmem : ((c : R) * u) * t ∈ q ^ 2 := by
    rw [show (c : R) * u * t = c * (t * u) by ring, hc]
    exact Ideal.mul_mem_left _ _ x.2
  have hD := hDq _ hmem
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hD
  have h1 : (c : R) * u * D t ∈ q := by
    have := q.sub_mem hD (q.mul_mem_right (D ((c : R) * u)) htq)
    rwa [add_sub_cancel_right] at this
  rcases Ideal.IsPrime.mem_or_mem ‹_› h1 with h2 | h2
  · exact (q.primeCompl.mul_mem c.2 u.2) h2
  · exact hDt h2

/-- A morphism that is smooth of positive relative dimension has, around every point, an affine
open `V` such that `Ω_{Γ(V)/ℤ}` surjects linearly onto `Γ(V)`: on a standard smooth chart
`Ω_{Γ(V)/Γ(U)}` is free of positive rank. -/
theorem exists_affineOpen_kaehlerDifferential_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) f] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      ∃ c : Ω[Γ(X, V)⁄ℤ] →ₗ[Γ(X, V)] Γ(X, V), Function.Surjective c := by
  obtain ⟨U₀, hU₀, V₀, hV₀, hxV₀, e₀, hf₀⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n + 1) (f := f) x
  let := (f.appLE U₀ V₀ e₀).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension (n + 1) Γ(Y, U₀) Γ(X, V₀) := hf₀
  have : Algebra.IsStandardSmooth Γ(Y, U₀) Γ(X, V₀) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n + 1)
  have : Nonempty V₀ := ⟨⟨x, hxV₀⟩⟩
  have hrank := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U₀)) (S := Γ(X, V₀)) (n + 1)
  let b := Module.Free.chooseBasis Γ(X, V₀) Ω[Γ(X, V₀)⁄Γ(Y, U₀)]
  have hne : Nonempty (Module.Free.ChooseBasisIndex Γ(X, V₀) Ω[Γ(X, V₀)⁄Γ(Y, U₀)]) := by
    rw [← Cardinal.mk_ne_zero_iff, b.mk_eq_rank'', hrank]
    exact_mod_cast Nat.succ_ne_zero n
  obtain ⟨i⟩ := hne
  refine ⟨V₀, hV₀, hxV₀, b.coord i ∘ₗ KaehlerDifferential.map ℤ Γ(Y, U₀) Γ(X, V₀) Γ(X, V₀),
    fun a => ?_⟩
  obtain ⟨ω, hω⟩ := KaehlerDifferential.map_surjective ℤ Γ(Y, U₀) Γ(X, V₀) (a • b i)
  exact ⟨ω, by simp [hω]⟩

/-- In a pullback square whose bottom map is an isomorphism, the top-left corner is reduced
when the top-right corner is. -/
theorem isReduced_of_isPullback_of_isIso {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [IsIso g] [IsReduced X] :
    IsReduced P := by
  have := h.isIso_fst_of_isIso
  exact isReduced_of_isOpenImmersion fst

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
  have := projectiveSpaceOverSchemeProjection_smoothOfRelativeDimension 1 (Spec (.of k))
  obtain ⟨V₀, hV₀, hxV₀, c, hc⟩ := exists_affineOpen_kaehlerDifferential_surjective π 0 x
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

/-- The pullback under the absolute Frobenius of `ℙ¹_k` of a closed point, that is, the
scheme-theoretic fibre over it, is nonreduced. -/
theorem absoluteFrobenius_fiber_not_isReduced [IsAlgClosed k]
    (y : projectiveSpaceOverScheme 1 (Spec (.of k))) (hy : IsClosed {y}) :
    ¬ IsReduced (((projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p).fiber y) := by
  let P := projectiveSpaceOverScheme 1 (Spec (.of k))
  let π := projectiveSpaceOverSchemeProjection 1 (Spec (.of k))
  let F := P.absoluteFrobenius p
  have := projectiveSpaceOverSchemeProjection_smoothOfRelativeDimension 1 (Spec (.of k))
  obtain ⟨V, hV, hyV, c, hc⟩ := exists_affineOpen_kaehlerDifferential_surjective π 0 y
  let R := Γ(P, V)
  let y' := hV.primeIdealOf ⟨y, hyV⟩
  let q := y'.asIdeal
  have hqmax : q.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hyV⟩ hy
  have hp : ((p : ℕ) : R) = 0 := natCast_eq_zero_of_hom_spec π V
  -- A derivation `D` of `R` with `D a ∉ q`.
  let D : Derivation ℤ R R := c.compDer (KaehlerDifferential.D ℤ R)
  obtain ⟨a, ha⟩ : ∃ a, D a ∉ q := by
    by_contra! h
    obtain ⟨ω, hω⟩ := hc 1
    have hcq : ∀ ω, c ω ∈ q := by
      intro ω
      have hω' : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D ℤ R)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hω' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        exact h b
      | zero => rw [map_zero]; exact q.zero_mem
      | add x y _ _ hx hy => rw [map_add]; exact q.add_mem hx hy
      | smul r x _ hx => rw [map_smul, smul_eq_mul]; exact q.mul_mem_left r hx
    exact hqmax.ne_top ((Ideal.eq_top_iff_one q).mpr (hω ▸ hcq ω))
  -- The residue field at `q` is `k`, hence perfect.
  have hclosed : IsClosed {y'} := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y').mpr hqmax
  have : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  let e : q.ResidueField ≃+* k := ((Spec.residueFieldIso (.of R) y').symm ≪≫
      residueFieldIsoBase (hV.fromSpec ≫ π) y' hclosed).commRingCatIsoToRingEquiv
  obtain ⟨μ, hμ⟩ : ∃ μ : R, a - μ ^ p ∈ q := by
    obtain ⟨c₀, hc₀⟩ := surjective_frobenius k p (e (algebraMap R q.ResidueField a))
    obtain ⟨μ, hμ⟩ := Ideal.algebraMap_residueField_surjective q (e.symm c₀)
    refine ⟨μ, Ideal.algebraMap_residueField_eq_zero.mp ?_⟩
    rw [map_sub, map_pow, hμ, ← map_pow, ← frobenius_def, hc₀, RingEquiv.symm_apply_apply,
      sub_self]
  have hDt : D (a - μ ^ p) ∉ q := by
    rwa [map_sub, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul R, hp, zero_smul, sub_zero]
  have ht := algebraMap_not_mem_maximalIdeal_sq_of_derivation q D _ hμ hDt
  -- The fibre over `y` is the fibre of `Spec Γ(F⁻¹V) ⟶ Spec Γ(V)` over `q`.
  let V' := F ⁻¹ᵁ V
  have hV' : IsAffineOpen V' := hV
  let φ := F.appLE V V' le_rfl
  have hsq : IsPullback hV'.fromSpec (Spec.map φ) F hV.fromSpec :=
    (IsOpenImmersion.isPullback _ _ _ _ (IsAffineOpen.SpecMap_appLE_fromSpec F hV hV' le_rfl).symm
      (by rw [hV.opensRange_fromSpec, hV'.opensRange_fromSpec])).flip
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback hsq y'
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have : IsIso (hV.fromSpec.residueFieldMap y') :=
    instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion hV.fromSpec y'
  have : IsIso (Spec.map (hV.fromSpec.residueFieldMap y')) :=
    (Scheme.Spec.mapIso (asIso (hV.fromSpec.residueFieldMap y')).op).isIso_hom
  have hy' : hV.fromSpec y' = y := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
  rw [← hy']
  intro hred
  have hred₁ : IsReduced ((Spec.map φ).fiber y') :=
    @isReduced_of_isPullback_of_isIso _ _ _ _ _ _ _ _ hpb _ hred
  let : Algebra R Γ(P, V') := φ.hom.toAlgebra
  let E := Spec.fiberToSpecResidueFieldIso R Γ(P, V') y'
  let e : Spec (.of (q.ResidueField ⊗[R] Γ(P, V'))) ≅ (Spec.map φ).fiber y' :=
    (Arrow.leftFunc.mapIso E).symm
  have hred₂ : IsReduced (Spec (.of (q.ResidueField ⊗[R] Γ(P, V')))) :=
    isReduced_of_isOpenImmersion e.hom
  have hφ : ∀ r : R, algebraMap R Γ(P, V') r = r ^ p := fun r => by
    change (F.appLE V (F ⁻¹ᵁ V) le_rfl) r = r ^ p
    rw [← Scheme.Hom.app_eq_appLE]
    rfl
  have hred₃ : IsReduced (q.ResidueField ⊗[R] Γ(P, V')) := (affine_isReduced_iff _).mp hred₂
  let ρ : Γ(P, V') →+* R := RingHom.id R
  exact not_isReduced_residueField_tensor_of_frobenius hp q ρ hφ (a - μ ^ p) (a - μ ^ p)
    (hφ _) rfl hμ ht hred₃

/-- The pullback under the absolute Frobenius of `ℙ¹_k` of a closed point is not a regular
scheme. -/
theorem absoluteFrobenius_fiber_not_isRegular [IsAlgClosed k]
    (y : projectiveSpaceOverScheme 1 (Spec (.of k))) (hy : IsClosed {y}) :
    ¬ (((projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p).fiber y).IsRegular :=
  fun h => absoluteFrobenius_fiber_not_isReduced k p y hy (isReduced_of_isRegular_of_subsingleton _ h)

end Frobenius

/-- **Hartshorne III, Example 10.5.1 and Remark 10.9.3.** Let `k` be an algebraically closed
field of characteristic `p > 0` and let `F : ℙ¹_k ⟶ ℙ¹_k` be the Frobenius morphism. Then
1. `F` has relative dimension zero: every scheme-theoretic fibre has dimension zero;
2. `F` is smooth on no nonempty open subset of `ℙ¹_k`;
3. the map `F^*Ω_{ℙ¹} ⟶ Ω_{ℙ¹}` on absolute differentials is zero;
4. the relative differential sheaf `Ω_{ℙ¹/F}` is locally free of rank one; and
5. the pullback under `F` of every point of the target (a hyperplane of `ℙ¹_k`), that is, the
   scheme-theoretic fibre over a closed point, is nonreduced and not regular. -/
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
      ((projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p)).IsLocallyFreeOfRank 1 ∧
    (∀ y : projectiveSpaceOverScheme 1 (Spec (.of k)), IsClosed {y} →
      ¬ IsReduced (((projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p).fiber y) ∧
      ¬ (((projectiveSpaceOverScheme 1 (Spec (.of k))).absoluteFrobenius p).fiber y).IsRegular) :=
  ⟨absoluteFrobenius_fiber_topologicalKrullDim _ p, absoluteFrobenius_not_smooth_on_open k p,
    pullbackRelativeDifferentialsToComp_absoluteFrobenius_eq_zero k p 1,
    relativeDifferentials_absoluteFrobenius_isLocallyFreeOfRank_one k p,
    fun y hy => ⟨absoluteFrobenius_fiber_not_isReduced k p y hy,
      absoluteFrobenius_fiber_not_isRegular k p y hy⟩⟩

end Hartshorne
