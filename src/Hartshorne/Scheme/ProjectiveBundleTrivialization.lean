/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveBundle
import Hartshorne.Scheme.ProjectiveSpaceOverSpec
import Hartshorne.Scheme.ProjTwistPullback
import Hartshorne.Scheme.RelativeProjTwistingSheaf
import Hartshorne.Scheme.RelativeVeryAmple

/-!
# Projective bundles of free modules

Hartshorne, *Algebraic Geometry*, II.7, p. 162: if `E` is free of rank `n + 1` over an open
`U ⊆ X`, then `P(E)|_U ≅ ℙⁿ_U`. Here `U` is an affine open with a frame `e` of `E` (a basis of
`E|_U`): the frame identifies `Γ(U, S(E))` with the polynomial ring `A[x₀, …, xₙ]`, `A = Γ(U, 𝒪_X)`,
as graded rings (`Scheme.Modules.frameGradedHom`), hence
`π⁻¹(U) ≅ Proj Γ(U, S(E)) ≅ Proj A[x₀, …, xₙ] ≅ ℙⁿ_{Spec A} ≅ ℙⁿ_U`
(`Scheme.Modules.projectiveBundleFrameIso`), compatibly with the projections to `U`
(`Scheme.Modules.projectiveBundleFrameIso_hom_projection`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

noncomputable section

namespace Hartshorne

open AlgebraicGeometry HomogeneousIdeal Graded

section GradedIso

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The inverse of a bijective graded ring homomorphism preserves degrees. -/
private lemma symm_mem_of_bijective (φ : 𝒜 →+*ᵍ ℬ) (hφ : Function.Bijective φ) {d : ℕ} {b : B}
    (hb : b ∈ ℬ d) : (RingEquiv.ofBijective φ.toRingHom hφ).symm b ∈ 𝒜 d := by
  classical
  set a := (RingEquiv.ofBijective φ.toRingHom hφ).symm b
  have hab : φ a = b := (RingEquiv.ofBijective φ.toRingHom hφ).apply_symm_apply b
  have hcomp : ∀ j, j ≠ d → (DirectSum.decompose 𝒜 a j : A) = 0 := by
    intro j hj
    apply hφ.1
    rw [map_zero, GradedRingHom.map_directSumDecompose, hab,
      DirectSum.decompose_of_mem_ne ℬ hb (Ne.symm hj)]
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  by_cases hd : d ∈ DFinsupp.support (DirectSum.decompose 𝒜 a)
  · rw [Finset.sum_eq_single d (fun j _ hj => hcomp j hj) (fun h => absurd hd h)]
    exact SetLike.coe_mem _
  · rw [Finset.sum_eq_zero fun j hj => hcomp j fun h => hd (h ▸ hj)]
    exact zero_mem _

/-- The inverse of a bijective graded ring homomorphism, as a graded ring homomorphism. -/
def gradedInvOfBijective (φ : 𝒜 →+*ᵍ ℬ) (hφ : Function.Bijective φ) : ℬ →+*ᵍ 𝒜 where
  toRingHom := (RingEquiv.ofBijective φ.toRingHom hφ).symm.toRingHom
  map_mem := symm_mem_of_bijective φ hφ

private lemma irrelevant_le_map_of_leftInverse (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒜)
    (h : ∀ b, φ (ψ b) = b) : ℬ₊ ≤ 𝒜₊.map φ := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi b hb
  rw [← h b]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi (ψ.map_mem hb))

private lemma projMap_eq_id (f : ℬ →+*ᵍ ℬ) (hf : ℬ₊ ≤ ℬ₊.map f) (h : ∀ b, f b = b) :
    Proj.map f hf = 𝟙 (Proj ℬ) := by
  obtain rfl : f = GradedRingHom.id ℬ := GradedRingHom.ext h
  exact Proj.map_id

/-- **A graded ring isomorphism induces an isomorphism of `Proj`.** -/
def projIsoOfBijective (φ : 𝒜 →+*ᵍ ℬ) (hφ : Function.Bijective φ) : Proj ℬ ≅ Proj 𝒜 where
  hom := Proj.map φ (irrelevant_le_map_of_leftInverse φ (gradedInvOfBijective φ hφ)
    (RingEquiv.ofBijective φ.toRingHom hφ).apply_symm_apply)
  inv := Proj.map (gradedInvOfBijective φ hφ) (irrelevant_le_map_of_leftInverse _ φ
    (RingEquiv.ofBijective φ.toRingHom hφ).symm_apply_apply)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact projMap_eq_id _ _ (RingEquiv.ofBijective φ.toRingHom hφ).apply_symm_apply
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact projMap_eq_id _ _ (RingEquiv.ofBijective φ.toRingHom hφ).symm_apply_apply

lemma projIsoOfBijective_hom (φ : 𝒜 →+*ᵍ ℬ) (hφ : Function.Bijective φ) :
    (projIsoOfBijective φ hφ).hom = Proj.map φ (irrelevant_le_map_of_leftInverse φ
      (gradedInvOfBijective φ hφ) (RingEquiv.ofBijective φ.toRingHom hφ).apply_symm_apply) :=
  rfl

private lemma isIso_projPartialDomain_ι (φ : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map φ) :
    IsIso (projPartialDomain φ).ι := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  exact ⟨inferInstance, ⟨fun y => ⟨⟨y, by rw [projPartialDomain_eq_top hf]; trivial⟩, rfl⟩⟩⟩

/-- Modules whose pullbacks along an isomorphism are isomorphic are isomorphic. -/
private def isoOfPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] {M N : Y.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N) : M ≅ N :=
  ((Scheme.Modules.pullbackId Y).app M).symm ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f)).symm.app M ≪≫
    ((Scheme.Modules.pullbackComp (inv f) f).app M).symm ≪≫
    (Scheme.Modules.pullback (inv f)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp (inv f) f).app N ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f)).app N ≪≫
    (Scheme.Modules.pullbackId Y).app N

/-- **Twisting sheaves pull back along `Proj.map`** (Hartshorne II.5.12(c), everywhere-defined
case): for a graded `φ : S → T` with `T₊ ⊆ φ(S₊)T` and `S` generated by `S₁` over `S₀`,
`(Proj φ)^* 𝒪_{Proj S}(k) ≅ 𝒪_{Proj T}(k)`. -/
def pullbackProjMapTwistIso (φ : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map φ)
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) (k : ℤ) :
    (Scheme.Modules.pullback (Proj.map φ hf)).obj (projTwistingSheaf 𝒜 k) ≅
      projTwistingSheaf ℬ k :=
  haveI := isIso_projPartialDomain_ι φ hf
  isoOfPullbackIso (projPartialDomain φ).ι
    ((Scheme.Modules.pullbackComp (projPartialDomain φ).ι (Proj.map φ hf)).app _ ≪≫
      (Scheme.Modules.pullbackCongr (projPartialMap_eq_map hf).symm).app _ ≪≫
      ProjTwistPullback.pullbackTwistIso φ k hgen ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback (projPartialDomain φ).ι).app _)

end GradedIso

end Hartshorne

namespace AlgebraicGeometry.Scheme.Modules

open Hartshorne Hartshorne.SheafAlgebraOperations Hartshorne.ModuleSheafAlgebra

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {E : X.Modules}

variable (E) in
/-- The chart ring map sends homogeneous polynomials of degree `d` to sections of `S^d(E)`. -/
lemma chartRingHom_mem_symmetricGrading {κ : Type u} {U : X.Opens} (hU : IsCompact (U : Set X))
    (e : κ → Γ(E, U)) {d : ℕ} {q : MvPolynomial κ Γ(X, U)} (hq : q.IsHomogeneous d) :
    E.chartRingHom U e q ∈ E.symmetricGrading U d := by
  classical
  let := E.symmetricGradedRing hU
  rw [q.as_sum, map_sum]
  refine sum_mem fun α hα => ?_
  have hdeg := hq (MvPolynomial.mem_support_iff.1 hα)
  rw [chartRingHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, Finsupp.prod]
  have h := SetLike.mul_mem_graded (E.unitRingHom_mem_symmetricGrading U (q.coeff α))
    (SetLike.prod_pow_mem_graded (E.symmetricGrading U) (fun _ => 1)
      (fun k => E.symDegreeOne U (e k)) α (F := α.support)
      fun k _ => E.symDegreeOne_mem_symmetricGrading U (e k))
  convert h using 2
  rw [zero_add, ← hdeg, Finsupp.weight_apply, Finsupp.sum]
  rfl

variable (hE : E.IsLocallyFree) (hfin : ∀ x, E.rankAt x < Cardinal.aleph0)

/-- An affine open as an object of the affine Zariski site. -/
private abbrev affineSiteOf {V : X.Opens} (hV : IsAffineOpen V) : X.AffineZariskiSite := ⟨V, hV⟩

/-- **A frame identifies `S(E)` with a polynomial ring, as graded rings**: for a frame `e` of `E`
over an affine open `V`, the graded ring homomorphism `A[x₀, …, xₙ] → Γ(V, S(E))`, `x_k ↦ e_k`,
where `A = Γ(V, 𝒪_X)`. -/
def frameGradedHom {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ} (e : ULift.{u} (Fin (n + 1)) → Γ(E, V)) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(X, V) →+*ᵍ
      (symmetricGradedAlgebra hE hfin).grading (affineSiteOf hV) where
  toRingHom := (E.chartRingHom V e).comp (MvPolynomial.rename ULift.up).toRingHom
  map_mem {d} p hp :=
    E.chartRingHom_mem_symmetricGrading hV.isCompact e
      (((MvPolynomial.mem_homogeneousSubmodule d p).1 hp).rename_isHomogeneous)

lemma frameGradedHom_apply {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ} (e : ULift.{u} (Fin (n + 1)) → Γ(E, V))
    (p : MvPolynomial (Fin (n + 1)) Γ(X, V)) :
    frameGradedHom hE hfin hV e p = E.chartRingHom V e (MvPolynomial.rename ULift.up p) :=
  rfl

lemma frameGradedHom_bijective {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ} {e : ULift.{u} (Fin (n + 1)) → Γ(E, V)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) E V e) :
    Function.Bijective (frameGradedHom hE hfin hV e) :=
  (E.chartRingHom_bijective hV he).comp
    (MvPolynomial.renameEquiv Γ(X, V) (Equiv.ulift.{u}.symm)).bijective

/-- **`P(E)` over an affine open on which `E` is free** (Hartshorne II.7, p. 162): a frame `e` of
`E` of rank `n + 1` over an affine open `V` gives
`π⁻¹(V) ≅ Proj Γ(V, S(E)) ≅ Proj A[x₀, …, xₙ] ≅ ℙⁿ_{Spec A} ≅ ℙⁿ_V`, `A = Γ(V, 𝒪_X)`, sending the
coordinate `x_k` to the frame element `e_k`. -/
def projectiveBundleFrameIso [IsNoetherian X] {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := X.sheaf) E V e) :
    (projectiveBundleProj hE hfin ⁻¹ᵁ V).toScheme ≅
      projectiveSpaceOverScheme n V :=
  (symmetricGradedAlgebra hE hfin).restrictIso (affineSiteOf hV) ≪≫
    projIsoOfBijective (frameGradedHom hE hfin hV e) (frameGradedHom_bijective hE hfin hV he) ≪≫
    projectiveSpaceOverSpecIso Γ(X, V) n (Equiv.refl _) ≪≫
    asIso (projectiveSpaceOverSchemeMap n hV.isoSpec.inv)

private lemma projectiveBundleFrameIso_aux {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := X.sheaf) E V e) :
    ((projIsoOfBijective (frameGradedHom hE hfin hV e) (frameGradedHom_bijective hE hfin hV he)).hom ≫
        (projectiveSpaceOverSpecIso Γ(X, V) n (Equiv.refl _)).hom ≫
          (asIso (projectiveSpaceOverSchemeMap n hV.isoSpec.inv)).hom) ≫
        projectiveSpaceOverSchemeProjection n V =
      (symmetricGradedAlgebra hE hfin).projToOpen (affineSiteOf hV) := by
  rw [← cancel_mono V.ι, asIso_hom, projectiveSpaceOverSpecIso_hom]
  simp only [Category.assoc]
  have hproj : projToProjectiveSpaceOverSpec Γ(X, V) n (Equiv.refl _) ≫
      projectiveSpaceOverSchemeProjection n (Spec Γ(X, V)) =
        Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(X, V)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V)
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(X, V) 0))) :=
    projToProjectiveSpaceOverSpec_projection _ _ _
  rw [projectiveSpaceOverSchemeMap_projection_assoc, reassoc_of% hproj,
    QuasiCoherentGradedAlgebra.projToOpen_ι,
    projIsoOfBijective_hom, ← Category.assoc (Proj.map _ _), projMap_toSpecZero, Category.assoc]
  congr 1
  rw [IsAffineOpen.fromSpec, ← Spec.map_comp_assoc]
  refine congrArg (fun f => Spec.map f ≫ _) ?_
  ext r
  change E.chartRingHom V e (MvPolynomial.rename ULift.up (MvPolynomial.C r)) =
    unitRingHom _ V r
  rw [MvPolynomial.rename_C, chartRingHom_C]

/-- The identification `P(E)|_V ≅ ℙⁿ_V` is an isomorphism over `V`. -/
theorem projectiveBundleFrameIso_hom_projection [IsNoetherian X] {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := X.sheaf) E V e) :
    (projectiveBundleFrameIso hE hfin hV he).hom ≫
        projectiveSpaceOverSchemeProjection n V =
      projectiveBundleProj hE hfin ∣_ V :=
  (Category.assoc _ _ _).trans ((congrArg (fun g => _ ≫ g)
    (projectiveBundleFrameIso_aux hE hfin hV he)).trans
      (QuasiCoherentGradedAlgebra.restrictIso_hom_projToOpen (symmetricGradedAlgebra hE hfin)
        (affineSiteOf hV)))

/-- **The twisting sheaf `𝒪_{P(E)}(k)`** of the projective bundle: the relative twisting sheaf of
`Proj_X S(E)`. -/
abbrev projectiveBundleTwistingSheaf [IsNoetherian X] (k : ℤ) : (projectiveBundle hE hfin).Modules :=
  (symmetricGradedAlgebra hE hfin).relTwistingSheaf k

private lemma adjoin_homogeneousSubmodule_one (R : Type u) [CommRing R] (n : ℕ) :
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 :
        Set (MvPolynomial (Fin (n + 1)) R)) = ⊤ :=
  top_le_iff.1 ((adjoin_projectiveSpaceGenerators R n (Equiv.refl _)).ge.trans
    (Algebra.adjoin_mono (Set.range_subset_iff.2 fun j =>
      projectiveSpaceGenerators_mem R n (Equiv.refl _) j)))

/-- **The identification `P(E)|_V ≅ ℙⁿ_V` is compatible with the twisting sheaves**: it pulls
`𝒪_{ℙⁿ_V}(k)` back to the restriction of `𝒪_{P(E)}(k)` to `π⁻¹(V)`. -/
def projectiveBundleFrameIsoTwist [IsNoetherian X] {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := X.sheaf) E V e)
    (k : ℤ) :
    (Scheme.Modules.pullback (projectiveBundleFrameIso hE hfin hV he).hom).obj
        (projectiveSpaceTwistingSheaf n V k) ≅
      (projectiveBundleTwistingSheaf hE hfin k).restrict (projectiveBundleProj hE hfin ⁻¹ᵁ V).ι :=
  let S := symmetricGradedAlgebra hE hfin
  let φ := frameGradedHom hE hfin hV e
  let hφ := frameGradedHom_bijective hE hfin hV he
  let r := (S.restrictIso (affineSiteOf hV)).hom
  let p := (projIsoOfBijective φ hφ).hom
  let c := projToProjectiveSpaceOverSpec Γ(X, V) n (Equiv.refl _)
  let m := projectiveSpaceOverSchemeMap n hV.isoSpec.inv
  -- `m^* 𝒪_{ℙⁿ_V}(k) ≅ 𝒪_{ℙⁿ_{Spec A}}(k)`
  let im : (Scheme.Modules.pullback m).obj (projectiveSpaceTwistingSheaf n V k) ≅
      projectiveSpaceTwistingSheaf n (Spec Γ(X, V)) k :=
    (Scheme.Modules.pullbackComp m _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (projectiveSpaceOverSchemeMap_fst n _)).app _
  -- `c^* 𝒪_{ℙⁿ_{Spec A}}(k) ≅ 𝒪_{Proj A[x]}(k)`
  let ic : (Scheme.Modules.pullback c).obj (projectiveSpaceTwistingSheaf n (Spec Γ(X, V)) k) ≅
      projTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(X, V)) k :=
    (Scheme.Modules.pullbackComp c _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (projToProjectiveSpaceOverSpec_fst _ _ _)).app _ ≪≫
      pullbackProjMapTwistIso _ _ (adjoin_intGrading_one_eq_top n) k
  -- `p^* 𝒪_{Proj A[x]}(k) ≅ 𝒪_{Proj Γ(V, S(E))}(k)`
  let ip : (Scheme.Modules.pullback p).obj (projTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(X, V))
      k) ≅ S.twistingSheaf k (affineSiteOf hV) :=
    pullbackProjMapTwistIso φ _ (adjoin_homogeneousSubmodule_one Γ(X, V) n) k
  -- `r^* 𝒪_{Proj Γ(V, S(E))}(k) ≅ 𝒪_{P(E)}(k)|_{π⁻¹(V)}`
  let ir : (Scheme.Modules.pullback r).obj (S.twistingSheaf k (affineSiteOf hV)) ≅
      (S.relTwistingSheaf k).restrict (S.relProjToBase ⁻¹ᵁ V).ι :=
    ((Scheme.Modules.restrictFunctorIsoPullback r).app _).symm ≪≫
      (S.relTwistingSheafAffineIso k (affineSiteOf hV)).symm
  ((Scheme.Modules.pullbackComp r (p ≫ c ≫ m)).app _).symm ≪≫
    (Scheme.Modules.pullback r).mapIso (((Scheme.Modules.pullbackComp p (c ≫ m)).app _).symm ≪≫
      (Scheme.Modules.pullback p).mapIso (((Scheme.Modules.pullbackComp c m).app _).symm ≪≫
        (Scheme.Modules.pullback c).mapIso im ≪≫ ic) ≪≫ ip) ≪≫ ir

end AlgebraicGeometry.Scheme.Modules
