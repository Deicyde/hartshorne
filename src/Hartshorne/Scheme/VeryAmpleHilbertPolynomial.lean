/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LinearSystem
import Hartshorne.Scheme.BirationalSectionAlgebraModel
import Hartshorne.Scheme.SectionAlgebraSheafComparison
import Hartshorne.Scheme.ImageReducedSource
import Hartshorne.Intersection.ProjectiveLinearSubspaceCycle
import Hartshorne.Scheme.ProjectiveIntersectionDegreeFormula
import Hartshorne.Scheme.ProjectiveIntersectionDivisor
import Hartshorne.Scheme.CartierClassPicard
import Hartshorne.Scheme.PicardPullback
import Hartshorne.Scheme.ProjectiveSpacePicard

/-!
# Very ample linear systems and the Hilbert polynomial

Hartshorne, *Algebraic Geometry*, II, Exercise 7.6(a) (p. 170).

Let `k` be algebraically closed, let `X` be an integral scheme projective over `k`, and let
`ι : X ⟶ ℙᴺ_k = Proj k[x₀, …, x_N]` be a closed immersion over `k` with `ι^* 𝒪(1) ≅ 𝒪_X(D)`
for a Cartier divisor `D` (so `D` is very ample, and `ι` is an embedding by a linear system of
`D`). The image of `X` is the closure of the image of its generic point, whose homogeneous
prime `𝔭` cuts out the classical projective variety `Y = Z(𝔭) ⊆ ℙᴺ(k)`. Then for all large `n`,
`dim |nD| = P_Y(n) - 1`, where `P_Y` is the Hilbert polynomial of `Y` (Chapter I, §7).

## Main results

* `Hartshorne.LinearSystem.exists_dim_complete_nsmul_eq_projectiveHilbertPolynomial`: the
  Cartier-divisor form, for an integral projective `X` and any such embedding.
* `Hartshorne.LinearSystem.exists_dim_complete_weil_nsmul_eq_projectiveHilbertPolynomial`:
  Hartshorne's form, for a Weil divisor on a regular (nonsingular) integral projective `X`.

Supporting results, in `Hartshorne.VeryAmpleHilbert`:

* `exists_iso_projQuotientι`: an integral closed subscheme `ι : X ⟶ ℙᴺ_k` is isomorphic over
  `ℙᴺ_k` to `Proj (S/I)` for the homogeneous prime `I` of the image of its generic point.
* `exists_finrank_pullback_twist_eq`: for such `I`, `dim_k Γ(X, ι^* 𝒪(n)) = dim_k (S/I)_n` for
  all large `n`.
* `nonempty_nsmul_sheaf_iso`: if `ι^* 𝒪(1) ≅ 𝒪_X(D)` then `ι^* 𝒪(n) ≅ 𝒪_X(nD)` for `n ≥ 1`.
* `finrank_globalSectionsOverField_congr`: isomorphic sheaves have global sections of the same
  dimension.

## Proof

Since `X` is reduced, the ideal sheaf of `ι` is the vanishing ideal of `ι(X)`, the closure of
the image `y` of the generic point. The closed subscheme `Proj (S/𝔭)` is integral, its image is
the closure of `y` as well, so the two closed subschemes agree and `X ≅ Proj (S/𝔭)` over `ℙᴺ_k`.
Under this isomorphism `ι^* 𝒪(n)` becomes `𝒪_{Proj (S/𝔭)}(n)`, and `(S/𝔭)_n → Γ(𝒪(n))`,
`s ↦ s / 1`, is bijective for large `n` (Exercise II.5.9(b)); both identifications are
compatible with scalars from `k`. By the Nullstellensatz `𝔭 = J(Y)`, so `(S/𝔭)_n = S(Y)_n`,
whose dimension is `P_Y(n)` for large `n`. Finally `ι^* 𝒪(n) ≅ 𝒪_X(nD)`, comparing classes in
`Pic X` through `𝒪(n) ≅ 𝒪(1)^{⊗ n}`, and `dim |nD| = dim_k Γ(X, 𝒪_X(nD)) - 1`.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial

namespace Hartshorne
namespace VeryAmpleHilbert

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem isReduced_proj_of_isDomain {A σ : Type u} [CommRing A] [IsDomain A]
    [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] : IsReduced (Proj 𝒜) := by
  have : ∀ x : Proj 𝒜, _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) := by
    intro x
    have hred : _root_.IsReduced
        (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) := by
      refine ⟨fun a ⟨n, hn⟩ => HomogeneousLocalization.val_injective _ ?_⟩
      have h1 := congrArg HomogeneousLocalization.val hn
      rw [HomogeneousLocalization.val_pow, HomogeneousLocalization.val_zero] at h1
      rw [HomogeneousLocalization.val_zero]
      exact IsReduced.eq_zero _ ⟨n, h1⟩
    exact isReduced_of_injective (Proj.stalkIso' 𝒜 x).toRingHom (Proj.stalkIso' 𝒜 x).injective
  exact isReduced_of_isReduced_stalk _

variable {k : Type u} [Field k] {N : ℕ}
local notation "𝒮" => homogeneousSubmodule (Fin (N + 1)) k

private theorem projQuotientι_base_asHomogeneousIdeal (I : HomogeneousIdeal 𝒮)
    (w : Proj (gradedQuotient 𝒮 I)) :
    ((projQuotientι 𝒮 I).base w).asHomogeneousIdeal =
      w.asHomogeneousIdeal.comap (gradedQuotientMk 𝒮 I) := by
  rw [projQuotientι_eq_map]; rfl

/-- The closure of the image of a morphism from an integral scheme is the closure of the image
of its generic point. -/
private theorem closure_range_eq {X : Scheme.{u}} [IsIntegral X] (ι : X ⟶ Proj 𝒮) :
    closure (Set.range ι) = closure {ι.base (genericPoint X)} := by
  apply le_antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨x, rfl⟩
    exact specializes_iff_mem_closure.mp
      (((genericPoint_spec X).specializes (Set.mem_univ x)).map ι.continuous)
  · exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)

/-- The homogeneous ideal of the image of the generic point. -/
private abbrev genericIdeal {X : Scheme.{u}} [IsIntegral X] (ι : X ⟶ Proj 𝒮) :
    HomogeneousIdeal 𝒮 :=
  (ι.base (genericPoint X)).asHomogeneousIdeal

/-- The classical projective set `Y = Z(𝔭)` cut out by the homogeneous prime `𝔭` of the image of
the generic point. -/
private abbrev embeddedSet {X : Scheme.{u}} [IsIntegral X] (ι : X ⟶ Proj 𝒮) :
    Set (ProjectiveSpace k (Fin (N + 1))) :=
  projZeroSet ((genericIdeal ι).toIdeal : Set (MvPolynomial (Fin (N + 1)) k))

private theorem projVanishingIdeal_embeddedSet [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
    (ι : X ⟶ Proj 𝒮) :
    (projVanishingIdeal (embeddedSet ι)).toIdeal = (genericIdeal ι).toIdeal :=
  (isProjVariety_projZeroSet_asHomogeneousIdeal _).2

/-- If `I` is the homogeneous prime of a point `y`, the closed subscheme `Proj (S/I)` has
underlying set the closure of `y`. -/
private theorem closure_range_projQuotientι_of_eq (I : HomogeneousIdeal 𝒮) (y : Proj 𝒮)
    (hI : I.toIdeal = y.asHomogeneousIdeal.toIdeal) :
    closure (Set.range (projQuotientι 𝒮 I)) = closure {y} := by
  have hker : ∀ a : MvPolynomial (Fin (N + 1)) k,
      Ideal.Quotient.mk I.toIdeal a = 0 ↔ a ∈ y.asHomogeneousIdeal := fun a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hI]; rfl
  apply le_antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    rw [← specializes_iff_mem_closure, projectiveSpace_specializes_iff_le,
      projQuotientι_base_asHomogeneousIdeal]
    intro a ha
    change Ideal.Quotient.mk _ a ∈ w.asHomogeneousIdeal
    rw [(hker a).2 ha]
    exact zero_mem _
  · refine closure_mono (Set.singleton_subset_iff.mpr ?_)
    have : I.toIdeal.IsPrime := hI ▸ y.isPrime
    have hrel : ¬ HomogeneousIdeal.irrelevant (gradedQuotient 𝒮 I) ≤ ⊥ := by
      intro h
      apply y.not_irrelevant_le
      intro a ha
      rw [← hker]
      have hmem : Ideal.Quotient.mk I.toIdeal a ∈
          (HomogeneousIdeal.irrelevant (gradedQuotient 𝒮 I)).toIdeal := by
        classical
        rw [← DirectSum.sum_support_decompose 𝒮 a, map_sum]
        refine sum_mem fun i _ => ?_
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · have h0 : ((DirectSum.decompose 𝒮 a 0 : 𝒮 0) : MvPolynomial (Fin (N + 1)) k) = 0 :=
            (HomogeneousIdeal.mem_irrelevant_iff 𝒮 a).1 ha
          rw [h0, map_zero]
          exact zero_mem _
        · exact HomogeneousIdeal.mem_irrelevant_of_mem _ hi
            (mk_mem_gradedQuotient (DirectSum.decompose 𝒮 a i).2)
      have := h hmem
      exact (Ideal.mem_bot).1 this
    have hbot : (⊥ : HomogeneousIdeal (gradedQuotient 𝒮 I)).toIdeal.IsPrime := by
      rw [HomogeneousIdeal.toIdeal_bot]
      exact Ideal.isPrime_bot
    let w : ProjectiveSpectrum (gradedQuotient 𝒮 I) := ⟨⊥, hbot, hrel⟩
    refine ⟨w, ?_⟩
    · apply ProjectiveSpectrum.ext
      rw [projQuotientι_base_asHomogeneousIdeal I w]
      apply HomogeneousIdeal.toIdeal_injective
      ext a
      change Ideal.Quotient.mk I.toIdeal a ∈ (⊥ : HomogeneousIdeal (gradedQuotient 𝒮 I)).toIdeal ↔ _
      rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot, hker]
      rfl

/-- If `I` is the homogeneous prime of the image of the generic point of an integral scheme `X`,
then `Proj (S/I) ⟶ ℙᴺ` and `ι` have the same ideal sheaf. -/
theorem ker_projQuotientι_eq {X : Scheme.{u}} [IsIntegral X] (ι : X ⟶ Proj 𝒮)
    (I : HomogeneousIdeal 𝒮)
    (hI : I.toIdeal = (ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal) :
    (projQuotientι 𝒮 I).ker = ι.ker := by
  have : I.toIdeal.IsPrime := hI ▸ (ι.base (genericPoint X)).isPrime
  have : IsReduced (Proj (gradedQuotient 𝒮 I)) := isReduced_proj_of_isDomain
  rw [ker_eq_vanishingIdeal_closure_range, ker_eq_vanishingIdeal_closure_range]
  congr 2
  rw [closure_range_projQuotientι_of_eq I _ hI, closure_range_eq]

/-- An integral closed subscheme `ι : X ⟶ ℙᴺ` is `Proj (S/I)` for the homogeneous prime `I` of
the image of its generic point. -/
theorem exists_iso_projQuotientι {X : Scheme.{u}} [IsIntegral X] (ι : X ⟶ Proj 𝒮)
    [IsClosedImmersion ι] (I : HomogeneousIdeal 𝒮)
    (hI : I.toIdeal = (ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal) :
    ∃ e : X ≅ Proj (gradedQuotient 𝒮 I), e.hom ≫ projQuotientι 𝒮 I = ι := by
  have h := ker_projQuotientι_eq ι I hI
  have := IsClosedImmersion.isIso_lift _ _ h
  exact ⟨asIso (IsClosedImmersion.lift _ ι h.le), IsClosedImmersion.lift_fac _ _ _⟩

/-- Two vector spaces mapping bijectively and compatibly with scalars onto the same module (with
scalars acting through a ring map) have the same dimension. -/
private theorem finrank_eq_of_bijective {K R G V W : Type*} [Field K] [CommRing R]
    [AddCommGroup G] [Module R G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (κ : K →+* R)
    (ψ : V →+ G) (χ : W →+ G) (hψ : Function.Bijective ψ) (hχ : Function.Bijective χ)
    (hψs : ∀ (c : K) (v : V), ψ (c • v) = κ c • ψ v)
    (hχs : ∀ (c : K) (w : W), χ (c • w) = κ c • χ w) :
    Module.finrank K V = Module.finrank K W := by
  let _ : Module K G := Module.compHom G κ
  let eV : V ≃ₗ[K] G :=
    LinearEquiv.ofBijective ({ ψ with map_smul' := hψs } : V →ₗ[K] G) hψ
  let eW : W ≃ₗ[K] G :=
    LinearEquiv.ofBijective ({ χ with map_smul' := hχs } : W →ₗ[K] G) hχ
  exact (eV.trans eW.symm).finrank_eq

private theorem spec_map_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (c : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv c) = (Scheme.ΓSpecIso S).inv (f c) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

private theorem mem_gradedQuotient_iff_mem_quotGrading (I : HomogeneousIdeal 𝒮) (n : ℕ)
    (m : MvPolynomial (Fin (N + 1)) k ⧸ I.toIdeal) :
    m ∈ gradedQuotient 𝒮 I n ↔ m ∈ quotGrading 𝒮 I n := by
  rw [mem_gradedQuotient_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

/-- `J(Y)` as a homogeneous ideal for the standard grading of `k[x₀, …, x_N]`. -/
private abbrev vanishingHomogeneousIdeal (Y : Set (ProjectiveSpace k (Fin (N + 1)))) :
    HomogeneousIdeal 𝒮 :=
  ⟨homogeneousVanishingIdeal Y, isHomogeneousIdeal_homogeneousVanishingIdeal Y⟩

private theorem appTop_comp_spec_map_ΓSpecIso_inv {Z : Scheme.{u}} {R S : CommRingCat.{u}}
    (g : Z ⟶ Spec S) (f : R ⟶ S) (c : R) :
    (g ≫ Spec.map f).appTop ((Scheme.ΓSpecIso R).inv c) =
      g.appTop ((Scheme.ΓSpecIso S).inv (f c)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, spec_map_appTop_ΓSpecIso_inv]

open SectionAlgebraModel GradedGlobalSections in
theorem exists_finrank_pullback_twist_eq {X : Scheme.{u}} [IsIntegral X] {q : X ⟶ Spec (.of k)}
    (ι : X ⟶ Proj 𝒮) [IsClosedImmersion ι] (hι : ι ≫ projectiveSpaceStructureMorphism = q)
    (I : HomogeneousIdeal 𝒮)
    (hI : I.toIdeal = (ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Module.finrank k (globalSectionsOverField q
        ((Scheme.Modules.pullback ι).obj (projTwistingSheaf 𝒮 n))) =
      Module.finrank k (quotGrading 𝒮 I n) := by
  obtain ⟨e, he⟩ := exists_iso_projQuotientι ι I hI
  obtain ⟨n₀, hn₀⟩ := exists_bijective_twistSection_quotient k (R := k) I
  refine ⟨n₀, fun n hn => ?_⟩
  let φ := gradedQuotientMk 𝒮 I
  have hf := ProjTruncation.irrelevant_le_map_of_surjective (gradedQuotientMk_surjective 𝒮 I)
  have h : e.inv ≫ ι = Proj.map φ hf := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp, projQuotientι_eq_map]
  let E := pullbackPullbackTwistIso φ hf (ProjectiveSpacePicard.adjoin_one_eq_top k N) ι e.inv h n
  set M := (Scheme.Modules.pullback ι).obj (projTwistingSheaf 𝒮 n)
  have hW : (⊤ : (Proj (gradedQuotient 𝒮 I)).Opens) ≤ e.inv ⁻¹ᵁ (q ⁻¹ᵁ ⊤) := fun _ _ => trivial
  let ψ : globalSectionsOverField q M →+ Γ(projTwistingSheaf (gradedQuotient 𝒮 I) n, ⊤) :=
    (E.hom.app ⊤).hom.comp (pullbackTopAddHom e.inv M hW)
  have hψ : Function.Bijective ψ :=
    bijective_iso_comp_pullbackTopAddHom e.inv M hW
      (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top) E
  let F : CommRingCat.of k ⟶ CommRingCat.of (gradedQuotient 𝒮 I 0) :=
    CommRingCat.ofHom (algebraMap k (𝒮 0)) ≫
      CommRingCat.ofHom (GradedRingHom.gradedZeroRingHom φ)
  let κ : k →+* Γ(Proj (gradedQuotient 𝒮 I), ⊤) :=
    (Proj.toSpecZero (gradedQuotient 𝒮 I) ≫ Spec.map F).appTop.hom.comp
      (Scheme.ΓSpecIso (.of k)).inv.hom
  let χ : quotGrading 𝒮 I n →+ Γ(projTwistingSheaf (gradedQuotient 𝒮 I) n, ⊤) :=
    { toFun := fun m => twistSection n
        ⟨m.1, (mem_gradedQuotient_iff_mem_quotGrading I n m.1).2 m.2⟩ (op ⊤)
      map_zero' := twistSection_zero n
      map_add' := fun a b => twistSection_add n
        ⟨a.1, (mem_gradedQuotient_iff_mem_quotGrading I n a.1).2 a.2⟩
        ⟨b.1, (mem_gradedQuotient_iff_mem_quotGrading I n b.1).2 b.2⟩ }
  have hχ : Function.Bijective χ := by
    let eq : quotGrading 𝒮 I n ≃ gradedQuotient 𝒮 I n :=
      { toFun := fun m => ⟨m.1, (mem_gradedQuotient_iff_mem_quotGrading I n m.1).2 m.2⟩
        invFun := fun m => ⟨m.1, (mem_gradedQuotient_iff_mem_quotGrading I n m.1).1 m.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc : (χ : quotGrading 𝒮 I n → _) =
        (fun a : gradedQuotient 𝒮 I n => twistSection n a (op ⊤)) ∘ eq := rfl
    rw [hc]
    exact (hn₀ n hn).comp eq.bijective
  have hW' : (⊤ : (Proj (gradedQuotient 𝒮 I)).Opens) ≤ (e.inv ≫ q) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hq : e.inv ≫ q = Proj.toSpecZero (gradedQuotient 𝒮 I) ≫ Spec.map F := by
    rw [← hι, ← Category.assoc, h, projectiveSpaceStructureMorphism, ← Category.assoc,
      projMap_toSpecZero, Category.assoc, ← Spec.map_comp]
  have hκ : ∀ c : k, (e.inv ≫ q).appLE ⊤ ⊤ hW' ((Scheme.ΓSpecIso (.of k)).inv c) = κ c := by
    intro c
    rw [ProjTwistPullback.appLE_top_top, hq]
    rfl
  refine finrank_eq_of_bijective κ ψ χ hψ hχ (fun c v => ?_) (fun c m => ?_)
  · exact iso_comp_pullbackTopAddHom_smul e.inv M q hW E _ (κ c) hW' (hκ c) v
  · have key := toSpecZero_appTop_smul_twistSection (𝒜 := gradedQuotient 𝒮 I)
      (F c) n ⟨m.1, (mem_gradedQuotient_iff_mem_quotGrading I n m.1).2 m.2⟩
    have hκc := appTop_comp_spec_map_ΓSpecIso_inv (Proj.toSpecZero (gradedQuotient 𝒮 I)) F c
    have hκc' : κ c = _ := hκc
    refine Eq.trans ?_ (congrArg (· • χ m) hκc').symm
    refine Eq.trans ?_ key.symm
    change twistSection n _ (op ⊤) = twistSection n _ (op ⊤)
    congr 2
    rw [Submodule.coe_smul, Algebra.smul_def]
    rfl

/-- Isomorphic sheaves have global sections of the same dimension. -/
theorem finrank_globalSectionsOverField_congr {X : Scheme.{u}} (q : X ⟶ Spec (.of k))
    {L L' : X.Modules} (e : L ≅ L') :
    Module.finrank k (globalSectionsOverField q L) =
      Module.finrank k (globalSectionsOverField q L') := by
  refine finrank_eq_of_bijective ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop).hom
    (e.hom.app ⊤).hom (AddMonoidHom.id _) (SectionAlgebraModel.bijective_app_of_iso e ⊤)
    Function.bijective_id (fun c v => ?_) (fun c w => rfl)
  exact Scheme.Modules.Hom.app_smul e.hom _ v

open Ringed in
private theorem pic_mk_twist_pow {n : ℕ} (hn : 1 ≤ n) :
    Pic.mk (R := (Proj 𝒮).sheaf) (projTwistingSheaf 𝒮 1)
        ((Scheme.Modules.isInvertible_iff_ringed _).1
          (ProjTwistingSheaf.isInvertible (ProjectiveSpacePicard.adjoin_one_eq_top k N) 1)) ^ n =
      Pic.mk (R := (Proj 𝒮).sheaf) (projTwistingSheaf 𝒮 n)
        ((Scheme.Modules.isInvertible_iff_ringed _).1
          (ProjTwistingSheaf.isInvertible (ProjectiveSpacePicard.adjoin_one_eq_top k N) n)) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [pow_succ, ih]
    exact (Pic.mk_eq_mk_iff _ _).2 ⟨moduleSheafTensorIsoTensor _ _ ≪≫
      twistMulIso 𝒮 (ProjectiveSpacePicard.adjoin_one_eq_top k N) n 1 ≪≫
      eqToIso (by push_cast; rfl)⟩

open Ringed in
/-- If `ι^* 𝒪(1) ≅ 𝒪_X(D)`, then `ι^* 𝒪(n) ≅ 𝒪_X(nD)` for `n ≥ 1`. -/
theorem nonempty_nsmul_sheaf_iso {X : Scheme.{u}} (ι : X ⟶ Proj 𝒮) (D : X.CartierDivisor)
    (φ : (Scheme.Modules.pullback ι).obj (projTwistingSheaf 𝒮 1) ≅ D.sheaf) {n : ℕ}
    (hn : 1 ≤ n) :
    Nonempty ((n • D).sheaf ≅ (Scheme.Modules.pullback ι).obj (projTwistingSheaf 𝒮 n)) := by
  have hO := fun m : ℤ => (Scheme.Modules.isInvertible_iff_ringed _).1
    (ProjTwistingSheaf.isInvertible (ProjectiveSpacePicard.adjoin_one_eq_top k N) m)
  have h1 : Pic.mk (R := X.sheaf) D.sheaf
      ((Scheme.Modules.isInvertible_iff_ringed _).1 D.isInvertible_sheaf) =
      Pic.pullback ι (Pic.mk (R := (Proj 𝒮).sheaf) _ (hO 1)) :=
    (Pic.mk_eq_mk_iff _ _).2 ⟨φ.symm⟩
  have h2 : Pic.mk (R := X.sheaf) (n • D).sheaf
      ((Scheme.Modules.isInvertible_iff_ringed _).1 (n • D).isInvertible_sheaf) =
      Pic.mk (R := X.sheaf) D.sheaf
        ((Scheme.Modules.isInvertible_iff_ringed _).1 D.isInvertible_sheaf) ^ n :=
    congrArg Additive.toMul (map_nsmul X.cartierDivisorToPicard n D)
  have h3 : Pic.mk (R := X.sheaf) (n • D).sheaf
      ((Scheme.Modules.isInvertible_iff_ringed _).1 (n • D).isInvertible_sheaf) =
      Pic.pullback ι (Pic.mk (R := (Proj 𝒮).sheaf) _ (hO n)) := by
    rw [h2, h1, ← map_pow, pic_mk_twist_pow hn]
  exact (Pic.mk_eq_mk_iff _ _).1 h3

end VeryAmpleHilbert

namespace LinearSystem

open VeryAmpleHilbert

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {N : ℕ}

local notation "𝒮" => homogeneousSubmodule (Fin (N + 1)) k

/-- **Very ample linear systems and the Hilbert polynomial** (Hartshorne II, Exercise 7.6(a)),
Cartier-divisor form. Let `k` be algebraically closed, `X` an integral scheme projective over `k`
with structure morphism `q`, and `ι : X ⟶ ℙᴺ_k` a closed immersion over `k` with
`ι^* 𝒪(1) ≅ 𝒪_X(D)` for a Cartier divisor `D`. Let `Y = Z(𝔭) ⊆ ℙᴺ(k)` be the classical
projective variety cut out by the homogeneous prime `𝔭` of the image of the generic point of `X`
(the classical points of `ι(X)`). Then for all large `n`, the complete linear system `|nD|` of
`𝒪_X(nD)` has dimension `P_Y(n) - 1`, where `P_Y` is the Hilbert polynomial of `Y`. -/
theorem exists_dim_complete_nsmul_eq_projectiveHilbertPolynomial [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] {q : X ⟶ Spec (.of k)} (hq : Projective q)
    (ι : X ⟶ Proj 𝒮) [IsClosedImmersion ι] (hι : ι ≫ projectiveSpaceStructureMorphism = q)
    (D : X.CartierDivisor)
    (φ : (Scheme.Modules.pullback ι).obj (projTwistingSheaf 𝒮 1) ≅ D.sheaf) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ((complete hq (n • D).isInvertible_sheaf).dim : ℚ) =
      (projectiveHilbertPolynomial (projZeroSet
        ((ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal :
          Set (MvPolynomial (Fin (N + 1)) k)))).eval (n : ℚ) - 1 := by
  obtain ⟨n₁, hn₁⟩ := exists_finrank_pullback_twist_eq ι hι
    (vanishingHomogeneousIdeal (embeddedSet ι)) (projVanishingIdeal_embeddedSet ι)
  obtain ⟨d₀, hd₀⟩ := Filter.eventually_atTop.1
    (projectiveHilbertPolynomial_isHilbertPolynomial (embeddedSet ι)).2
  refine ⟨max (max n₁ 1) d₀.toNat, fun n hn => ?_⟩
  obtain ⟨e⟩ := nonempty_nsmul_sheaf_iso ι D φ (n := n) (by omega)
  rw [dim_complete, finrank_globalSectionsOverField_congr q e, hn₁ n (by omega)]
  have h := hd₀ n (by omega)
  rw [Int.cast_natCast] at h
  rw [h]
  push_cast
  rfl

open AlgebraicGeometry.Scheme in
/-- **Very ample linear systems and the Hilbert polynomial** (Hartshorne II, Exercise 7.6(a)).
Let `k` be algebraically closed and `X` a regular integral scheme projective over `k` (a
nonsingular projective variety). Let `D` be a Weil divisor and `ι : X ⟶ ℙᴺ_k` a closed immersion
over `k` with `ι^* 𝒪(1) ≅ 𝒪_X(D)`, for instance the embedding defined by `|D|` when `D` is very
ample. Let `Y = Z(𝔭) ⊆ ℙᴺ(k)` be the classical projective variety of the classical points of
`ι(X)`, cut out by the homogeneous prime `𝔭` of the image of the generic point. Then for all large
`n`, `dim |nD| = P_Y(n) - 1`, where `P_Y` is the Hilbert polynomial of `Y`. -/
theorem exists_dim_complete_weil_nsmul_eq_projectiveHilbertPolynomial [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] {q : X ⟶ Spec (.of k)} (hq : Projective q)
    (hreg : X.IsRegular) (ι : X ⟶ Proj 𝒮) [IsClosedImmersion ι]
    (hι : ι ≫ projectiveSpaceStructureMorphism = q) :
    letI := isNoetherian_of_projective q hq
    letI := isSeparated_of_projective q hq
    ∀ (D : X.WeilDivisor),
      ((Scheme.Modules.pullback ι).obj (projTwistingSheaf 𝒮 1) ≅
        (weilCartierEquiv hreg.isLocallyFactorial D).sheaf) →
      ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ((complete hq (weilCartierEquiv hreg.isLocallyFactorial (n • D)).isInvertible_sheaf).dim :
            ℚ) =
          (projectiveHilbertPolynomial (projZeroSet
            ((ι.base (genericPoint X)).asHomogeneousIdeal.toIdeal :
              Set (MvPolynomial (Fin (N + 1)) k)))).eval (n : ℚ) - 1 := by
  let := isNoetherian_of_projective q hq
  let := isSeparated_of_projective q hq
  intro D φ
  obtain ⟨n₀, hn₀⟩ := exists_dim_complete_nsmul_eq_projectiveHilbertPolynomial hq ι hι _ φ
  refine ⟨n₀, fun n hn => ?_⟩
  rw [map_nsmul]
  exact hn₀ n hn

end LinearSystem

end Hartshorne
