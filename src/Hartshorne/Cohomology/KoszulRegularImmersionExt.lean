/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.KoszulRegularImmersion
import Hartshorne.RingedSpace.ScalarExtensionSheaf
import Hartshorne.RingedSpace.SheafExtRestrict
import Hartshorne.Scheme.AffineFormalModuleExact

universe u

open CategoryTheory Opposite TopologicalSpace Limits
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace Ringed

namespace KoszulSheaf

open Koszul ScalarExtension

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {A : Type u} [CommRing A] (φ : A →+* R.obj.obj (op ⊤)) {r : ℕ} (f : Fin r → A)

/-- The Koszul complex `K_•(f; A)`. -/
noncomputable abbrev K : ChainComplex (ModuleCat.{u} A) ℕ := sequenceKoszulComplex f (ModuleCat.of A A)

instance (p : ℕ) : Module.Free A ((K f).X p) :=
  inferInstanceAs (Module.Free A (⋀[A]^p (Fin r → A) ⊗[A] A))

instance (p : ℕ) : Module.Finite A ((K f).X p) :=
  inferInstanceAs (Module.Finite A (⋀[A]^p (Fin r → A) ⊗[A] A))

/-- The sheafified Koszul complex `𝒪_X ⊗_A K_•(f; A)`. -/
noncomputable def complex : ChainComplex (SheafOfModules.{u} (ringCatSheafOf R)) ℕ where
  X p := sheaf φ ((K f).X p)
  d i j := sheafMap φ ((K f).d i j)
  shape i j h := by rw [(K f).shape i j h]; exact sheafMap_zero φ
  d_comp_d' i j k _ _ := by rw [← sheafMap_comp, (K f).d_comp_d, sheafMap_zero]

lemma isFiniteLocallyFree_complex (p : ℕ) : IsFiniteLocallyFree ((complex φ f).X p) :=
  isFiniteLocallyFree_sheaf φ _

variable (G : SheafOfModules.{u} (ringCatSheafOf R))

lemma overHomEquiv_zero (W : Opens X) {N : ModuleCat.{u} A} [Module.Free A N]
    [Module.Finite A N] : overHomEquiv φ G W (0 : (sheaf φ N).over W ⟶ G.over W) = 0 := by
  ext m
  rw [overHomEquiv_apply]
  rfl

lemma homComplex_d_apply (p : ℕ) (W : Opens X)
    (σ : ((complex φ f).X p).over W ⟶ G.over W) :
    (((moduleSheafHomComplex (complex φ f)).obj G).d p (p + 1)).val.app (op W) σ =
      SheafOfModules.Hom.over ((complex φ f).d (p + 1) p) W ≫ σ := by
  rw [moduleSheafHomComplex_d]
  exact moduleSheafHomPrecomp_app_app _ G W σ

lemma overHomEquiv_homComplex_d (p : ℕ) (W : Opens X)
    (σ : ((complex φ f).X p).over W ⟶ G.over W) :
    overHomEquiv φ G W ((((moduleSheafHomComplex (complex φ f)).obj G).d p (p + 1)).val.app
      (op W) σ) = (K f).d (p + 1) p ≫ overHomEquiv φ G W σ := by
  rw [homComplex_d_apply]
  exact overHomEquiv_comp φ G _ W σ

/-- **The dual of the sheafified Koszul complex is exact below the top degree.** If over a basis
of opens `W` the sequence `f` is Koszul-regular on `G(W)`, then `hⁿ(ℋom(𝒪_X ⊗_A K_•(f; A), G))`
vanishes for `n < r`. -/
theorem isZero_homology_homComplex {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hG : ∀ W ∈ B, IsKoszulRegular f
      (ModuleCat.of A ((ModuleCat.restrictScalars (baseMap φ W)).obj (G.val.obj (op W)))))
    {n : ℕ} (hn : n < r) :
    IsZero (((moduleSheafHomComplex (complex φ f)).obj G).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  cases n with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp)]
    refine sheafOfModules_exact_of_isBasis_sections _ hB (fun W hW x hx => ⟨0, ?_⟩)
    rw [map_zero]
    have h1 := overHomEquiv_homComplex_d φ f G 0 W x
    have hx' : (((moduleSheafHomComplex (complex φ f)).obj G).d 0 (0 + 1)).val.app (op W) x = 0 :=
      hx
    rw [hx', overHomEquiv_zero] at h1
    have h2 : LinearMap.lcomp A _ ((K f).d (0 + 1) 0).hom (overHomEquiv φ G W x).hom =
        LinearMap.lcomp A _ ((K f).d (0 + 1) 0).hom 0 := by
      rw [map_zero]
      ext y
      exact (congrArg (fun k => k.hom y) h1).symm
    have h3 := injective_lcomp_sequenceKoszulComplex_d f _ (hG W hW) hn h2
    apply (overHomEquiv φ G W).injective
    rw [overHomEquiv_zero]
    ext y
    exact (congrArg (fun k => k y) h3).symm
  | succ n =>
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
    refine sheafOfModules_exact_of_isBasis_sections _ hB (fun W hW x hx => ?_)
    have h1 := overHomEquiv_homComplex_d φ f G (n + 1) W x
    have hx' : (((moduleSheafHomComplex (complex φ f)).obj G).d (n + 1) (n + 1 + 1)).val.app
        (op W) x = 0 := hx
    rw [hx', overHomEquiv_zero] at h1
    have h2 : LinearMap.lcomp A _ ((K f).d (n + 1 + 1) (n + 1)).hom (overHomEquiv φ G W x).hom =
        0 := by
      ext y
      exact (congrArg (fun k => k.hom y) h1).symm
    let P := (ModuleCat.restrictScalars (baseMap φ W)).obj (G.val.obj (op W))
    obtain ⟨y', hy'⟩ := (exact_lcomp_sequenceKoszulComplex_d f P (hG W hW) (p := n)
      (by omega)) _ |>.1 h2
    let y : (K f).X n ⟶ P := ModuleCat.homEquiv.symm y'
    refine ⟨(overHomEquiv φ G W).symm y, ?_⟩
    apply (overHomEquiv φ G W).injective
    have h4 := overHomEquiv_homComplex_d φ f G n W ((overHomEquiv φ G W).symm y)
    rw [Equiv.apply_symm_apply] at h4
    refine h4.trans ?_
    ext z
    rw [← hy']
    rfl

lemma extendScalars_map_eq_lTensor {S : Type u} [CommRing S] (ψ : A →+* S)
    {N N' : ModuleCat.{u} A} (g : N ⟶ N') :
    ⇑((ModuleCat.extendScalars ψ).map g) =
      ⇑(LinearMap.lTensor ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of S S)) g.hom) := by
  funext t
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a m => rfl
  | add t t' ht ht' => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ht ht').trans
      (map_add _ _ _).symm)

/-- The augmented sheafified Koszul complex, as a morphism to `F₀[0]`. -/
noncomputable abbrev augmentation {F₀ : SheafOfModules.{u} (ringCatSheafOf R)}
    (ε : (complex φ f).X 0 ⟶ F₀) (hε : (complex φ f).d 1 0 ≫ ε = 0) :
    complex φ f ⟶ (ChainComplex.single₀ _).obj F₀ :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hε⟩

/-- **The sheafified Koszul complex is a resolution.** Let `f` be Koszul-regular on `A`, and let
`ε : 𝒪_X ⊗_A K_0 ⟶ F₀` kill the image of `d₁`. If over a basis of opens `W` the ring `𝒪_X(W)` is
flat over `A` and `𝒪_X(W) ⊗_A K_1 → 𝒪_X(W) ⊗_A K_0 → F₀(W) → 0` is exact, then the augmentation
`𝒪_X ⊗_A K_•(f; A) ⟶ F₀[0]` is a quasi-isomorphism. -/
theorem quasiIso_augmentation (hf : IsKoszulRegular f (ModuleCat.of A A))
    {F₀ : SheafOfModules.{u} (ringCatSheafOf R)} (ε : (complex φ f).X 0 ⟶ F₀)
    (hε : (complex φ f).d 1 0 ≫ ε = 0) {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hflat : ∀ W ∈ B, Module.Flat A
      ((ModuleCat.restrictScalars (baseMap φ W)).obj (ModuleCat.of _ (R.obj.obj (op W)))))
    (h0 : ∀ W ∈ B, Function.Exact (((complex φ f).d 1 0).val.app (op W)) (ε.val.app (op W)) ∧
      Function.Surjective (ε.val.app (op W))) :
    QuasiIso (augmentation φ f ε hε) := ⟨fun n => by
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · have hex : (ShortComplex.mk ((complex φ f).d 1 0) ε hε).Exact :=
        sheafOfModules_exact_of_isBasis_sections _ hB (fun W hW x hx => (h0 W hW).1 x |>.1 hx)
      have hepi : Epi ε := by
        rw [← ShortComplex.exact_iff_epi (ShortComplex.mk ε (0 : F₀ ⟶ F₀) (by simp)) rfl]
        exact sheafOfModules_exact_of_isBasis_sections _ hB (fun W hW x _ => (h0 W hW).2 x)
      refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨hex, hepi⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm)
        ((Category.id_comp _).trans ((ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _).symm.trans
          (Category.comp_id _).symm))
    all_goals first | rfl | exact (complex φ f).shape 0 0 (by simp)
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
      refine sheafOfModules_exact_of_isBasis_sections _ hB (fun W hW x hx => ?_)
      have hK : Function.Exact ((K f).d (n + 1 + 1) (n + 1)).hom ((K f).d (n + 1) n).hom := by
        have := hf n
        rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)] at this
        exact LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 this).symm
      have := hflat W hW
      have hT := Module.Flat.lTensor_exact
        ((ModuleCat.restrictScalars (baseMap φ W)).obj (ModuleCat.of _ (R.obj.obj (op W)))) hK
      rw [← extendScalars_map_eq_lTensor, ← extendScalars_map_eq_lTensor] at hT
      exact (hT x).1 hx
    · exact ChainComplex.exactAt_succ_single_obj _ _⟩

omit φ in
lemma degreeZeroEquiv_d_mem (k : (K f).X 1) :
    degreeZeroEquiv (V := Fin r → A) A (((K f).d 1 0).hom k) ∈ Ideal.span (Set.range f) := by
  rw [← range_koszulForm]
  have hm : degreeZeroEquiv (V := Fin r → A) A (((K f).d 1 0).hom k) ∈
      koszulSubmodule (koszulForm f) A := by
    rw [← range_degreeZeroEquiv_comp_contraction (koszulForm f) A]
    exact ⟨k, by rw [koszulComplex_d]; rfl⟩
  change _ ∈ (LinearMap.range (koszulForm f) : Ideal A) • (⊤ : Submodule A A) at hm
  rwa [Ideal.smul_eq_mul, Ideal.mul_top] at hm

omit φ in
/-- The generator `k₀ ∈ K_0 = ⋀^0 A^r ⊗ A` corresponding to `1 ∈ A`. -/
noncomputable def k₀ : (K f).X 0 := (degreeZeroEquiv (V := Fin r → A) A).symm 1

omit φ in
lemma eq_smul_k₀ (k : (K f).X 0) : k = degreeZeroEquiv (V := Fin r → A) A k • k₀ f := by
  apply (degreeZeroEquiv (V := Fin r → A) A).injective
  rw [LinearEquiv.map_smul, k₀, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

omit φ in
lemma exists_d_eq (j : Fin r) : ∃ e : (K f).X 1, ((K f).d 1 0).hom e = f j • k₀ f := by
  refine ⟨(exteriorPower.oneEquiv A (Fin r → A)).symm (Pi.single j 1) ⊗ₜ[A] (1 : A), ?_⟩
  rw [eq_smul_k₀ f (((K f).d 1 0).hom _)]
  congr 1
  rw [koszulComplex_d]
  change degreeZeroEquiv _ ((contraction (koszulForm f) 0).rTensor A _) = _
  rw [degreeZeroEquiv_contraction_tmul, LinearEquiv.apply_symm_apply, koszulForm_single,
    smul_eq_mul, mul_one]

/-- Every section of `𝒪_X ⊗_A K_0` over `W` is of the form `s ⊗ k₀`. -/
lemma exists_eq_tmul_k₀ (W : Opens X) (x : ((complex φ f).X 0).val.obj (op W)) :
    ∃ s : R.obj.obj (op W), x = s ⊗ₜ[A, baseMap φ W] k₀ f := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (TensorProduct.zero_tmul _ _).symm⟩
  | tmul s k =>
    refine ⟨baseMap φ W (degreeZeroEquiv (V := Fin r → A) A k) *
      (show R.obj.obj (op W) from s), ?_⟩
    conv_lhs => rw [eq_smul_k₀ f k]
    exact (TensorProduct.smul_tmul _ _ _).symm
  | add x y hx hy =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    exact ⟨s + t, (TensorProduct.add_tmul (R := A) (M := (ModuleCat.restrictScalars
      (baseMap φ W)).obj (ModuleCat.of _ (R.obj.obj (op W)))) s t (k₀ f)).symm⟩

/-- The image of `d₁` on sections over `W` contains `a ⊗ k₀` for every `a` in the ideal of
`𝒪_X(W)` generated by `f`. -/
lemma exists_d_eq_tmul_k₀ (W : Opens X) (a : R.obj.obj (op W))
    (ha : a ∈ Ideal.span (Set.range fun j => baseMap φ W (f j))) :
    ∃ y, (((complex φ f).d 1 0).val.app (op W)) y = a ⊗ₜ[A, baseMap φ W] k₀ f := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨e, he⟩ := exists_d_eq f j
    refine ⟨(1 : R.obj.obj (op W)) ⊗ₜ[A, baseMap φ W] e, ?_⟩
    change (1 : R.obj.obj (op W)) ⊗ₜ[A, baseMap φ W] (((K f).d 1 0).hom e) = _
    rw [he]
    refine (TensorProduct.smul_tmul (R := A) (M := (ModuleCat.restrictScalars
      (baseMap φ W)).obj (ModuleCat.of _ (R.obj.obj (op W)))) (f j) _ (k₀ f)).symm.trans ?_
    congr 1
    exact mul_one (baseMap φ W (f j))
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact (TensorProduct.zero_tmul _ _).symm
  | add a b _ _ ha hb =>
    obtain ⟨y₁, hy₁⟩ := ha
    obtain ⟨y₂, hy₂⟩ := hb
    refine ⟨y₁ + y₂, ?_⟩
    rw [map_add, hy₁, hy₂]
    exact (TensorProduct.add_tmul (R := A) (M := (ModuleCat.restrictScalars
      (baseMap φ W)).obj (ModuleCat.of _ (R.obj.obj (op W)))) _ _ (k₀ f)).symm
  | smul b a _ ha =>
    obtain ⟨y, hy⟩ := ha
    refine ⟨b • y, ?_⟩
    rw [map_smul, hy]
    exact ModuleCat.ExtendScalars.smul_tmul (f := baseMap φ W) b a (k₀ f)

end KoszulSheaf

end Ringed

open AlgebraicGeometry Koszul

section Local

variable {Y : Scheme.{u}} {V₀ : Y.Opens} (hV₀ : IsAffineOpen V₀)
include hV₀

lemma flat_of_eq_basicOpen (g : Γ(Y, V₀)) (W' : Y.Opens) (hW' : Y.basicOpen g = W')
    (hle : W' ≤ V₀) :
    Module.Flat Γ(Y, V₀) ((ModuleCat.restrictScalars (Y.presheaf.map (homOfLE hle).op).hom).obj
      (ModuleCat.of Γ(Y, W') Γ(Y, W'))) := by
  subst hW'
  let _ := (Y.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have := hV₀.isLocalization_basicOpen g
  have : Module.Flat Γ(Y, V₀) Γ(Y, Y.basicOpen g) := IsLocalization.flat _ (Submonoid.powers g)
  exact this

lemma flat_sections_of_eq_basicOpen {M : Y.Modules} {W₀ : Y.Opens} {m : ℕ}
    (α : M.over W₀ ≅ SheafOfModules.free (ULift.{u} (Fin m))) (hV₀W₀ : V₀ ≤ W₀)
    (g : Γ(Y, V₀)) (W' : Y.Opens) (hW' : Y.basicOpen g = W') (hle : W' ≤ V₀) :
    Module.Flat Γ(Y, V₀) ((ModuleCat.restrictScalars (Y.presheaf.map (homOfLE hle).op).hom).obj
      (M.val.obj (op W'))) := by
  have hS := flat_of_eq_basicOpen hV₀ g W' hW' hle
  let _ := (Y.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : Module.Flat Γ(Y, V₀) Γ(Y, W') := hS
  have : Module.Free Γ(Y, W') Γ(M, W') := module_free_sections_of_iso_free α (hle.trans hV₀W₀)
  let _ : Module Γ(Y, V₀) Γ(M, W') := Module.compHom _ (Y.presheaf.map (homOfLE hle).op).hom
  have : IsScalarTower Γ(Y, V₀) Γ(Y, W') Γ(M, W') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : Module.Flat Γ(Y, V₀) Γ(M, W') := Module.Flat.trans Γ(Y, V₀) Γ(Y, W') Γ(M, W')
  exact this

lemma ker_app_of_eq_basicOpen {X : Scheme.{u}} {i : X ⟶ Y} [IsClosedImmersion i] {r : ℕ}
    {f : Fin r → Γ(Y, V₀)} (hI : i.ker.ideal ⟨V₀, hV₀⟩ = Ideal.span (Set.range f))
    (g : Γ(Y, V₀)) (W' : Y.Opens) (hW' : Y.basicOpen g = W') (hle : W' ≤ V₀) :
    IsAffineOpen W' ∧ RingHom.ker (i.app W').hom =
      Ideal.span (Set.range (fun j => (Y.presheaf.map (homOfLE hle).op).hom (f j))) := by
  subst hW'
  refine ⟨hV₀.basicOpen g, ?_⟩
  rw [← i.ker_apply ⟨_, hV₀.basicOpen g⟩]
  change i.ker.ideal (Y.affineBasicOpen (U := ⟨V₀, hV₀⟩) g) = _
  rw [← i.ker.map_ideal_basicOpen ⟨V₀, hV₀⟩ g, hI, Ideal.map_span, ← Set.range_comp]
  rfl

omit hV₀ in
lemma incl_le (W : Opens ((Opens.toTopCat Y).obj V₀)) : V₀.isOpenEmbedding.functor.obj W ≤ V₀ := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

omit hV₀ in
lemma baseMap_eq (W : Opens ((Opens.toTopCat Y).obj V₀)) :
    Ringed.ScalarExtension.baseMap (R := Ringed.restrictRingSheaf Y.sheaf V₀)
      (Y.presheaf.map (homOfLE (incl_le ⊤)).op).hom W =
        (Y.presheaf.map (homOfLE (incl_le W)).op).hom := by
  ext a
  change (Y.presheaf.map (homOfLE (incl_le ⊤)).op ≫ Y.presheaf.map _) a = _
  rw [← Functor.map_comp]
  rfl

lemma isBasis_basicOpen :
    Opens.IsBasis {W : Opens ((Opens.toTopCat Y).obj V₀) |
      ∃ g : Γ(Y, V₀), Y.basicOpen g = V₀.isOpenEmbedding.functor.obj W} := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨g, hgU, hxg⟩ := hV₀.exists_basicOpen_le (V := V₀.isOpenEmbedding.functor.obj U)
    ⟨x.1, ⟨x, hx, rfl⟩⟩ x.2
  refine ⟨⟨Subtype.val ⁻¹' (Y.basicOpen g), (Y.basicOpen g).isOpen.preimage continuous_subtype_val⟩,
    ⟨g, ?_⟩, hxg, ?_⟩
  · apply Opens.ext
    ext z
    change z ∈ (Y.basicOpen g : Set Y) ↔
      z ∈ Subtype.val '' (Subtype.val ⁻¹' (Y.basicOpen g : Set Y) : Set V₀)
    exact ⟨fun hz => ⟨⟨z, Y.basicOpen_le g hz⟩, hz, rfl⟩, fun ⟨w, hw, hwz⟩ => hwz ▸ hw⟩
  · intro z hz
    obtain ⟨w, hw, hwz⟩ := hgU hz
    rw [Subtype.ext hwz] at hw
    exact hw

omit hV₀ in
/-- The structure map `Γ(Y, V₀) → 𝒪_{V₀}(V₀)` of the open subspace `V₀`. -/
noncomputable def restrictPhi (V₀ : Y.Opens) :
    Γ(Y, V₀) →+* (Ringed.restrictRingSheaf Y.sheaf V₀).obj.obj (op ⊤) :=
  (Y.presheaf.map (homOfLE (incl_le ⊤)).op).hom

variable {X : Scheme.{u}} (i : X ⟶ Y) {r : ℕ} (f : Fin r → Γ(Y, V₀))

omit hV₀ in
/-- The restriction `(i_* 𝒪_X)|_{V₀}`. -/
noncomputable abbrev pushforwardRestrict (V₀ : Y.Opens) :
    SheafOfModules.{u} (ringCatSheafOf (Ringed.restrictRingSheaf Y.sheaf V₀)) :=
  (Ringed.moduleRestrict V₀).obj
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf))

omit hV₀ in
/-- The augmentation `K_0 = ⋀^0 Γ(Y, V₀)^r ⊗ Γ(Y, V₀) → Γ(X, i⁻¹ V₀)`, `k ↦ k · 1`. -/
noncomputable def augLinear :
    (Ringed.KoszulSheaf.K f).X 0 ⟶ (ModuleCat.restrictScalars
      (Ringed.ScalarExtension.baseMap (restrictPhi V₀) ⊤)).obj
        ((pushforwardRestrict i V₀).val.obj (op ⊤)) :=
  ModuleCat.homEquiv.symm (LinearMap.toSpanSingleton _ _
    (show (pushforwardRestrict i V₀).val.obj (op ⊤) from
      (1 : Γ(X, i ⁻¹ᵁ (V₀.isOpenEmbedding.functor.obj ⊤)))) ∘ₗ
    (degreeZeroEquiv (V := Fin r → Γ(Y, V₀)) Γ(Y, V₀)).toLinearMap)

omit hV₀ in
/-- The augmentation `𝒪_{V₀} ⊗ K_0 ⟶ (i_* 𝒪_X)|_{V₀}`. -/
noncomputable def augHom :
    (Ringed.KoszulSheaf.complex (restrictPhi V₀) f).X 0 ⟶ pushforwardRestrict i V₀ :=
  ⟨Ringed.ScalarExtension.homOfLinear (restrictPhi V₀) _ (augLinear i f)⟩

omit hV₀ in
lemma augHom_app_tmul_k₀ (W : Opens ((Opens.toTopCat Y).obj V₀))
    (s : (Ringed.restrictRingSheaf Y.sheaf V₀).obj.obj (op W)) :
    (augHom i f).val.app (op W) (s ⊗ₜ[Γ(Y, V₀), Ringed.ScalarExtension.baseMap (restrictPhi V₀) W]
      Ringed.KoszulSheaf.k₀ f) = (i.app (V₀.isOpenEmbedding.functor.obj W)).hom s := by
  refine (Ringed.ScalarExtension.homOfLinear_app_tmul _ _ (augLinear i f) (op W) s _).trans ?_
  have hc : augLinear i f (Ringed.KoszulSheaf.k₀ f) =
      (show (ModuleCat.restrictScalars (Ringed.ScalarExtension.baseMap (restrictPhi V₀) ⊤)).obj
        ((pushforwardRestrict i V₀).val.obj (op ⊤)) from
          (1 : Γ(X, i ⁻¹ᵁ (V₀.isOpenEmbedding.functor.obj ⊤)))) := by
    change (degreeZeroEquiv (V := Fin r → Γ(Y, V₀)) Γ(Y, V₀) (Ringed.KoszulSheaf.k₀ f)) •
      (show (ModuleCat.restrictScalars (Ringed.ScalarExtension.baseMap (restrictPhi V₀) ⊤)).obj
        ((pushforwardRestrict i V₀).val.obj (op ⊤)) from
          (1 : Γ(X, i ⁻¹ᵁ (V₀.isOpenEmbedding.functor.obj ⊤)))) = _
    rw [show degreeZeroEquiv (V := Fin r → Γ(Y, V₀)) Γ(Y, V₀) (Ringed.KoszulSheaf.k₀ f) = 1 from
      LinearEquiv.apply_symm_apply _ _, one_smul]
  have h1 : (pushforwardRestrict i V₀).val.map (homOfLE (le_top : W ≤ ⊤)).op
      (show (pushforwardRestrict i V₀).val.obj (op ⊤) from
        (1 : Γ(X, i ⁻¹ᵁ (V₀.isOpenEmbedding.functor.obj ⊤)))) =
        (show (pushforwardRestrict i V₀).val.obj (op W) from
          (1 : Γ(X, i ⁻¹ᵁ (V₀.isOpenEmbedding.functor.obj W)))) :=
    map_one (X.presheaf.map _).hom
  rw [hc]
  erw [h1]
  exact mul_one ((i.app (V₀.isOpenEmbedding.functor.obj W)).hom s)

lemma d_comp_augHom [IsClosedImmersion i] (hI : i.ker.ideal ⟨V₀, hV₀⟩ = Ideal.span (Set.range f)) :
    (Ringed.KoszulSheaf.complex (restrictPhi V₀) f).d 1 0 ≫ augHom i f = 0 := by
  have hfj : ∀ j, (i.app (V₀.isOpenEmbedding.functor.obj ⊤)).hom
      ((Y.presheaf.map (homOfLE (incl_le ⊤)).op).hom (f j)) = 0 := by
    intro j
    have h1 : f j ∈ RingHom.ker (i.app V₀).hom := by
      rw [← i.ker_apply ⟨V₀, hV₀⟩, hI]
      exact Ideal.subset_span ⟨j, rfl⟩
    rw [RingHom.mem_ker] at h1
    rw [← CommRingCat.comp_apply, i.naturality, CommRingCat.comp_apply, h1, map_zero]
  have hann : ∀ a ∈ Ideal.span (Set.range f), a • (show (ModuleCat.restrictScalars
      (Ringed.ScalarExtension.baseMap (restrictPhi V₀) ⊤)).obj
        ((pushforwardRestrict i V₀).val.obj (op ⊤)) from
      (1 : Γ(X, i ⁻¹ᵁ (V₀.isOpenEmbedding.functor.obj ⊤)))) = 0 := by
    intro a ha
    refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_)
      (fun b x _ hx => ?_) ha
    · obtain ⟨j, rfl⟩ := hx
      change (i.app _).hom (Ringed.ScalarExtension.baseMap (restrictPhi V₀) ⊤ (f j)) * 1 = 0
      rw [restrictPhi, baseMap_eq ⊤]
      erw [hfj j]
      exact zero_mul _
    · exact zero_smul _ _
    · rw [add_smul, hx, hy, add_zero]
    · rw [smul_eq_mul, mul_smul, hx, smul_zero]
  have hc0 : (Ringed.KoszulSheaf.K f).d 1 0 ≫ augLinear i f = 0 := by
    ext k
    exact hann _ (Ringed.KoszulSheaf.degreeZeroEquiv_d_mem f k)
  apply SheafOfModules.hom_ext
  refine (Ringed.ScalarExtension.presheafMap_comp_homOfLinear _ _ _ (augLinear i f)).trans ?_
  rw [hc0]
  exact Ringed.ScalarExtension.homOfLinear_zero _ _

lemma augHom_exact [IsClosedImmersion i]
    (hI : i.ker.ideal ⟨V₀, hV₀⟩ = Ideal.span (Set.range f)) (W : Opens ((Opens.toTopCat Y).obj V₀))
    (g : Γ(Y, V₀)) (hg : Y.basicOpen g = V₀.isOpenEmbedding.functor.obj W) :
    Function.Exact (((Ringed.KoszulSheaf.complex (restrictPhi V₀) f).d 1 0).val.app (op W))
        ((augHom i f).val.app (op W)) ∧
      Function.Surjective ((augHom i f).val.app (op W)) := by
  obtain ⟨haff, hker⟩ := ker_app_of_eq_basicOpen hV₀ hI g _ hg (incl_le W)
  refine ⟨fun x => ⟨fun hεx => ?_, ?_⟩, fun t => ?_⟩
  · obtain ⟨s, rfl⟩ := Ringed.KoszulSheaf.exists_eq_tmul_k₀ (restrictPhi V₀) f W x
    rw [augHom_app_tmul_k₀] at hεx
    refine Ringed.KoszulSheaf.exists_d_eq_tmul_k₀ (restrictPhi V₀) f W s ?_
    have hs : (show Γ(Y, V₀.isOpenEmbedding.functor.obj W) from s) ∈
        RingHom.ker (i.app (V₀.isOpenEmbedding.functor.obj W)).hom := hεx
    rw [hker] at hs
    rw [restrictPhi, baseMap_eq W]
    exact hs
  · rintro ⟨y, rfl⟩
    exact congrArg (fun ψ => ψ.val.app (op W) y) (d_comp_augHom hV₀ i f hI)
  · obtain ⟨s, rfl⟩ := Scheme.Hom.app_surjective i _ haff t
    exact ⟨_, augHom_app_tmul_k₀ i f W s⟩

/-- **The local Koszul calculation of the lower sheaf Exts.** Let `i : X ⟶ Y` be a closed
immersion, `V₀ ⊆ Y` an affine open on which the ideal of `i` is generated by a Koszul-regular
sequence `f₁, …, f_r`, and `M` an `𝒪_Y`-module which is free of finite rank on an open containing
`V₀`. Then `ℰxtⁿ_Y(i_* 𝒪_X, M)|_{V₀} = 0` for `n < r`. -/
theorem isZero_moduleRestrict_sheafExt [IsClosedImmersion i]
    (hI : i.ker.ideal ⟨V₀, hV₀⟩ = Ideal.span (Set.range f))
    (hf : IsKoszulRegular f (ModuleCat.of Γ(Y, V₀) Γ(Y, V₀))) {M : Y.Modules} {W₀ : Y.Opens}
    {m : ℕ} (α : M.over W₀ ≅ SheafOfModules.free (ULift.{u} (Fin m))) (hV₀W₀ : V₀ ≤ W₀) {n : ℕ}
    (hn : n < r) :
    IsZero ((Ringed.moduleRestrict V₀).obj ((Ringed.sheafExt (R := Y.sheaf)
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf)) n).obj M)) := by
  refine IsZero.of_iso ?_ (Ringed.sheafExtRestrictIso V₀ _ M n)
  have hB := isBasis_basicOpen hV₀
  have hflat : ∀ W ∈ {W : Opens ((Opens.toTopCat Y).obj V₀) |
      ∃ g : Γ(Y, V₀), Y.basicOpen g = V₀.isOpenEmbedding.functor.obj W}, Module.Flat Γ(Y, V₀)
        ((ModuleCat.restrictScalars (Ringed.ScalarExtension.baseMap (restrictPhi V₀) W)).obj
          (ModuleCat.of _ ((Ringed.restrictRingSheaf Y.sheaf V₀).obj.obj (op W)))) := by
    rintro W ⟨g, hg⟩
    rw [restrictPhi, baseMap_eq W]
    exact flat_of_eq_basicOpen hV₀ g _ hg (incl_le W)
  have hG : ∀ W ∈ {W : Opens ((Opens.toTopCat Y).obj V₀) |
      ∃ g : Γ(Y, V₀), Y.basicOpen g = V₀.isOpenEmbedding.functor.obj W}, IsKoszulRegular f
        (ModuleCat.of Γ(Y, V₀) ((ModuleCat.restrictScalars
          (Ringed.ScalarExtension.baseMap (restrictPhi V₀) W)).obj
            (((Ringed.moduleRestrict V₀).obj M).val.obj (op W)))) := by
    rintro W ⟨g, hg⟩
    rw [restrictPhi, baseMap_eq W]
    have := flat_sections_of_eq_basicOpen hV₀ α hV₀W₀ g _ hg (incl_le W)
    exact @IsKoszulRegular.of_flat _ _ _ f hf _ _ _ this
  have := Ringed.KoszulSheaf.quasiIso_augmentation (restrictPhi V₀) f hf (augHom i f)
    (d_comp_augHom hV₀ i f hI) hB hflat (fun W ⟨g, hg⟩ => augHom_exact hV₀ i f hI W g hg)
  exact IsZero.of_iso (Ringed.KoszulSheaf.isZero_homology_homComplex (restrictPhi V₀) f
      ((Ringed.moduleRestrict V₀).obj M) hB hG hn)
    ((Ringed.sheafExtIsoHomologyOfLocallyFreeResolution _
      (Ringed.KoszulSheaf.augmentation (restrictPhi V₀) f (augHom i f) (d_comp_augHom hV₀ i f hI))
      (Ringed.KoszulSheaf.isFiniteLocallyFree_complex (restrictPhi V₀) f) n).app _)

end Local



end Hartshorne
