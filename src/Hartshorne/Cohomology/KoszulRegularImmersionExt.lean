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

end KoszulSheaf

end Ringed

end Hartshorne
