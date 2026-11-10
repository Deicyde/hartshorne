/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AcyclicResolutionComparison
import Hartshorne.Cohomology.HigherDirectImages
import Hartshorne.Cohomology.SheafCohomology
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The acyclic Leray comparison

Hartshorne, *Algebraic Geometry*, III, Exercise 8.1 (p. 252).

Let `f : X ⟶ Y` be a continuous map and `F` an abelian sheaf on `X` with `R^q f_* F = 0` for
every `q > 0`. Then `H^p(Y, f_* F) ≅ H^p(X, F)` for every `p`, naturally in `F`
(`Hartshorne.acyclicLerayIso`, `Hartshorne.acyclicLerayIso_naturality`).

## Proof

Inverse image of abelian sheaves preserves finite limits, so its right adjoint `f_*` preserves
injective objects. For the chosen injective resolution `F ⟶ I^•`, the complex `f_* I^•` consists
of injective, hence `Γ(Y, -)`-acyclic, sheaves; its cohomology computes `R^q f_* F`, which
vanishes for `q > 0`, and since `f_*` is left exact `f_* F ⟶ f_* I^•` is a resolution. Acyclic
resolutions compute derived functors, and `Γ(Y, f_* I^•) = Γ(X, I^•)` computes `H^p(X, F)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Hartshorne

namespace AcyclicLeray

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

attribute [local instance] Hartshorne.instAdditiveSheafAddCommGrpCatPushforward_hartshorne

/-- Inverse image of abelian sheaves preserves finite limits. -/
instance pullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  have : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    lan_preservesFiniteLimits_of_flat _ (Opens.map f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f) AddCommGrpCat.{u}
    _ _

/-- Direct image of abelian sheaves preserves injective objects, being right adjoint to the
exact inverse image functor. -/
instance pushforward_preservesInjectiveObjects :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesInjectiveObjects where
  injective_obj {I} hI :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).map_injective I hI

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation `f_* F ⟶ f_* I^•` obtained by applying `f_*` to the chosen injective
resolution of `F`. -/
def augmentation (F : X.Sheaf AddCommGrpCat.{u}) :
    (CochainComplex.single₀ _).obj ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map ((injectiveResolution F).ι.f 0), by
      rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp,
        InjectiveResolution.ι_f_zero_comp_complex_d, Functor.map_zero]⟩

@[simp]
theorem augmentation_f_zero (F : X.Sheaf AddCommGrpCat.{u}) :
    (augmentation f F).f 0 =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map ((injectiveResolution F).ι.f 0) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

set_option backward.isDefEq.respectTransparency false in
/-- If `R^q f_* F = 0` for `q > 0`, then `f_* F ⟶ f_* I^•` is a resolution. -/
theorem quasiIso_augmentation (F : X.Sheaf AddCommGrpCat.{u})
    (hF : ∀ q, 0 < q → IsZero ((abelianHigherDirectImage f q).obj F)) :
    QuasiIso (augmentation f F) := by
  rw [quasiIso_iff]
  intro n
  rcases n with _ | n
  · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · have hm : Mono ((augmentation f F).f 0) := by
        rw [augmentation_f_zero]
        exact Functor.map_mono _ _
      refine ⟨?_, hm⟩
      have hex := (injectiveResolution F).exact₀.map_of_mono_of_preservesKernel
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) inferInstance inferInstance
      refine (ShortComplex.exact_iff_of_iso ?_).1 hex
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [augmentation_f_zero]) (by simp)
    all_goals first
      | rfl
      | exact HomologicalComplex.shape (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex) 0 0
            (fun h ↦ Nat.succ_ne_zero 0 h)
  · rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ n),
      HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hF (n + 1) (Nat.succ_pos n)).of_iso
      ((injectiveResolution F).isoRightDerivedObj
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) (n + 1)).symm

theorem isRightAcyclic_pushforward_injectiveResolution (F : X.Sheaf AddCommGrpCat.{u}) (i : ℕ) :
    IsRightAcyclic (sheafSectionsOver (X := Y) ⊤)
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj ((injectiveResolution F).cocomplex.X i)) :=
  fun n ↦ (sheafSectionsOver (X := Y) ⊤).isZero_rightDerived_obj_injective_succ n _

end AcyclicLeray

open AcyclicLeray

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- **Hartshorne III, Exercise 8.1.** Let `f : X ⟶ Y` be a continuous map and `F` an abelian
sheaf on `X` with `R^q f_* F = 0` for every `q > 0`. Then `H^p(Y, f_* F) ≅ H^p(X, F)` for every
`p`. -/
def acyclicLerayIso (F : X.Sheaf AddCommGrpCat.{u})
    (hF : ∀ q, 0 < q → IsZero ((abelianHigherDirectImage f q).obj F)) (p : ℕ) :
    (sheafCohomology Y p).obj ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) ≅
      (sheafCohomology X p).obj F :=
  haveI := quasiIso_augmentation f F hF
  acyclicResolutionIso (sheafSectionsOver (X := Y) ⊤) (augmentation f F)
      (isRightAcyclic_pushforward_injectiveResolution f F) p ≪≫
    ((injectiveResolution F).isoRightDerivedObj (sheafSectionsOver (X := X) ⊤) p).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Hartshorne III, Exercise 8.1 (naturality).** The isomorphisms
`H^p(Y, f_* F) ≅ H^p(X, F)` are natural in the abelian sheaf `F` with `R^q f_* F = 0` for
`q > 0`. -/
theorem acyclicLerayIso_naturality {F G : X.Sheaf AddCommGrpCat.{u}} (g : F ⟶ G)
    (hF : ∀ q, 0 < q → IsZero ((abelianHigherDirectImage f q).obj F))
    (hG : ∀ q, 0 < q → IsZero ((abelianHigherDirectImage f q).obj G)) (p : ℕ) :
    (sheafCohomology Y p).map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g) ≫
        (acyclicLerayIso f G hG p).hom =
      (acyclicLerayIso f F hF p).hom ≫ (sheafCohomology X p).map g := by
  have := quasiIso_augmentation f F hF
  have := quasiIso_augmentation f G hG
  let φ := InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F)
  have comm : augmentation f F ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map φ =
        (CochainComplex.single₀ _).map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g) ≫
          augmentation f G := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, augmentation_f_zero,
      augmentation_f_zero, CochainComplex.single₀_map_f_zero,
      Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, ← Functor.map_comp,
      InjectiveResolution.desc_commutes_zero]
  have e1 := acyclicResolutionIso_naturality (sheafSectionsOver (X := Y) ⊤) (augmentation f F)
    (isRightAcyclic_pushforward_injectiveResolution f F) (augmentation f G)
    (isRightAcyclic_pushforward_injectiveResolution f G)
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map g)
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map φ) comm p
  have e2 := InjectiveResolution.isoRightDerivedObj_inv_naturality g (injectiveResolution F)
    (injectiveResolution G) φ (InjectiveResolution.desc_commutes_zero _ _ _)
    (sheafSectionsOver (X := X) ⊤) p
  simp only [acyclicLerayIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% e1, e2]
  rfl

end Hartshorne
