/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AcyclicResolutionComparison
import Hartshorne.Cohomology.HigherDirectImages
import Hartshorne.Cohomology.SheafCohomologyFlasque
import Hartshorne.Scheme.ClosedExtensionByZero
import Mathlib.Topology.Sheaves.Abelian

/-!
# Closed pushforward preserves cohomology

Hartshorne, *Algebraic Geometry*, III, Lemma 2.10 (pp. 209–210).

Let `i : Y ⟶ X` be the inclusion of a closed subset and `F` an abelian sheaf on `Y`. Then
`H^n(Y, F) ≅ H^n(X, i_* F)` for every `n`, naturally in `F`
(`Hartshorne.closedPushforwardCohomologyIso`,
`Hartshorne.closedPushforwardCohomologyIso_naturality`). The comparison is induced by the
equality of global sections `Γ(Y, F) = Γ(X, i_* F)`: in degree zero it is the composite of the
identifications of both sides with global sections
(`Hartshorne.closedPushforwardCohomologyIso_zero`).

## Proof

This follows the printed proof. Let `F ⟶ J^•` be a flasque resolution of `F` on `Y`. Direct
image along a closed inclusion is extension by zero on stalks, so it is exact
(`Hartshorne.closedPushforward_map_exact`), and direct image preserves flasque sheaves
(Exercise II.1.16(d)). Hence `i_* F ⟶ i_* J^•` is a flasque resolution of `i_* F` on `X`
(`Hartshorne.ClosedPushforward.pushforwardResolution`). Termwise
`Γ(Y, J^k) = Γ(X, i_* J^k)`, and flasque sheaves are acyclic (Proposition 2.5), so by
Proposition 1.2A (Remark 2.5.1) both cohomologies are the cohomology of this one complex
(`Hartshorne.closedPushforwardCohomologyIsoOfFlasqueResolution`). The recorded isomorphism uses
the chosen injective resolution of `F`, which is flasque (Lemma 2.4).

The vanishing of the higher direct images `R^q i_* F` for `q > 0`
(`Hartshorne.isZero_abelianHigherDirectImage_closedSubspaceInclusion`) is recorded as a
consequence of the exactness of `i_*`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject

namespace Hartshorne

universe u

variable {X : TopCat.{u}} (Z : Set X)

namespace ClosedPushforward

/-- The comparison of stalks of the direct image along any continuous map is natural in the
presheaf. -/
theorem stalkPushforward_naturality {Y : TopCat.{u}} (f : Y ⟶ X)
    {P Q : Y.Presheaf AddCommGrpCat.{u}} (φ : P ⟶ Q) (y : Y) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f y)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map φ) ≫
      Q.stalkPushforward AddCommGrpCat.{u} f y =
    P.stalkPushforward AddCommGrpCat.{u} f y ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  erw [TopCat.Presheaf.stalkPushforward_germ, TopCat.Presheaf.stalkPushforward_germ_assoc]
  erw [TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

section AcyclicZero

variable {C : Type*} [Category* C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  {A : C} {K : CochainComplex C ℕ} (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]
  (hK : ∀ i, IsRightAcyclic F (K.X i))

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero, the acyclic-resolution isomorphism `R⁰F(A) ≅ H⁰(F(K•))` is induced by
`F(A) ⟶ F(K⁰)`. -/
theorem toRightDerivedZero_comp_acyclicResolutionIso_zero :
    F.toRightDerivedZero.app A ≫ (acyclicResolutionIso F ε hK 0).hom ≫
        (CochainComplex.isoHomologyπ₀ _).inv ≫
          HomologicalComplex.iCycles ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) 0 =
      F.map (ε.f 0) := by
  simp only [acyclicResolutionIso, AcyclicResolution.homIso₀, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, asIso_inv, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← NatTrans.naturality_assoc, IsIso.hom_inv_id_assoc]
  have h : (AcyclicResolution.cyclesIsoF F K 0).inv ≫
      HomologicalComplex.iCycles ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) 0 =
        F.map (K.iCycles 0) := by
    rw [Iso.inv_comp_eq, AcyclicResolution.cyclesIsoF_hom_map_iCycles]
  rw [h, ← F.map_comp, AcyclicResolution.isoCycles₀_hom_iCycles]

end AcyclicZero

end ClosedPushforward

open ClosedPushforward

local instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
    (closedSubspaceInclusion X Z)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Direct image along the inclusion of a closed subset is exact. -/
theorem closedPushforward_map_exact (hZ : IsClosed Z)
    (S : ShortComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u})) (hS : S.Exact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z))).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact] at hS ⊢
  intro x
  by_cases hx : x ∈ Z
  · refine (ShortComplex.exact_iff_of_iso ?_).2 (hS ⟨x, hx⟩)
    exact ShortComplex.isoMk (closedExtensionByZeroOnImageStalkIso Z S.X₁ ⟨x, hx⟩)
      (closedExtensionByZeroOnImageStalkIso Z S.X₂ ⟨x, hx⟩)
      (closedExtensionByZeroOnImageStalkIso Z S.X₃ ⟨x, hx⟩)
      (stalkPushforward_naturality (closedSubspaceInclusion X Z) S.f.hom ⟨x, hx⟩).symm
      (stalkPushforward_naturality (closedSubspaceInclusion X Z) S.g.hom ⟨x, hx⟩).symm
  · exact ShortComplex.exact_of_isZero_X₂ _
      ((isZero_zero _).of_iso (closedExtensionByZeroOffImageStalkIso Z hZ S.X₂ x hx))

/-- The higher direct images along the inclusion of a closed subset vanish. -/
theorem isZero_abelianHigherDirectImage_closedSubspaceInclusion (hZ : IsClosed Z)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    IsZero ((abelianHigherDirectImage (closedSubspaceInclusion X Z) q).obj F) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  refine IsZero.of_iso ?_ ((injectiveResolution F).isoRightDerivedObj
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)) (n + 1))
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 ?_
  rw [HomologicalComplex.exactAt_iff]
  have h := (injectiveResolution F).cocomplex_exactAt_succ n
  rw [HomologicalComplex.exactAt_iff] at h
  exact closedPushforward_map_exact Z hZ _ h

namespace ClosedPushforward

/-- Direct image along the inclusion of a closed subset preserves homology, being exact. -/
theorem preservesHomology (hZ : IsClosed Z) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).PreservesHomology :=
  ((Functor.exact_tfae _).out 1 2).1 (closedPushforward_map_exact Z hZ)

variable {Z}

/-- Applying the direct image `i_*` to a resolution `F ⟶ J^•` gives `i_* F ⟶ i_* J^•`. -/
def pushforwardResolution {F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}}
    {J : CochainComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ℕ}
    (ε : (CochainComplex.single₀ _).obj F ⟶ J) :
    (CochainComplex.single₀ _).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (closedSubspaceInclusion X Z)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J :=
  (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z))
      (ComplexShape.up ℕ) 0).inv.app F ≫
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (closedSubspaceInclusion X Z)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map ε

theorem pushforwardResolution_f_zero {F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}}
    {J : CochainComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ℕ}
    (ε : (CochainComplex.single₀ _).obj F ⟶ J) :
    (pushforwardResolution ε).f 0 =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).map (ε.f 0) := by
  simp only [pushforwardResolution, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f]
  exact Category.id_comp _

/-- Since `i_*` is exact, `i_* F ⟶ i_* J^•` is again a resolution. -/
theorem quasiIso_pushforwardResolution (hZ : IsClosed Z)
    {F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}}
    {J : CochainComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ℕ}
    (ε : (CochainComplex.single₀ _).obj F ⟶ J) [QuasiIso ε] :
    QuasiIso (pushforwardResolution ε) := by
  have := preservesHomology Z hZ
  unfold pushforwardResolution
  infer_instance

/-- The direct image of a flasque resolution consists of flasque, hence `Γ(X, -)`-acyclic,
sheaves. -/
theorem isRightAcyclic_pushforward_of_isFlasque
    (J : CochainComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ℕ)
    (hJ : ∀ k, (J.X k).IsFlasque) (k : ℕ) :
    IsRightAcyclic (sheafSectionsOver (X := X) ⊤)
      ((((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (closedSubspaceInclusion X Z)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J).X k) := by
  have := hJ k
  exact isRightAcyclic_sheafSectionsOver_top_of_isFlasque
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj (J.X k))

/-- A morphism of resolutions over `g : F ⟶ G` stays one after applying `i_*`. -/
theorem pushforwardResolution_comm {F G : (TopCat.of Z).Sheaf AddCommGrpCat.{u}} (g : F ⟶ G)
    {J K : CochainComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ℕ}
    (εF : (CochainComplex.single₀ _).obj F ⟶ J) (εG : (CochainComplex.single₀ _).obj G ⟶ K)
    (φ : J ⟶ K) (comm : εF ≫ φ = (CochainComplex.single₀ _).map g ≫ εG) :
    pushforwardResolution εF ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
          (closedSubspaceInclusion X Z)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ =
      (CochainComplex.single₀ _).map
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).map g) ≫
        pushforwardResolution εG := by
  have h := congrArg (fun ψ => ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
    (closedSubspaceInclusion X Z)).mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) comm
  simp only [Functor.map_comp] at h
  have h' := (HomologicalComplex.singleMapHomologicalComplex
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z))
    (ComplexShape.up ℕ) 0).inv.naturality g
  dsimp only [pushforwardResolution]
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc]
  congr 1
  exact h'.symm

instance sheafSectionsOver_closedSubspace_additive :
    (sheafSectionsOver (X := TopCat.of Z) ⊤).Additive :=
  sheafSectionsOver_additive _

instance sheafSectionsOver_closedSubspace_preservesFiniteLimits :
    PreservesFiniteLimits (sheafSectionsOver (X := TopCat.of Z) ⊤) :=
  sheafSectionsOver_preservesFiniteLimits _

end ClosedPushforward

/-- **Hartshorne III, Lemma 2.10, from a flasque resolution.** For the inclusion `i : Y ⟶ X` of a
closed subset and a flasque resolution `F ⟶ J^•` of an abelian sheaf `F` on `Y`, both
`H^n(Y, F)` and `H^n(X, i_* F)` are the cohomology of `Γ(Y, J^•) = Γ(X, i_* J^•)`; this gives
`H^n(Y, F) ≅ H^n(X, i_* F)`. -/
def closedPushforwardCohomologyIsoOfFlasqueResolution (hZ : IsClosed Z)
    {F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}}
    {J : CochainComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ℕ}
    (ε : (CochainComplex.single₀ _).obj F ⟶ J) [QuasiIso ε] (hJ : ∀ k, (J.X k).IsFlasque)
    (n : ℕ) :
    (sheafCohomology (TopCat.of Z) n).obj F ≅
      (sheafCohomology X n).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F) :=
  haveI := quasiIso_pushforwardResolution hZ ε
  acyclicResolutionIso (sheafSectionsOver (X := TopCat.of Z) ⊤) ε
      (fun k => @isRightAcyclic_sheafSectionsOver_top_of_isFlasque _ (J.X k) (hJ k)) n ≪≫
    -- `Γ(Y, J^k) = Γ(X, i_* J^k)` holds by definition, so the two complexes of global sections
    -- agree and the isomorphisms compose directly.
      (acyclicResolutionIso (sheafSectionsOver (X := X) ⊤) (pushforwardResolution ε)
        (isRightAcyclic_pushforward_of_isFlasque J hJ) n).symm

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphisms obtained from flasque resolutions are natural with respect to morphisms of
flasque resolutions. -/
theorem closedPushforwardCohomologyIsoOfFlasqueResolution_naturality (hZ : IsClosed Z)
    {F G : (TopCat.of Z).Sheaf AddCommGrpCat.{u}} (g : F ⟶ G)
    {J K : CochainComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ℕ}
    (εF : (CochainComplex.single₀ _).obj F ⟶ J) [QuasiIso εF] (hJ : ∀ k, (J.X k).IsFlasque)
    (εG : (CochainComplex.single₀ _).obj G ⟶ K) [QuasiIso εG] (hK : ∀ k, (K.X k).IsFlasque)
    (φ : J ⟶ K) (comm : εF ≫ φ = (CochainComplex.single₀ _).map g ≫ εG) (n : ℕ) :
    (sheafCohomology (TopCat.of Z) n).map g ≫
        (closedPushforwardCohomologyIsoOfFlasqueResolution Z hZ εG hK n).hom =
      (closedPushforwardCohomologyIsoOfFlasqueResolution Z hZ εF hJ n).hom ≫
        (sheafCohomology X n).map
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).map g) := by
  have := quasiIso_pushforwardResolution hZ εF
  have := quasiIso_pushforwardResolution hZ εG
  have e1 := acyclicResolutionIso_naturality (sheafSectionsOver (X := TopCat.of Z) ⊤) εF
    (fun k => @isRightAcyclic_sheafSectionsOver_top_of_isFlasque _ (J.X k) (hJ k)) εG
    (fun k => @isRightAcyclic_sheafSectionsOver_top_of_isFlasque _ (K.X k) (hK k))
    g φ comm n
  have e2 := acyclicResolutionIso_naturality (sheafSectionsOver (X := X) ⊤)
    (pushforwardResolution εF) (isRightAcyclic_pushforward_of_isFlasque J hJ)
    (pushforwardResolution εG) (isRightAcyclic_pushforward_of_isFlasque K hK)
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).map g)
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (closedSubspaceInclusion X Z)).mapHomologicalComplex _).map φ)
    (pushforwardResolution_comm g εF εG φ comm) n
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq] at e2
  simp only [closedPushforwardCohomologyIsoOfFlasqueResolution, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [reassoc_of% e1, e2]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero the isomorphism obtained from a flasque resolution is the composite of the
identifications of both sides with global sections. -/
theorem closedPushforwardCohomologyIsoOfFlasqueResolution_zero (hZ : IsClosed Z)
    {F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}}
    {J : CochainComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ℕ}
    (ε : (CochainComplex.single₀ _).obj F ⟶ J) [QuasiIso ε] (hJ : ∀ k, (J.X k).IsFlasque) :
    (closedPushforwardCohomologyIsoOfFlasqueResolution Z hZ ε hJ 0).hom =
      (sheafCohomologyZeroIso (X := TopCat.of Z)).hom.app F ≫
        (sheafCohomologyZeroIso (X := X)).inv.app
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F) := by
  have := quasiIso_pushforwardResolution hZ ε
  have hJ' : ∀ k, IsRightAcyclic (sheafSectionsOver (X := TopCat.of Z) ⊤) (J.X k) :=
    fun k => @isRightAcyclic_sheafSectionsOver_top_of_isFlasque _ (J.X k) (hJ k)
  have hK := isRightAcyclic_pushforward_of_isFlasque (X := X) J hJ
  have key : (sheafSectionsOver (⊤ : Opens (TopCat.of Z))).toRightDerivedZero.app F ≫
        (acyclicResolutionIso (sheafSectionsOver (⊤ : Opens (TopCat.of Z))) ε hJ' 0).hom =
      (sheafSectionsOver (⊤ : Opens X)).toRightDerivedZero.app
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F) ≫
      (acyclicResolutionIso (sheafSectionsOver (⊤ : Opens X)) (pushforwardResolution ε)
        hK 0).hom := by
    refine (cancel_mono ((CochainComplex.isoHomologyπ₀ _).inv ≫
      HomologicalComplex.iCycles _ 0)).1 ?_
    have h0 := toRightDerivedZero_comp_acyclicResolutionIso_zero
      (sheafSectionsOver (⊤ : Opens (TopCat.of Z))) ε hJ'
    have h := toRightDerivedZero_comp_acyclicResolutionIso_zero
      (sheafSectionsOver (⊤ : Opens X)) (pushforwardResolution ε) hK
    rw [pushforwardResolution_f_zero] at h
    exact (Category.assoc _ _ _).trans (h0.trans ((Category.assoc _ _ _).trans h).symm)
  refine (Iso.inv_comp_eq ((sheafCohomologyZeroIso (TopCat.of Z)).app F)).1 ?_
  change (sheafSectionsOver (⊤ : Opens (TopCat.of Z))).toRightDerivedZero.app F ≫
      (acyclicResolutionIso (sheafSectionsOver (⊤ : Opens (TopCat.of Z))) ε hJ' 0).hom ≫
        (acyclicResolutionIso (sheafSectionsOver (⊤ : Opens X)) (pushforwardResolution ε)
          hK 0).inv =
      (sheafSectionsOver (⊤ : Opens X)).toRightDerivedZero.app
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F)
  exact (Category.assoc _ _ _).symm.trans ((congrArg
    (fun φ ↦ φ ≫ (acyclicResolutionIso (sheafSectionsOver (⊤ : Opens X))
      (pushforwardResolution ε) hK 0).inv) key).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans
        (Category.comp_id _))))

/-- The chosen injective resolution of an abelian sheaf is a flasque resolution
(Hartshorne III, Lemma 2.4, for abelian sheaves). -/
theorem isFlasque_injectiveResolution_cocomplex {Y : TopCat.{u}} (F : Y.Sheaf AddCommGrpCat.{u})
    (k : ℕ) : ((injectiveResolution F).cocomplex.X k).IsFlasque :=
  injectiveAbelianSheaf_isFlasque _

/-- **Closed pushforward preserves cohomology** (Hartshorne III, Lemma 2.10). For the inclusion
`i : Y ⟶ X` of a closed subset and an abelian sheaf `F` on `Y`, `H^n(Y, F) ≅ H^n(X, i_* F)` for
every `n`. It is computed from the chosen injective resolution of `F`, a flasque resolution. -/
def closedPushforwardCohomologyIso (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    (n : ℕ) :
    (sheafCohomology (TopCat.of Z) n).obj F ≅
      (sheafCohomology X n).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F) :=
  closedPushforwardCohomologyIsoOfFlasqueResolution Z hZ (injectiveResolution F).ι
    (isFlasque_injectiveResolution_cocomplex F) n

/-- The isomorphisms `H^n(Y, F) ≅ H^n(X, i_* F)` are natural in the abelian sheaf `F` on the
closed subset `Y`. -/
theorem closedPushforwardCohomologyIso_naturality (hZ : IsClosed Z)
    {F G : (TopCat.of Z).Sheaf AddCommGrpCat.{u}} (g : F ⟶ G) (n : ℕ) :
    (sheafCohomology (TopCat.of Z) n).map g ≫ (closedPushforwardCohomologyIso Z hZ G n).hom =
      (closedPushforwardCohomologyIso Z hZ F n).hom ≫
        (sheafCohomology X n).map
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).map g) :=
  closedPushforwardCohomologyIsoOfFlasqueResolution_naturality Z hZ g _
    (isFlasque_injectiveResolution_cocomplex F) _ (isFlasque_injectiveResolution_cocomplex G)
    (InjectiveResolution.desc g (injectiveResolution G) (injectiveResolution F))
    (InjectiveResolution.desc_commutes _ _ _) n

/-- The comparison `H^n(Y, F) ≅ H^n(X, i_* F)` is induced by the equality of global sections
`Γ(Y, F) = Γ(X, i_* F)`: in degree zero it is the composite of the identifications of both sides
with global sections. -/
theorem closedPushforwardCohomologyIso_zero (hZ : IsClosed Z)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (closedPushforwardCohomologyIso Z hZ F 0).hom =
      (sheafCohomologyZeroIso (X := TopCat.of Z)).hom.app F ≫
        (sheafCohomologyZeroIso (X := X)).inv.app
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F) :=
  closedPushforwardCohomologyIsoOfFlasqueResolution_zero Z hZ _ _

end Hartshorne
