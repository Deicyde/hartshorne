/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AcyclicLerayComparison
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

Direct image along a closed inclusion is extension by zero on stalks, so it is exact
(`Hartshorne.closedPushforward_map_exact`). It is also right adjoint to the exact inverse image,
so it preserves injective objects. Applying `i_*` to an injective resolution `F ⟶ I^•` therefore
gives a resolution `i_* F ⟶ i_* I^•` by injective, hence acyclic, sheaves on `X`, and
`Γ(X, i_* I^•) = Γ(Y, I^•)`. Equivalently, the higher direct images `R^q i_* F` vanish for
`q > 0`, and the comparison is the acyclic Leray isomorphism.
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

omit [PreservesFiniteLimits F] in
set_option backward.isDefEq.respectTransparency false in
/-- In degree zero, `F(A) ⟶ R⁰F(A) ≅ H⁰(F(I•))` is induced by `F(A) ⟶ F(I⁰)`. -/
theorem toRightDerivedZero_comp_isoRightDerivedObj_zero (I : InjectiveResolution A) :
    F.toRightDerivedZero.app A ≫ (I.isoRightDerivedObj F 0).hom ≫
        (CochainComplex.isoHomologyπ₀ _).inv ≫
          HomologicalComplex.iCycles ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            I.cocomplex) 0 =
      F.map (I.ι.f 0) := by
  rw [I.toRightDerivedZero_eq F]
  simp

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

/-- **Closed pushforward preserves cohomology** (Hartshorne III, Lemma 2.10). For the inclusion
`i : Y ⟶ X` of a closed subset and an abelian sheaf `F` on `Y`, `H^n(Y, F) ≅ H^n(X, i_* F)` for
every `n`. -/
def closedPushforwardCohomologyIso (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u})
    (n : ℕ) :
    (sheafCohomology (TopCat.of Z) n).obj F ≅
      (sheafCohomology X n).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F) :=
  (acyclicLerayIso (closedSubspaceInclusion X Z) F
    (isZero_abelianHigherDirectImage_closedSubspaceInclusion Z hZ F) n).symm

/-- The isomorphisms `H^n(Y, F) ≅ H^n(X, i_* F)` are natural in the abelian sheaf `F` on the
closed subset `Y`. -/
theorem closedPushforwardCohomologyIso_naturality (hZ : IsClosed Z)
    {F G : (TopCat.of Z).Sheaf AddCommGrpCat.{u}} (g : F ⟶ G) (n : ℕ) :
    (sheafCohomology (TopCat.of Z) n).map g ≫ (closedPushforwardCohomologyIso Z hZ G n).hom =
      (closedPushforwardCohomologyIso Z hZ F n).hom ≫
        (sheafCohomology X n).map
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).map g) := by
  simp only [closedPushforwardCohomologyIso, Iso.symm_hom]
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (acyclicLerayIso_naturality (closedSubspaceInclusion X Z) g _ _ n).symm

/-- The comparison `H^n(Y, F) ≅ H^n(X, i_* F)` is induced by the equality of global sections
`Γ(Y, F) = Γ(X, i_* F)`: in degree zero it is the composite of the identifications of both sides
with global sections. -/
theorem closedPushforwardCohomologyIso_zero (hZ : IsClosed Z)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (closedPushforwardCohomologyIso Z hZ F 0).hom =
      (sheafCohomologyZeroIso (X := TopCat.of Z)).hom.app F ≫
        (sheafCohomologyZeroIso (X := X)).inv.app
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F) := by
  have hF := isZero_abelianHigherDirectImage_closedSubspaceInclusion Z hZ F
  have := AcyclicLeray.quasiIso_augmentation (closedSubspaceInclusion X Z) F hF
  have hK := AcyclicLeray.isRightAcyclic_pushforward_injectiveResolution
    (closedSubspaceInclusion X Z) F
  have := sheafSectionsOver_additive (⊤ : Opens (TopCat.of Z))
  let I := injectiveResolution F
  let ε := AcyclicLeray.augmentation (closedSubspaceInclusion X Z) F
  have key : (sheafSectionsOver (⊤ : Opens (TopCat.of Z))).toRightDerivedZero.app F ≫
        (I.isoRightDerivedObj (sheafSectionsOver (⊤ : Opens (TopCat.of Z))) 0).hom =
      (sheafSectionsOver (⊤ : Opens X)).toRightDerivedZero.app
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F) ≫
      (acyclicResolutionIso (sheafSectionsOver (⊤ : Opens X)) ε hK 0).hom := by
    refine (cancel_mono ((CochainComplex.isoHomologyπ₀ _).inv ≫
      HomologicalComplex.iCycles _ 0)).1 ?_
    have h0 := toRightDerivedZero_comp_isoRightDerivedObj_zero
      (sheafSectionsOver (⊤ : Opens (TopCat.of Z))) I
    have h := toRightDerivedZero_comp_acyclicResolutionIso_zero
      (sheafSectionsOver (⊤ : Opens X)) ε hK
    rw [AcyclicLeray.augmentation_f_zero] at h
    exact (Category.assoc _ _ _).trans (h0.trans ((Category.assoc _ _ _).trans h).symm)
  refine (Iso.inv_comp_eq ((sheafCohomologyZeroIso (TopCat.of Z)).app F)).1 ?_
  change (sheafSectionsOver (⊤ : Opens (TopCat.of Z))).toRightDerivedZero.app F ≫
      (I.isoRightDerivedObj (sheafSectionsOver (⊤ : Opens (TopCat.of Z))) 0).hom ≫
        (acyclicResolutionIso (sheafSectionsOver (⊤ : Opens X)) ε hK 0).inv =
      (sheafSectionsOver (⊤ : Opens X)).toRightDerivedZero.app
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F)
  exact (Category.assoc _ _ _).symm.trans ((congrArg
    (fun φ ↦ φ ≫ (acyclicResolutionIso (sheafSectionsOver (⊤ : Opens X)) ε hK 0).inv) key).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans
        (Category.comp_id _))))

end Hartshorne
