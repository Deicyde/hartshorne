/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.RightDerivedPullback
import Hartshorne.Weil.RationalEllAdicCohomology

/-!
# Functoriality of ℓ-adic cohomology

For a morphism of schemes `f : X ⟶ Y` and a prime `ℓ`, this file constructs the pullback

`f^* : H^i_et(Y, ℚ_ℓ) ⟶ H^i_et(X, ℚ_ℓ)`

as a morphism of `ℚ_[ℓ]`-modules, and proves `(𝟙_X)^* = 𝟙` and `(f ≫ g)^* = g^* ≫ f^*`, i.e.
`(g ∘ f)^* = f^* ∘ g^*`.  Together these give the functor `rationalEllAdicCohomologyFunctor`
from `Schemeᵒᵖ` to `ℚ_[ℓ]`-modules.

## Strategy

The torsion pullback `torsionEtaleCohomologyPullback` is built from a chosen comparison of
injective resolutions through the inverse image.  We identify it
(`torsionEtaleCohomologyPullback_eq_pullback`) with the map of right derived functors
`Hartshorne.RightDerivedPullback.pullback` induced by the morphism `ℤ/ℓ^r ⟶ f_* ℤ/ℓ^r` of
constant sheaves (`constantSheafToEtalePushforward`), which is described through global
sections only.  The abstract pullback is independent of all choices and satisfies naturality,
composition and identity laws, as soon as the identification `Γ(Y, f_* -) ≅ Γ(X, -)` is
compatible with `(f ≫ g)_* ≅ g_* f_*` and `(𝟙_X)_* ≅ 𝟭`; these compatibilities
(`etalePushforwardCompΓ_comp`, `etalePushforwardCompΓ_id`) are checked by restricting global
sections to a terminal object of the small étale site.

The torsion pullbacks then commute with the reductions `ℤ/ℓ^s → ℤ/ℓ^r`, so they induce a map of
inverse limits `classicalEllAdicCohomologyPullback`; it is `ℤ_[ℓ]`-linear because additive maps
commute with multiplication by natural numbers, and its scalar extension to `ℚ_[ℓ]` is
`rationalEllAdicCohomologyPullback`.
-/

open CategoryTheory Limits Opposite

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Sheaf

universe v u w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type w}
  [Category.{w'} A] [HasWeakSheafify J A] [HasTerminal C]

/-- On a site with a terminal object `T`, the identification of global sections with sections
over `T` is the restriction map to `T`. -/
theorem ΓNatIsoSheafSections_hom_app {T : C} (hT : IsTerminal T) (F : Sheaf J A) :
    (ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app (constantSheafΓAdj J A)
    (constantSheafAdj J A hT) F
  rw [Equiv.symm_apply_eq] at h
  rw [ΓNatIsoSheafSections, h]
  have e1 : ((constantSheafΓAdj J A).homEquiv _ _).symm (𝟙 ((Γ J A).obj F)) =
      (constantSheafΓAdj J A).counit.app F := Adjunction.homEquiv_symm_id _ _
  unfold ΓRes coneΓ ΓHomEquiv
  dsimp only
  rw [Equiv.symm_trans_apply, Equiv.symm_symm]
  refine Eq.trans ?_ (congrArg (fun φ : (presheafToSheaf J A).obj
    ((Functor.const Cᵒᵖ).obj ((Γ J A).obj F)) ⟶ F ↦
      NatTrans.app (((sheafificationAdjunction J A).homEquiv _ F) φ) (op T)) e1.symm)
  unfold constantSheafAdj
  rw [Adjunction.comp_homEquiv]
  exact Category.id_comp (obj := A) _

/-- On a site with a terminal object `T`, two morphisms into the global sections of a sheaf are
equal once their restrictions to `T` are. -/
theorem Γ_hom_ext {T : C} (hT : IsTerminal T) {F : Sheaf J A} {W : A}
    {a b : W ⟶ (Γ J A).obj F} (h : a ≫ F.ΓRes (op T) = b ≫ F.ΓRes (op T)) : a = b := by
  rw [← ΓNatIsoSheafSections_hom_app hT] at h
  exact (cancel_mono _).1 h

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

universe u

open Hartshorne

variable {X Y Z : Scheme.{u}}

instance preservesInjectiveObjects_etalePushforward (f : X ⟶ Y) :
    (etalePushforward f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafAdjunctionContinuous (etaleBaseChange f) Ab.{u} _ _)

/-- The identification of global sections of a direct image with global sections, followed by
restriction to the base change `V ×_Y X` of an étale `Y`-scheme `V`, is restriction to `V`. -/
theorem etalePushforwardCompΓ_hom_app_comp_ΓRes (f : X ⟶ Y)
    (J : Sheaf X.smallEtaleTopology Ab.{u}) (V : Y.Etale) :
    (etalePushforwardCompΓ f).hom.app J ≫ J.ΓRes (op ((etaleBaseChange f).obj V)) =
      ((etalePushforward f).obj J).ΓRes (op V) := by
  have h1 : (etalePushforwardCompΓ f).hom.app J =
      ((etalePushforward f).obj J).ΓRes (op _) ≫
        (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleBaseChangeObj f)).inv.app J := by
    simp [etalePushforwardCompΓ, Sheaf.ΓNatIsoSheafSections_hom_app]
    rfl
  have h2 := J.ΓRes_map ((etaleBaseChange f).map
    ((MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) Y).from V)).op
  have h3 := ((etalePushforward f).obj J).ΓRes_map
    ((MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) Y).from V).op
  rw [h1, ← h2, ← h3, ← Sheaf.ΓNatIsoSheafSections_hom_app (isTerminalEtaleBaseChangeObj f),
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

/-- Base change along a composite is the composite of the base changes. -/
noncomputable def etaleBaseChangeComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleBaseChange g ⋙ etaleBaseChange f ≅ etaleBaseChange (f ≫ g) :=
  (MorphismProperty.Over.pullbackComp f g).symm

/-- Base change along the identity is isomorphic to the identity functor: both are right
adjoint to the identity. -/
noncomputable def etaleBaseChangeId (X : Scheme.{u}) : etaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  ((MorphismProperty.Over.mapPullbackAdj (@AlgebraicGeometry.Etale) ⊤ (𝟙 X)
    (MorphismProperty.id_mem _ X) trivial).ofNatIsoLeft
      (MorphismProperty.Over.mapId ⊤ X)).rightAdjointUniq Adjunction.id

/-- The direct image along a composite is the composite of the direct images. -/
noncomputable def etalePushforwardComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    etalePushforward f ⋙ etalePushforward g ≅ etalePushforward (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (etaleBaseChangeComp f g) Ab.{u}
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- The direct image along the identity is isomorphic to the identity functor. -/
noncomputable def etalePushforwardId (X : Scheme.{u}) : etalePushforward (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (etaleBaseChangeId X) Ab.{u} X.smallEtaleTopology

/-- The identifications of global sections of direct images are compatible with composition. -/
theorem etalePushforwardCompΓ_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (J : Sheaf X.smallEtaleTopology Ab.{u}) :
    (etalePushforwardCompΓ g).hom.app ((etalePushforward f).obj J) ≫
        (etalePushforwardCompΓ f).hom.app J =
      (Sheaf.Γ Z.smallEtaleTopology Ab.{u}).map ((etalePushforwardComp f g).hom.app J) ≫
        (etalePushforwardCompΓ (f ≫ g)).hom.app J := by
  let TZ : Z.Etale := MorphismProperty.Over.mk ⊤ (𝟙 Z) (MorphismProperty.id_mem
    (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) Z)
  have hTZ : IsTerminal TZ := MorphismProperty.Over.mkIdTerminal _ Z
  have hT : IsTerminal ((etaleBaseChange f).obj ((etaleBaseChange g).obj TZ)) :=
    IsTerminal.isTerminalObj _ _ (IsTerminal.isTerminalObj _ _ hTZ)
  have hT' : IsTerminal ((etaleBaseChange (f ≫ g)).obj TZ) := IsTerminal.isTerminalObj _ _ hTZ
  refine Sheaf.Γ_hom_ext hT ?_
  refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (etalePushforwardCompΓ_hom_app_comp_ΓRes f J ((etaleBaseChange g).obj TZ))).trans
      (etalePushforwardCompΓ_hom_app_comp_ΓRes g _ TZ))).trans ?_
  rw [← J.ΓRes_map (hT'.from ((etaleBaseChange f).obj ((etaleBaseChange g).obj TZ))).op,
    Category.assoc, reassoc_of% etalePushforwardCompΓ_hom_app_comp_ΓRes,
    ← Category.assoc, Sheaf.ΓRes_naturality, Category.assoc]
  conv_lhs => rw [← Category.comp_id (Sheaf.ΓRes _ _)]
  congr 1
  change 𝟙 _ = (𝟙 _ ≫ J.obj.map ((etaleBaseChangeComp f g).inv.app TZ).op) ≫
    J.obj.map (hT'.from ((etaleBaseChange f).obj ((etaleBaseChange g).obj TZ))).op
  rw [Category.id_comp, ← Functor.map_comp, ← op_comp, hT.hom_ext (_ ≫ _) (𝟙 _)]
  exact (J.obj.map_id _).symm

/-- The identification of global sections of the direct image along the identity is induced by
the isomorphism of that direct image with the identity. -/
theorem etalePushforwardCompΓ_id (X : Scheme.{u}) (J : Sheaf X.smallEtaleTopology Ab.{u}) :
    (etalePushforwardCompΓ (𝟙 X)).hom.app J =
      (Sheaf.Γ X.smallEtaleTopology Ab.{u}).map ((etalePushforwardId X).hom.app J) := by
  have hT := isTerminalEtaleBaseChangeObj (𝟙 X)
  have hTX := MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) X
  refine Sheaf.Γ_hom_ext hT ?_
  refine (etalePushforwardCompΓ_hom_app_comp_ΓRes _ J _).trans ?_
  refine Eq.trans ?_ (Sheaf.ΓRes_naturality _ _).symm
  rw [← ((etalePushforward (𝟙 X)).obj J).ΓRes_map
    (hTX.from ((etaleBaseChange (𝟙 X)).obj _)).op, Category.assoc]
  conv_lhs => rw [← Category.comp_id (Sheaf.ΓRes _ _)]
  congr 1
  change 𝟙 _ = J.obj.map ((etaleBaseChange (𝟙 X)).map
      (hTX.from ((etaleBaseChange (𝟙 X)).obj _))).op ≫
    (J.obj.map ((etaleBaseChangeId X).inv.app ((etaleBaseChange (𝟙 X)).obj _)).op ≫ 𝟙 _)
  rw [Category.comp_id, ← Functor.map_comp, ← op_comp, hT.hom_ext (_ ≫ _) (𝟙 _)]
  exact (J.obj.map_id _).symm

/-- The pullback map `H^i_et(Y, F) ⟶ H^i_et(X, f⁻¹ F)` is the map of right derived functors of
global sections induced by the adjunction unit `F ⟶ f_* f⁻¹ F`. -/
theorem etaleCohomologyPullback_eq_pullback (f : X ⟶ Y) (F : Sheaf Y.smallEtaleTopology Ab.{u})
    (i : ℕ) :
    etaleCohomologyPullback f F i = RightDerivedPullback.pullback (etalePushforwardCompΓ f)
      ((Functor.sheafAdjunctionContinuous (etaleBaseChange f) Ab.{u} _ _).unit.app F) i := by
  let adj := Functor.sheafAdjunctionContinuous (etaleBaseChange f) Ab.{u}
    Y.smallEtaleTopology X.smallEtaleTopology
  have hφ := HomologicalComplex.congr_hom
    (Hartshorne.resolutionToInjectiveComparison_exists_uniqueUpToHomotopy
      (etaleInverseImageResolutionAugmentation f F)
      (injectiveResolution ((etaleInverseImage f).obj F))).1.some.2 0
  simp [etaleInverseImageResolutionAugmentation, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq] at hφ
  rw [RightDerivedPullback.pullback_eq _ _ i (etaleCohomologyPullbackCochainMap f F)]
  · rfl
  · change _ ≫ adj.homEquiv _ _ _ = _
    have hφ' : (etaleInverseImage f).map ((injectiveResolution F).ι.f 0) ≫
        (etaleInverseImageComparison f F).f 0 =
          (injectiveResolution ((etaleInverseImage f).obj F)).ι.f 0 := hφ
    rw [← adj.homEquiv_naturality_left]
    erw [hφ']
    exact adj.homEquiv_unit _ _ _

/-- The morphism `M_Y ⟶ f_* M_X` of constant sheaves with value `M`, adjoint (constant sheaf ⊣
global sections) to `M ⟶ Γ(X, M_X) ≅ Γ(Y, f_* M_X)`. -/
noncomputable def constantSheafToEtalePushforward (f : X ⟶ Y) (M : Ab.{u}) :
    (constantSheaf Y.smallEtaleTopology Ab.{u}).obj M ⟶
      (etalePushforward f).obj ((constantSheaf X.smallEtaleTopology Ab.{u}).obj M) :=
  ((constantSheafΓAdj _ _).homEquiv _ _).symm
    ((constantSheafΓAdj _ _).unit.app M ≫ (etalePushforwardCompΓ f).inv.app _)

theorem homEquiv_constantSheafToEtalePushforward (f : X ⟶ Y) (M : Ab.{u}) :
    (constantSheafΓAdj Y.smallEtaleTopology Ab.{u}).homEquiv _ _
        (constantSheafToEtalePushforward f M) =
      (constantSheafΓAdj _ _).unit.app M ≫ (etalePushforwardCompΓ f).inv.app _ :=
  Equiv.apply_symm_apply _ _

theorem constantSheafToEtalePushforward_naturality (f : X ⟶ Y) {M N : Ab.{u}} (u : M ⟶ N) :
    constantSheafToEtalePushforward f M ≫
        (etalePushforward f).map ((constantSheaf X.smallEtaleTopology Ab.{u}).map u) =
      (constantSheaf Y.smallEtaleTopology Ab.{u}).map u ≫ constantSheafToEtalePushforward f N := by
  apply ((constantSheafΓAdj Y.smallEtaleTopology Ab.{u}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    homEquiv_constantSheafToEtalePushforward, homEquiv_constantSheafToEtalePushforward]
  have h1 :=
    (etalePushforwardCompΓ f).inv.naturality ((constantSheaf X.smallEtaleTopology Ab.{u}).map u)
  have h2 := (constantSheafΓAdj X.smallEtaleTopology Ab.{u}).unit.naturality u
  simp only [Functor.comp_map, Functor.id_map] at h1 h2
  rw [Category.assoc, ← h1, ← Category.assoc, ← h2, Category.assoc]

theorem constantSheafToEtalePushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Ab.{u}) :
    constantSheafToEtalePushforward g M ≫
        (etalePushforward g).map (constantSheafToEtalePushforward f M) ≫
          (etalePushforwardComp f g).hom.app _ =
      constantSheafToEtalePushforward (f ≫ g) M := by
  apply ((constantSheafΓAdj Z.smallEtaleTopology Ab.{u}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, CategoryTheory.Functor.map_comp,
    homEquiv_constantSheafToEtalePushforward, homEquiv_constantSheafToEtalePushforward]
  have h1 := (etalePushforwardCompΓ g).inv.naturality (constantSheafToEtalePushforward f M)
  have h2 := homEquiv_constantSheafToEtalePushforward f M
  rw [Adjunction.homEquiv_unit] at h2
  have h3 := etalePushforwardCompΓ_comp f g ((constantSheaf X.smallEtaleTopology Ab.{u}).obj M)
  simp only [Functor.comp_map] at h1
  rw [← cancel_mono ((etalePushforwardCompΓ (f ≫ g)).hom.app _)]
  simp only [Category.assoc, ← h3, Iso.inv_hom_id_app]
  rw [← reassoc_of% h1, reassoc_of% h2]
  simp

theorem constantSheafToEtalePushforward_id (X : Scheme.{u}) (M : Ab.{u}) :
    constantSheafToEtalePushforward (𝟙 X) M ≫ (etalePushforwardId X).hom.app _ = 𝟙 _ := by
  apply ((constantSheafΓAdj X.smallEtaleTopology Ab.{u}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, homEquiv_constantSheafToEtalePushforward,
    ← etalePushforwardCompΓ_id, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- The inverse image of the constant sheaf, identified with the constant sheaf, corresponds under
the adjunction to `constantSheafToEtalePushforward`. -/
theorem unit_comp_map_constantSheafCompEtaleInverseImageIso (f : X ⟶ Y) (M : Ab.{u}) :
    (Functor.sheafAdjunctionContinuous (etaleBaseChange f) Ab.{u} _ _).unit.app
        ((constantSheaf Y.smallEtaleTopology Ab.{u}).obj M) ≫
      (etalePushforward f).map ((constantSheafCompEtaleInverseImageIso f).hom.app M) =
      constantSheafToEtalePushforward f M := by
  let adjf := Functor.sheafAdjunctionContinuous (etaleBaseChange f) Ab.{u}
    Y.smallEtaleTopology X.smallEtaleTopology
  let adj1 := ((constantSheafΓAdj Y.smallEtaleTopology Ab.{u}).comp adjf).ofNatIsoRight
    (etalePushforwardCompΓ f)
  have h : adj1.unit.app M ≫ (Sheaf.Γ X.smallEtaleTopology Ab.{u}).map
      ((constantSheafCompEtaleInverseImageIso f).hom.app M) =
        (constantSheafΓAdj X.smallEtaleTopology Ab.{u}).unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app adj1 _ M
  have hu : adj1.unit.app M = (constantSheafΓAdj Y.smallEtaleTopology Ab.{u}).unit.app M ≫
      (Sheaf.Γ Y.smallEtaleTopology Ab.{u}).map (adjf.unit.app _) ≫
        (etalePushforwardCompΓ f).hom.app _ := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.homEquiv_id, Adjunction.comp_unit_app, Category.assoc]
    rfl
  have hn := (etalePushforwardCompΓ f).hom.naturality
    ((constantSheafCompEtaleInverseImageIso f).hom.app M)
  simp only [Functor.comp_map] at hn
  apply ((constantSheafΓAdj Y.smallEtaleTopology Ab.{u}).homEquiv _ _).injective
  rw [homEquiv_constantSheafToEtalePushforward, ← cancel_mono
    ((etalePushforwardCompΓ f).hom.app _), Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, hn,
    ← h, hu]
  simp only [Category.assoc]
  rfl

/-- The pullback `H^i_et(Y, ℤ/ℓ^r) ⟶ H^i_et(X, ℤ/ℓ^r)` is the map of right derived functors of
global sections induced by the morphism `ℤ/ℓ^r ⟶ f_* ℤ/ℓ^r` of constant sheaves. -/
theorem torsionEtaleCohomologyPullback_eq_pullback (f : X ⟶ Y) (ℓ r i : ℕ) :
    torsionEtaleCohomologyPullback f ℓ r i =
      RightDerivedPullback.pullback (etalePushforwardCompΓ f)
        (constantSheafToEtalePushforward f _) i := by
  unfold torsionEtaleCohomologyPullback
  rw [etaleCohomologyPullback_eq_pullback, RightDerivedPullback.pullback_comp_rightDerived_map]
  exact congrArg (fun a ↦ RightDerivedPullback.pullback (etalePushforwardCompΓ f) a i)
    (unit_comp_map_constantSheafCompEtaleInverseImageIso f _)

/-- The torsion pullback maps commute with the reduction maps `ℤ/ℓ^s → ℤ/ℓ^r` (`r ≤ s`). -/
theorem torsionEtaleCohomologyPullback_naturality (f : X ⟶ Y) (ℓ i : ℕ) {r s : ℕ} (h : r ≤ s) :
    torsionEtaleCohomologyPullback f ℓ s i ≫
        ((Sheaf.Γ X.smallEtaleTopology Ab.{u}).rightDerived i).map
          (X.constantTorsionEtaleSheafReduction ℓ h) =
      ((Sheaf.Γ Y.smallEtaleTopology Ab.{u}).rightDerived i).map
          (Y.constantTorsionEtaleSheafReduction ℓ h) ≫
        torsionEtaleCohomologyPullback f ℓ r i := by
  rw [torsionEtaleCohomologyPullback_eq_pullback, torsionEtaleCohomologyPullback_eq_pullback,
    RightDerivedPullback.pullback_comp_rightDerived_map,
    RightDerivedPullback.rightDerived_map_comp_pullback]
  exact congrArg (fun a ↦ RightDerivedPullback.pullback (etalePushforwardCompΓ f) a i)
    (constantSheafToEtalePushforward_naturality f _)

/-- Identity law for the torsion pullback maps. -/
theorem torsionEtaleCohomologyPullback_id (X : Scheme.{u}) (ℓ r i : ℕ) :
    torsionEtaleCohomologyPullback (𝟙 X) ℓ r i = 𝟙 _ := by
  rw [torsionEtaleCohomologyPullback_eq_pullback,
    RightDerivedPullback.pullback_eq_rightDerived_map (etalePushforwardCompΓ (𝟙 X))
      (etalePushforwardId X) (etalePushforwardCompΓ_id X),
    constantSheafToEtalePushforward_id, CategoryTheory.Functor.map_id]
  rfl

/-- Composition law for the torsion pullback maps. -/
theorem torsionEtaleCohomologyPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (ℓ r i : ℕ) :
    torsionEtaleCohomologyPullback (f ≫ g) ℓ r i =
      torsionEtaleCohomologyPullback g ℓ r i ≫ torsionEtaleCohomologyPullback f ℓ r i := by
  rw [torsionEtaleCohomologyPullback_eq_pullback, torsionEtaleCohomologyPullback_eq_pullback,
    torsionEtaleCohomologyPullback_eq_pullback,
    RightDerivedPullback.pullback_comp_pullback (etalePushforwardCompΓ f) (etalePushforwardCompΓ g)
      (etalePushforwardCompΓ (f ≫ g)) (etalePushforwardComp f g) (etalePushforwardCompΓ_comp f g),
    constantSheafToEtalePushforward_comp]

/-- The pullback morphism `(r ↦ H^i_et(Y, ℤ/ℓ^r)) ⟶ (r ↦ H^i_et(X, ℤ/ℓ^r))` of classical inverse
systems. -/
noncomputable def torsionEtaleCohomologySystemPullback (f : X ⟶ Y) (ℓ i : ℕ) :
    Y.torsionEtaleCohomologySystem ℓ i ⟶ X.torsionEtaleCohomologySystem ℓ i where
  app r := torsionEtaleCohomologyPullback f ℓ r.unop i
  naturality _ _ g := (torsionEtaleCohomologyPullback_naturality f ℓ i (leOfHom g.unop)).symm

theorem torsionEtaleCohomologySystemPullback_id (X : Scheme.{u}) (ℓ i : ℕ) :
    torsionEtaleCohomologySystemPullback (𝟙 X) ℓ i = 𝟙 _ :=
  NatTrans.ext (funext fun r ↦ torsionEtaleCohomologyPullback_id X ℓ r.unop i)

theorem torsionEtaleCohomologySystemPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (ℓ i : ℕ) :
    torsionEtaleCohomologySystemPullback (f ≫ g) ℓ i =
      torsionEtaleCohomologySystemPullback g ℓ i ≫ torsionEtaleCohomologySystemPullback f ℓ i :=
  NatTrans.ext (funext fun r ↦ torsionEtaleCohomologyPullback_comp f g ℓ r.unop i)

/-- The pullback `H^i_classical(Y, ℤ_ℓ) ⟶ H^i_classical(X, ℤ_ℓ)` induced on inverse limits by the
torsion pullback maps. -/
noncomputable def classicalEllAdicCohomologyPullback (f : X ⟶ Y) (ℓ i : ℕ) :
    Y.classicalEllAdicCohomology ℓ i ⟶ X.classicalEllAdicCohomology ℓ i :=
  limMap (torsionEtaleCohomologySystemPullback f ℓ i)

theorem classicalEllAdicCohomologyPullback_id (X : Scheme.{u}) (ℓ i : ℕ) :
    classicalEllAdicCohomologyPullback (𝟙 X) ℓ i = 𝟙 _ := by
  rw [classicalEllAdicCohomologyPullback, torsionEtaleCohomologySystemPullback_id]
  exact lim.map_id _

theorem classicalEllAdicCohomologyPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (ℓ i : ℕ) :
    classicalEllAdicCohomologyPullback (f ≫ g) ℓ i =
      classicalEllAdicCohomologyPullback g ℓ i ≫ classicalEllAdicCohomologyPullback f ℓ i := by
  rw [classicalEllAdicCohomologyPullback, torsionEtaleCohomologySystemPullback_comp]
  exact lim.map_comp _ _

section Rational

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The classical pullback commutes with the action of `ℤ_[ℓ]`. -/
theorem classicalEllAdicCohomologyPullback_smul (f : X ⟶ Y) (i : ℕ) (a : ℤ_[ℓ])
    (x : Y.classicalEllAdicCohomology ℓ i) :
    (classicalEllAdicCohomologyPullback f ℓ i).hom (a • x) =
      a • (classicalEllAdicCohomologyPullback f ℓ i).hom x := by
  have hsys : Y.torsionEtaleCohomologySystemPadicIntAction ℓ i a ≫
      torsionEtaleCohomologySystemPullback f ℓ i =
        torsionEtaleCohomologySystemPullback f ℓ i ≫
          X.torsionEtaleCohomologySystemPadicIntAction ℓ i a := by
    refine NatTrans.ext (funext fun r ↦ ?_)
    change Y.torsionEtaleCohomologyPadicIntAction ℓ r.unop i a ≫
        torsionEtaleCohomologyPullback f ℓ r.unop i =
      torsionEtaleCohomologyPullback f ℓ r.unop i ≫
        X.torsionEtaleCohomologyPadicIntAction ℓ r.unop i a
    rw [torsionEtaleCohomologyPadicIntAction_apply, torsionEtaleCohomologyPadicIntAction_apply,
      Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  have h : Y.classicalEllAdicCohomologyPadicIntAction ℓ i a ≫
      classicalEllAdicCohomologyPullback f ℓ i =
        classicalEllAdicCohomologyPullback f ℓ i ≫
          X.classicalEllAdicCohomologyPadicIntAction ℓ i a := by
    change limMap _ ≫ limMap _ = limMap _ ≫ limMap _
    simp only [limMap_eq]
    rw [← lim.map_comp, ← lim.map_comp, hsys]
  exact congrArg (fun φ ↦ φ.hom x) h

/-- The classical pullback as a `ℤ_[ℓ]`-linear map. -/
noncomputable def classicalEllAdicCohomologyPullbackLinearMap (f : X ⟶ Y) (i : ℕ) :
    Y.classicalEllAdicCohomology ℓ i →ₗ[ℤ_[ℓ]] X.classicalEllAdicCohomology ℓ i where
  toFun := (classicalEllAdicCohomologyPullback f ℓ i).hom
  map_add' := map_add _
  map_smul' := classicalEllAdicCohomologyPullback_smul ℓ f i

/-- The pullback `f^* : H^i_et(Y, ℚ_ℓ) ⟶ H^i_et(X, ℚ_ℓ)`: the scalar extension to `ℚ_[ℓ]` of the
`ℤ_[ℓ]`-linear classical pullback. -/
noncomputable def rationalEllAdicCohomologyPullback (f : X ⟶ Y) (i : ℕ) :
    Y.rationalEllAdicCohomology ℓ i ⟶ X.rationalEllAdicCohomology ℓ i :=
  ModuleCat.ofHom ((classicalEllAdicCohomologyPullbackLinearMap ℓ f i).baseChange ℚ_[ℓ])

/-- Identity law: `(𝟙_X)^* = 𝟙` on `H^i_et(X, ℚ_ℓ)`. -/
theorem rationalEllAdicCohomologyPullback_id (X : Scheme.{u}) (i : ℕ) :
    rationalEllAdicCohomologyPullback ℓ (𝟙 X) i = 𝟙 _ := by
  have h : classicalEllAdicCohomologyPullbackLinearMap ℓ (𝟙 X) i = LinearMap.id :=
    LinearMap.ext fun x ↦ congrArg (fun φ ↦ φ.hom x) (classicalEllAdicCohomologyPullback_id X ℓ i)
  ext : 1
  rw [rationalEllAdicCohomologyPullback, ModuleCat.hom_ofHom, h, LinearMap.baseChange_id]
  rfl

/-- Composition law: `(g ∘ f)^* = f^* ∘ g^*`. -/
theorem rationalEllAdicCohomologyPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℕ) :
    rationalEllAdicCohomologyPullback ℓ (f ≫ g) i =
      rationalEllAdicCohomologyPullback ℓ g i ≫ rationalEllAdicCohomologyPullback ℓ f i := by
  have h : classicalEllAdicCohomologyPullbackLinearMap ℓ (f ≫ g) i =
      classicalEllAdicCohomologyPullbackLinearMap ℓ f i ∘ₗ
        classicalEllAdicCohomologyPullbackLinearMap ℓ g i :=
    LinearMap.ext fun x ↦
      congrArg (fun φ ↦ φ.hom x) (classicalEllAdicCohomologyPullback_comp f g ℓ i)
  ext : 1
  rw [rationalEllAdicCohomologyPullback, ModuleCat.hom_ofHom, h, LinearMap.baseChange_comp]
  rfl

/-- Rational `ℓ`-adic cohomology `X ↦ H^i_et(X, ℚ_ℓ)` as a contravariant functor from schemes to
`ℚ_[ℓ]`-vector spaces, acting on morphisms by pullback. -/
noncomputable def rationalEllAdicCohomologyFunctor (i : ℕ) :
    Scheme.{u}ᵒᵖ ⥤ ModuleCat.{u} ℚ_[ℓ] where
  obj X := X.unop.rationalEllAdicCohomology ℓ i
  map f := rationalEllAdicCohomologyPullback ℓ f.unop i
  map_id X := rationalEllAdicCohomologyPullback_id ℓ X.unop i
  map_comp f g := rationalEllAdicCohomologyPullback_comp ℓ g.unop f.unop i

end Rational

end AlgebraicGeometry.Scheme
