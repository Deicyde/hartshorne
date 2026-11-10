/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.ImmersionConormalSheaf
import Hartshorne.Scheme.QuasicoherentAbelianClosure

/-!
# Independence of the conormal sheaf of an immersion

Hartshorne, *Algebraic Geometry*, II.8 (pp. 175–176); Stacks Project, tags 01R1–01R3.

Let `i : Z ⟶ X` be an immersion. A closed factorization of `i` is an open subscheme `U ⊆ X`
with a closed immersion `j : Z ⟶ U` such that `j ≫ U.ι = i`. Each gives a conormal sheaf
`j^* I_j` on `Z`.

For an open immersion `κ : V ⟶ U` and any `j : Z ⟶ V`, restricting to `V` preserves kernels and
carries `𝒪_U ⟶ (j ≫ κ)_* 𝒪_Z` to `𝒪_V ⟶ j_* 𝒪_Z`. Hence `I_{j ≫ κ}|_V ≅ I_j` and
`j^* I_j ≅ (j ≫ κ)^* I_{j ≫ κ}` (`conormalRestrictIso`).

Every factoring open lies in `i.coborderRange` (`ClosedFactorization.le_coborderRange`). So each
construction is identified with the canonical conormal sheaf `N^*_i = immersionConormalSheaf i`
(`ClosedFactorization.toCanonical`). The comparison isomorphisms between two factorizations are
defined through `N^*_i`. They are the identity for one factorization
(`ClosedFactorization.comparison_self`) and satisfy the cocycle law for three
(`ClosedFactorization.comparison_trans`).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne.ConormalIndependence

open Scheme

section Restrict

variable {Z U V : Scheme.{u}} (j : Z ⟶ V) (κ : V ⟶ U) [IsOpenImmersion κ]

/-- `(j ≫ κ)_* 𝒪_Z` restricted to `V` is `j_* 𝒪_Z`. -/
noncomputable def pushforwardRestrictIso :
    (Modules.restrictFunctor κ).obj
        ((Modules.pushforward (j ≫ κ)).obj (SheafOfModules.unit Z.ringCatSheaf)) ≅
      (Modules.pushforward j).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  (Modules.restrictFunctor κ).mapIso ((Modules.pushforwardComp j κ).app _).symm ≪≫
    (Modules.restrictFunctorAdjCounitIso κ).app _

/-- Restricting `𝒪_U ⟶ (j ≫ κ)_* 𝒪_Z` to `V` gives `𝒪_V ⟶ j_* 𝒪_Z`. -/
theorem structureSheafToPushforward_restrict :
    (Modules.restrictFunctor κ).map (structureSheafToPushforward (j ≫ κ)) ≫
        (pushforwardRestrictIso j κ).hom =
      (Modules.restrictUnitIso κ).hom ≫ structureSheafToPushforward j := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  change Z.presheaf.map ((Opens.map j.base).map (eqToHom (κ.preimage_image_eq W).symm)).op
      ((j ≫ κ).app (κ ''ᵁ W) x) = j.app W ((κ.appIso W).hom x)
  have h := congr(ConcreteCategory.hom
    $(j.naturality (eqToHom (κ.preimage_image_eq W).symm).op) (κ.app (κ ''ᵁ W) x))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [Scheme.Hom.appIso_hom]
  exact h.symm

/-- The ideal sheaf of `j ≫ κ`, restricted to the open subscheme `V`, is the ideal sheaf of `j`. -/
noncomputable def idealSheafRestrictIso :
    (closedImmersionIdealSheaf (j ≫ κ)).restrict κ ≅ closedImmersionIdealSheaf j :=
  PreservesKernel.iso (Modules.restrictFunctor κ) (structureSheafToPushforward (j ≫ κ)) ≪≫
    kernel.mapIso _ _ (Modules.restrictUnitIso κ) (pushforwardRestrictIso j κ)
      (structureSheafToPushforward_restrict j κ)

/-- `j^* I_j ≅ (j ≫ κ)^* I_{j ≫ κ}` for an open immersion `κ`. -/
noncomputable def conormalRestrictIso :
    (Modules.pullback j).obj (closedImmersionIdealSheaf j) ≅
      (Modules.pullback (j ≫ κ)).obj (closedImmersionIdealSheaf (j ≫ κ)) :=
  (Modules.pullback j).mapIso ((idealSheafRestrictIso j κ).symm ≪≫
    (Modules.restrictFunctorIsoPullback κ).app _) ≪≫ (Modules.pullbackComp j κ).app _

end Restrict

section Coherence

variable {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W) [IsOpenImmersion f] [IsOpenImmersion g]

/-- `restrictUnitIso` is compatible with `restrictFunctorComp`. -/
theorem restrictUnitIso_comp :
    (Modules.restrictFunctorComp f g).hom.app _ ≫
        (Modules.restrictFunctor f).map (Modules.restrictUnitIso g).hom ≫
          (Modules.restrictUnitIso f).hom =
      (Modules.restrictUnitIso (f ≫ g)).hom := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  exact (congr(ConcreteCategory.hom ($(Scheme.Hom.comp_appIso f g U)).hom x)).symm

/-- The conjugate of `restrictFunctorIsoPullback` is the identity of the pushforward. -/
theorem conjugateEquiv_restrictFunctorIsoPullback_hom :
    conjugateEquiv (Modules.pullbackPushforwardAdjunction f) (Modules.restrictAdjunction f)
      (Modules.restrictFunctorIsoPullback f).hom = 𝟙 _ := by
  simp only [Modules.restrictFunctorIsoPullback, Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, Equiv.apply_symm_apply]

omit [IsOpenImmersion f] [IsOpenImmersion g] in
/-- The conjugate of `pullbackComp` is the inverse of `pushforwardComp`. -/
theorem conjugateEquiv_pullbackComp_hom :
    conjugateEquiv (Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Modules.pullbackPushforwardAdjunction g).comp (Modules.pullbackPushforwardAdjunction f))
      (Modules.pullbackComp f g).hom = (Modules.pushforwardComp f g).inv := by
  rw [← Iso.comp_hom_eq_id, ← Modules.conjugateEquiv_pullbackComp_inv, conjugateEquiv_comp,
    Iso.inv_hom_id, conjugateEquiv_id]

/-- The conjugate of `restrictFunctorComp` is `pushforwardComp`. -/
theorem conjugateEquiv_restrictFunctorComp_hom :
    conjugateEquiv ((Modules.restrictAdjunction g).comp (Modules.restrictAdjunction f))
      (Modules.restrictAdjunction (f ≫ g)) (Modules.restrictFunctorComp f g).hom =
      (Modules.pushforwardComp f g).hom := by
  ext M : 2
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  have hr : ∀ {A B : Y.Modules} (φ : A ⟶ B) (W' : X.Opens),
      Modules.Hom.app ((Modules.restrictFunctor f).map φ) W' = Modules.Hom.app φ (f ''ᵁ W') :=
    fun _ _ => rfl
  simp [conjugateEquiv_apply_app, Adjunction.comp_counit_app, hr]
  erw [← M.presheaf.map_comp, ← M.presheaf.map_comp, ← M.presheaf.map_comp, ← M.presheaf.map_id]
  rfl

/-- `restrictFunctorIsoPullback` is compatible with composition of open immersions. -/
theorem restrictFunctorIsoPullback_comp :
    (Modules.restrictFunctorComp f g).hom ≫
        Functor.whiskerRight (Modules.restrictFunctorIsoPullback g).hom
          (Modules.restrictFunctor f) ≫
          Functor.whiskerLeft (Modules.pullback g) (Modules.restrictFunctorIsoPullback f).hom ≫
            (Modules.pullbackComp f g).hom =
      (Modules.restrictFunctorIsoPullback (f ≫ g)).hom := by
  apply (conjugateEquiv (Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Modules.restrictAdjunction (f ≫ g))).injective
  rw [conjugateEquiv_restrictFunctorIsoPullback_hom (f ≫ g),
    ← conjugateEquiv_comp _ ((Modules.restrictAdjunction g).comp (Modules.restrictAdjunction f)),
    ← conjugateEquiv_comp _
      ((Modules.pullbackPushforwardAdjunction g).comp (Modules.restrictAdjunction f)),
    ← conjugateEquiv_comp _
      ((Modules.pullbackPushforwardAdjunction g).comp (Modules.pullbackPushforwardAdjunction f)),
    conjugateEquiv_pullbackComp_hom, conjugateEquiv_whiskerLeft,
    conjugateEquiv_restrictFunctorIsoPullback_hom f, conjugateEquiv_whiskerRight,
    conjugateEquiv_restrictFunctorIsoPullback_hom g, conjugateEquiv_restrictFunctorComp_hom]
  simp

end Coherence

section Cocycle

variable {Z V U : Scheme.{u}}

/-- `idealSheafRestrictIso` is compatible with the inclusions into the structure sheaves. -/
theorem idealSheafRestrictIso_hom_ι (j : Z ⟶ V) (κ : V ⟶ U) [IsOpenImmersion κ] :
    (idealSheafRestrictIso j κ).hom ≫ closedImmersionIdealSheafι j =
      (Modules.restrictFunctor κ).map (closedImmersionIdealSheafι (j ≫ κ)) ≫
        (Modules.restrictUnitIso κ).hom := by
  have h1 : (kernel.mapIso _ _ (Modules.restrictUnitIso κ) (pushforwardRestrictIso j κ)
      (structureSheafToPushforward_restrict j κ)).hom ≫ kernel.ι (structureSheafToPushforward j) =
      kernel.ι _ ≫ (Modules.restrictUnitIso κ).hom :=
    kernel.lift_ι _ _ _
  have h2 : (PreservesKernel.iso (Modules.restrictFunctor κ)
      (structureSheafToPushforward (j ≫ κ))).hom ≫ kernel.ι _ =
      (Modules.restrictFunctor κ).map (kernel.ι (structureSheafToPushforward (j ≫ κ))) :=
    (congrArg (_ ≫ ·) (PreservesKernel.iso_inv_ι _ _).symm).trans (Iso.hom_inv_id_assoc _ _)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h2)))

/-- `idealSheafRestrictIso` for a morphism `j'` equal to `j ≫ κ`. -/
noncomputable def idealSheafRestrictIso' (j : Z ⟶ V) (κ : V ⟶ U) [IsOpenImmersion κ]
    (j' : Z ⟶ U) (h : j ≫ κ = j') :
    (closedImmersionIdealSheaf j').restrict κ ≅ closedImmersionIdealSheaf j :=
  (Modules.restrictFunctor κ).mapIso (eqToIso (congrArg closedImmersionIdealSheaf h.symm)) ≪≫
    idealSheafRestrictIso j κ

/-- `idealSheafRestrictIso'` is compatible with the inclusions into the structure sheaves. -/
theorem idealSheafRestrictIso'_hom_ι (j : Z ⟶ V) (κ : V ⟶ U) [IsOpenImmersion κ]
    (j' : Z ⟶ U) (h : j ≫ κ = j') :
    (idealSheafRestrictIso' j κ j' h).hom ≫ closedImmersionIdealSheafι j =
      (Modules.restrictFunctor κ).map (closedImmersionIdealSheafι j') ≫
        (Modules.restrictUnitIso κ).hom := by
  subst h
  simp [idealSheafRestrictIso', idealSheafRestrictIso_hom_ι]

end Cocycle

section Transitivity

variable {Z V₁ V₂ U : Scheme.{u}} (j : Z ⟶ V₁) (κ₁ : V₁ ⟶ V₂) (κ₂ : V₂ ⟶ U)
  [IsOpenImmersion κ₁] [IsOpenImmersion κ₂]

/-- `idealSheafRestrictIso` is transitive along composed open immersions. -/
theorem idealSheafRestrictIso_trans :
    (Modules.restrictFunctorComp κ₁ κ₂).app (closedImmersionIdealSheaf ((j ≫ κ₁) ≫ κ₂)) ≪≫
        (Modules.restrictFunctor κ₁).mapIso (idealSheafRestrictIso (j ≫ κ₁) κ₂) ≪≫
          idealSheafRestrictIso j κ₁ =
      idealSheafRestrictIso' j (κ₁ ≫ κ₂) ((j ≫ κ₁) ≫ κ₂) (Category.assoc _ _ _).symm := by
  ext1
  rw [← cancel_mono (closedImmersionIdealSheafι j), idealSheafRestrictIso'_hom_ι]
  have h1 := idealSheafRestrictIso_hom_ι j κ₁
  have h2 := idealSheafRestrictIso_hom_ι (j ≫ κ₁) κ₂
  have hC := restrictUnitIso_comp κ₁ κ₂
  have hN := (Modules.restrictFunctorComp κ₁ κ₂).hom.naturality_assoc
    (closedImmersionIdealSheafι ((j ≫ κ₁) ≫ κ₂))
    ((Modules.restrictFunctor κ₁).map (Modules.restrictUnitIso κ₂).hom ≫
      (Modules.restrictUnitIso κ₁).hom)
  have s1 := congrArg (fun t =>
    (Modules.restrictFunctorComp κ₁ κ₂).hom.app (closedImmersionIdealSheaf ((j ≫ κ₁) ≫ κ₂)) ≫
      (Modules.restrictFunctor κ₁).map (idealSheafRestrictIso (j ≫ κ₁) κ₂).hom ≫ t) h1
  have s2 := (Functor.map_comp_assoc (Modules.restrictFunctor κ₁)
    (idealSheafRestrictIso (j ≫ κ₁) κ₂).hom (closedImmersionIdealSheafι (j ≫ κ₁))
    (Modules.restrictUnitIso κ₁).hom).symm
  have s3 := congrArg (fun t => (Modules.restrictFunctor κ₁).map t ≫
    (Modules.restrictUnitIso κ₁).hom) h2
  have s4 := Functor.map_comp_assoc (Modules.restrictFunctor κ₁)
    ((Modules.restrictFunctor κ₂).map (closedImmersionIdealSheafι ((j ≫ κ₁) ≫ κ₂)))
    (Modules.restrictUnitIso κ₂).hom (Modules.restrictUnitIso κ₁).hom
  have s5 := congrArg (fun t =>
    (Modules.restrictFunctorComp κ₁ κ₂).hom.app (closedImmersionIdealSheaf ((j ≫ κ₁) ≫ κ₂)) ≫ t)
    (s2.trans (s3.trans s4))
  have s6 := congrArg (fun t =>
    (Modules.restrictFunctor (κ₁ ≫ κ₂)).map (closedImmersionIdealSheafι ((j ≫ κ₁) ≫ κ₂)) ≫ t) hC
  exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    (s1.trans (s5.trans (hN.symm.trans s6))))

end Transitivity

section Factorization

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- A factorization of an immersion `i : Z ⟶ X` as a closed immersion `j : Z ⟶ U` into an open
subscheme `U ⊆ X` followed by the inclusion of `U`. -/
structure ClosedFactorization where
  /-- the open subscheme -/
  U : X.Opens
  /-- the closed immersion into `U` -/
  j : Z ⟶ U.toScheme
  fac : j ≫ U.ι = i
  isClosedImmersion : IsClosedImmersion j

namespace ClosedFactorization

variable {i}

/-- The pullback `j^* I` of the ideal sheaf `I` of the closed immersion `j : Z ⟶ U`. -/
noncomputable def conormal (F : ClosedFactorization i) : Z.Modules :=
  (Modules.pullback F.j).obj (closedImmersionIdealSheaf F.j)

variable (i) in
/-- The canonical factorization through `i.coborderRange`. -/
noncomputable def canonical : ClosedFactorization i :=
  ⟨i.coborderRange, i.liftCoborder, i.liftCoborder_ι, inferInstance⟩

variable (i) in
/-- The canonical factorization gives the canonical conormal sheaf `N^*_i`. -/
theorem conormal_canonical : (canonical i).conormal = immersionConormalSheaf i :=
  rfl

/-- Every open in which `Z` is closed lies in `i.coborderRange`. -/
theorem le_coborderRange (F : ClosedFactorization i) : F.U ≤ i.coborderRange := by
  intro x hx
  show x ∈ coborder (Set.range i)
  rw [coborder_eq_union_closure_compl]
  by_cases hxs : x ∈ Set.range i
  · exact Or.inl hxs
  refine Or.inr fun hcl => hxs ?_
  have hjc : IsClosed (Set.range F.j) :=
    (@Scheme.Hom.isClosedEmbedding _ _ F.j F.isClosedImmersion).isClosed_range
  have hfun : ∀ z, i z = F.U.ι (F.j z) := fun z =>
    (congrArg (fun g : Z ⟶ X => g z) F.fac).symm
  have hs : Set.range i = F.U.ι '' Set.range F.j := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hfun)
  have hcl' := F.U.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image
    (Set.range F.j)
  have hmem : (⟨x, hx⟩ : F.U) ∈ closure (Set.range F.j) := by
    rw [hcl', ← hs]
    exact hcl
  rw [hjc.closure_eq] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, (hfun z).trans ?_⟩
  rw [hz]
  rfl

/-- `F.j` followed by the inclusion `F.U ⟶ i.coborderRange` is `i.liftCoborder`. -/
theorem j_homOfLE (F : ClosedFactorization i) :
    F.j ≫ X.homOfLE (le_coborderRange F) = i.liftCoborder := by
  rw [← cancel_mono i.coborderRange.ι, Category.assoc, Scheme.homOfLE_ι, F.fac,
    i.liftCoborder_ι]

/-- **Independence of the conormal sheaf.** The construction from any closed factorization is
canonically isomorphic to the conormal sheaf `N^*_i`. -/
noncomputable def toCanonical (F : ClosedFactorization i) :
    F.conormal ≅ immersionConormalSheaf i :=
  conormalRestrictIso F.j (X.homOfLE (le_coborderRange F)) ≪≫
    eqToIso (congrArg (fun g => (Modules.pullback g).obj (closedImmersionIdealSheaf g))
      (j_homOfLE F))

/-- The comparison isomorphism between the constructions from two closed factorizations. -/
noncomputable def comparison (F G : ClosedFactorization i) : F.conormal ≅ G.conormal :=
  toCanonical F ≪≫ (toCanonical G).symm

/-- The comparison isomorphism of a factorization with itself is the identity. -/
theorem comparison_self (F : ClosedFactorization i) : comparison F F = Iso.refl _ :=
  Iso.self_symm_id _

/-- **Cocycle law** for the comparison isomorphisms of three closed factorizations. -/
theorem comparison_trans (F G H : ClosedFactorization i) :
    comparison F G ≪≫ comparison G H = comparison F H := by
  simp [comparison]

/-- The comparison isomorphisms are compatible with the identifications with `N^*_i`. -/
theorem comparison_toCanonical (F G : ClosedFactorization i) :
    comparison F G ≪≫ toCanonical G = toCanonical F := by
  simp [comparison]

end ClosedFactorization

end Factorization

end Hartshorne.ConormalIndependence
