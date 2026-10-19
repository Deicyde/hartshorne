/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.OpenExtensionByZero
import Mathlib.Topology.Sheaves.Functors

/-!
# Canonical adjunction for ordinary open extension by zero

The construction uses the conditional presheaf of Hartshorne II.1, Exercise 1.19(b),
and the canonical maps to its sheafification.
-/

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne

universe u

/-- On a contained open, the conditional subgroup is the full group of sections. -/
private def openZeroInsideIso {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (V : Opens X) (hV : V ≤ U) :
    (openExtensionByZeroPresheaf U F).obj (op V) ≅
      F.presheaf.obj (op ((Opens.map U.inclusion').obj V)) :=
  AddEquiv.toAddCommGrpIso
    { toFun := fun s => s.val
      invFun := fun s => ⟨s, Or.inl hV⟩
      left_inv := fun s => Subtype.ext (Eq.refl s.val)
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

/-- Outside the open, every section of the original conditional presheaf is zero. -/
private theorem openZeroOutside_eq_zero {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (V : Opens X) (hV : ¬ V ≤ U)
    (s : (openExtensionByZeroPresheaf U F).obj (op V)) : s = 0 :=
  Subtype.ext (s.property.resolve_left hV)

/-- A sheaf morphism acts on the original conditional groups of sections. -/
private def openZeroFunctorMapApp {X : TopCat.{u}} (U : Opens X)
    {F G : (TopCat.of U).Sheaf AddCommGrpCat.{u}} (φ : F ⟶ G) (V : (Opens X)ᵒᵖ) :
    (openExtensionByZeroPresheaf U F).obj V ⟶
      (openExtensionByZeroPresheaf U G).obj V :=
  let h := (φ.hom.app ((Opens.map U.inclusion').op.obj V)).hom
  AddCommGrpCat.ofHom
    { toFun := fun s => ⟨h s.val, by
        rcases s.property with hV | hs
        · exact Or.inl hV
        · right
          change h s.val = 0
          rw [hs, map_zero]⟩
      map_zero' := Subtype.ext (map_zero h)
      map_add' := fun s t => Subtype.ext (map_add h s.val t.val) }

/-- These section maps commute with the inherited restrictions. -/
private def openZeroFunctorMap {X : TopCat.{u}} (U : Opens X)
    {F G : (TopCat.of U).Sheaf AddCommGrpCat.{u}} (φ : F ⟶ G) :
    openExtensionByZeroPresheaf U F ⟶ openExtensionByZeroPresheaf U G where
  app V := openZeroFunctorMapApp U φ V
  naturality {V W} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply Subtype.ext
    change (φ.hom.app ((Opens.map U.inclusion').op.obj W)).hom
        ((F.presheaf.map ((Opens.map U.inclusion').op.map f)).hom s.val) =
      (G.presheaf.map ((Opens.map U.inclusion').op.map f)).hom
        ((φ.hom.app ((Opens.map U.inclusion').op.obj V)).hom s.val)
    exact ConcreteCategory.congr_hom
      (φ.hom.naturality ((Opens.map U.inclusion').op.map f)) s.val

/-- The existing conditional presheaves, with their canonical maps, form a functor. -/
private def openZeroFunctor {X : TopCat.{u}} (U : Opens X) :
    (TopCat.of U).Sheaf AddCommGrpCat.{u} ⥤ X.Presheaf AddCommGrpCat.{u} where
  obj F := openExtensionByZeroPresheaf U F
  map φ := openZeroFunctorMap U φ
  map_id F := by
    ext V s
    apply Subtype.ext
    change (s.val : F.presheaf.obj ((Opens.map U.inclusion').op.obj (op V))) = s.val
    rfl
  map_comp φ ψ := by
    ext V s
    apply Subtype.ext
    change (ψ.hom.app ((Opens.map U.inclusion').op.obj (op V))).hom
      ((φ.hom.app ((Opens.map U.inclusion').op.obj (op V))).hom s.val) = _
    rfl

/-- The image of an open of the open subspace is contained in that subspace. -/
private theorem openZero_image_le {X : TopCat.{u}} (U : Opens X)
    (W : Opens (TopCat.of U)) : U.isOpenEmbedding.functor.obj W ≤ U := by
  rintro x ⟨w, _, rfl⟩
  exact w.property

/-- The canonical seed transports along preimage of image and enters the full subgroup. -/
private def openZeroSeedApp {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (W : (Opens (TopCat.of U))ᵒᵖ) :
    F.presheaf.obj W ≅
      (openExtensionByZeroPresheaf U F).obj (U.isOpenEmbedding.functor.op.obj W) :=
  F.presheaf.mapIso
      ((eqToIso (Opens.map_functor_eq (U := U) W.unop)).op) ≪≫
    (openZeroInsideIso U F (U.isOpenEmbedding.functor.obj W.unop)
      (openZero_image_le U W.unop)).symm

/-- On contained opens, forgetting the conditional subgroup commutes with restriction. -/
private theorem openZeroInsideIso_map {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) {V W : (Opens X)ᵒᵖ} (f : V ⟶ W)
    (hV : V.unop ≤ U) (hW : W.unop ≤ U) :
    (openExtensionByZeroPresheaf U F).map f ≫ (openZeroInsideIso U F W.unop hW).hom =
      (openZeroInsideIso U F V.unop hV).hom ≫
        F.presheaf.map ((Opens.map U.inclusion').op.map f) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The independently defined seed is natural on opens of the open subspace. -/
private theorem openZeroSeedApp_naturality {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u})
    {V W : (Opens (TopCat.of U))ᵒᵖ} (f : V ⟶ W) :
    F.presheaf.map f ≫ (openZeroSeedApp U F W).hom =
      (openZeroSeedApp U F V).hom ≫
        (U.isOpenEmbedding.functor.op ⋙ openExtensionByZeroPresheaf U F).map f := by
  apply (cancel_mono
    (openZeroInsideIso U F (U.isOpenEmbedding.functor.obj W.unop)
      (openZero_image_le U W.unop)).hom).1
  simp only [openZeroSeedApp, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    Iso.symm_hom, Functor.comp_map, Category.assoc]
  erw [openZeroInsideIso_map U F (U.isOpenEmbedding.functor.op.map f)
    (openZero_image_le U V.unop) (openZero_image_le U W.unop)]
  simp only [Functor.op_obj, unop_op, Iso.inv_hom_id, Iso.inv_hom_id_assoc,
    Category.comp_id, ← Functor.map_comp]
  congr 1

/-- The canonical seed is an isomorphism after restriction to image opens. -/
private def openZeroSeedIso {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) :
    F.presheaf ≅ U.isOpenEmbedding.functor.op ⋙ openExtensionByZeroPresheaf U F :=
  NatIso.ofComponents (openZeroSeedApp U F) (fun f => openZeroSeedApp_naturality U F f)

/-- A contained open is canonically the image of its inverse image in the open subspace. -/
private def openZeroImagePreimageIso {X : TopCat.{u}} (U V : Opens X) (hV : V ≤ U) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) ≅ V :=
  eqToIso ((Opens.functor_map_eq_inf U V).trans (inf_eq_left.mpr hV))

/-- Canonical descent to any target presheaf, using the zero branch outside the open. -/
private noncomputable def openZeroDescApp {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (T : X.Presheaf AddCommGrpCat.{u})
    (β : F.presheaf ⟶ U.isOpenEmbedding.functor.op ⋙ T) (V : (Opens X)ᵒᵖ) :
    (openExtensionByZeroPresheaf U F).obj V ⟶ T.obj V := by
  classical
  exact if hV : V.unop ≤ U then
    (openZeroInsideIso U F V.unop hV).hom ≫
      β.app (op ((Opens.map U.inclusion').obj V.unop)) ≫
        T.map (openZeroImagePreimageIso U V.unop hV).inv.op
  else 0

set_option backward.isDefEq.respectTransparency false in
/-- Canonical descent commutes with restriction between contained opens. -/
private theorem openZeroDescApp_naturality_inside {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (T : X.Presheaf AddCommGrpCat.{u})
    (β : F.presheaf ⟶ U.isOpenEmbedding.functor.op ⋙ T) {V W : (Opens X)ᵒᵖ}
    (f : V ⟶ W) (hV : V.unop ≤ U) (hW : W.unop ≤ U) :
    (openExtensionByZeroPresheaf U F).map f ≫ openZeroDescApp U F T β W =
      openZeroDescApp U F T β V ≫ T.map f := by
  classical
  simp only [openZeroDescApp, dif_pos hV, dif_pos hW, Category.assoc]
  erw [← Category.assoc, openZeroInsideIso_map U F f hV hW, Category.assoc]
  erw [β.naturality_assoc ((Opens.map U.inclusion').op.map f)]
  simp only [Functor.comp_map, ← Functor.map_comp]
  congr 2

/-- Canonical descent is a morphism to every target presheaf, not only to sheaves. -/
private noncomputable def openZeroDesc {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (T : X.Presheaf AddCommGrpCat.{u})
    (β : F.presheaf ⟶ U.isOpenEmbedding.functor.op ⋙ T) :
    openExtensionByZeroPresheaf U F ⟶ T where
  app V := openZeroDescApp U F T β V
  naturality {V W} f := by
    classical
    by_cases hV : V.unop ≤ U
    · exact openZeroDescApp_naturality_inside U F T β f hV ((leOfHom f.unop).trans hV)
    · apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      have hs : s = 0 := openZeroOutside_eq_zero U F V.unop hV s
      rw [hs, map_zero, map_zero]

/-- The two canonical open-set transports around an image open compose to the identity. -/
private theorem openZeroSeedTransport_id {X : TopCat.{u}} (U : Opens X)
    (W : (Opens (TopCat.of U))ᵒᵖ) :
    U.isOpenEmbedding.functor.op.map
        ((eqToIso (Opens.map_functor_eq (U := U) W.unop)).hom.op) ≫
      (openZeroImagePreimageIso U (U.isOpenEmbedding.functor.obj W.unop)
        (openZero_image_le U W.unop)).inv.op = 𝟙 (U.isOpenEmbedding.functor.op.obj W) :=
  Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Canonical descent recovers the original map after composition with the seed. -/
private theorem openZeroDesc_fac {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (T : X.Presheaf AddCommGrpCat.{u})
    (β : F.presheaf ⟶ U.isOpenEmbedding.functor.op ⋙ T) :
    (openZeroSeedIso U F).hom ≫ Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (openZeroDesc U F T β) = β := by
  apply NatTrans.ext
  funext W
  change (openZeroSeedApp U F W).hom ≫
    openZeroDescApp U F T β (U.isOpenEmbedding.functor.op.obj W) = β.app W
  classical
  simp only [openZeroDescApp, Functor.op_obj, unop_op,
    dif_pos (openZero_image_le U W.unop), openZeroSeedApp, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  erw [← Category.assoc,
    β.naturality ((eqToIso (Opens.map_functor_eq (U := U) W.unop)).hom.op), Category.assoc]
  dsimp only [Functor.comp_map]
  erw [← Functor.map_comp]
  erw [openZeroSeedTransport_id U W]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- Agreement after the canonical seed implies agreement on image opens. -/
private theorem openZeroHomEq_onImage {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (T : X.Presheaf AddCommGrpCat.{u})
    {φ ψ : openExtensionByZeroPresheaf U F ⟶ T}
    (h : (openZeroSeedIso U F).hom ≫ Functor.whiskerLeft U.isOpenEmbedding.functor.op φ =
      (openZeroSeedIso U F).hom ≫ Functor.whiskerLeft U.isOpenEmbedding.functor.op ψ)
    (W : (Opens (TopCat.of U))ᵒᵖ) :
    φ.app (U.isOpenEmbedding.functor.op.obj W) =
      ψ.app (U.isOpenEmbedding.functor.op.obj W) :=
  (cancel_epi ((openZeroSeedIso U F).hom.app W)).1 (NatTrans.congr_app h W)

set_option backward.isDefEq.respectTransparency false in
/-- Image-open agreement transports to every contained ambient open. -/
private theorem openZeroHomEq_onContained {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (T : X.Presheaf AddCommGrpCat.{u})
    {φ ψ : openExtensionByZeroPresheaf U F ⟶ T}
    (h : (openZeroSeedIso U F).hom ≫ Functor.whiskerLeft U.isOpenEmbedding.functor.op φ =
      (openZeroSeedIso U F).hom ≫ Functor.whiskerLeft U.isOpenEmbedding.functor.op ψ)
    (V : (Opens X)ᵒᵖ) (hV : V.unop ≤ U) : φ.app V = ψ.app V := by
  let e := openZeroImagePreimageIso U V.unop hV
  apply (cancel_epi ((openExtensionByZeroPresheaf U F).map e.inv.op)).1
  erw [φ.naturality e.inv.op, ψ.naturality e.inv.op]
  exact congrArg (fun a => a ≫ T.map e.inv.op)
    (openZeroHomEq_onImage U F T h (op ((Opens.map U.inclusion').obj V.unop)))

/-- Maps from the original conditional presheaf are determined by the canonical seed. -/
private theorem openZeroHom_ext {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (T : X.Presheaf AddCommGrpCat.{u})
    {φ ψ : openExtensionByZeroPresheaf U F ⟶ T}
    (h : (openZeroSeedIso U F).hom ≫ Functor.whiskerLeft U.isOpenEmbedding.functor.op φ =
      (openZeroSeedIso U F).hom ≫ Functor.whiskerLeft U.isOpenEmbedding.functor.op ψ) :
    φ = ψ := by
  apply NatTrans.ext
  funext V
  classical
  by_cases hV : V.unop ≤ U
  · exact openZeroHomEq_onContained U F T h V hV
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    have hs : s = 0 := openZeroOutside_eq_zero U F V.unop hV s
    rw [hs, map_zero, map_zero]

/-- Explicit descent and direct uniqueness prove the native left-Kan universal property. -/
private theorem openZero_isLeftKanExtension {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) :
    (openExtensionByZeroPresheaf U F).IsLeftKanExtension (openZeroSeedIso U F).hom where
  nonempty_isUniversal := by
    refine ⟨CategoryTheory.Limits.IsInitial.ofUniqueHom
      (fun E => StructuredArrow.homMk (openZeroDesc U F E.right E.hom)
        (openZeroDesc_fac U F E.right E.hom)) ?_⟩
    intro E m
    apply StructuredArrow.hom_ext
    apply openZeroHom_ext U F E.right
    erw [openZeroDesc_fac]
    exact StructuredArrow.w m

set_option backward.isDefEq.respectTransparency false in
/-- The original conditional presheaf is canonically its left Kan extension. -/
private noncomputable def openZeroLanIso {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) :
    openExtensionByZeroPresheaf U F ≅ U.isOpenEmbedding.functor.op.lan.obj F.presheaf := by
  letI := openZero_isLeftKanExtension U F
  exact CategoryTheory.Functor.leftKanExtensionUnique (openExtensionByZeroPresheaf U F)
    (openZeroSeedIso U F).hom (U.isOpenEmbedding.functor.op.lan.obj F.presheaf)
    (U.isOpenEmbedding.functor.op.lanUnit.app F.presheaf)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical Kan comparison preserves the independently defined seed. -/
private theorem openZeroLanIso_hom_fac {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) :
    (openZeroSeedIso U F).hom ≫ Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (openZeroLanIso U F).hom = U.isOpenEmbedding.functor.op.lanUnit.app F.presheaf := by
  let := openZero_isLeftKanExtension U F
  simp [openZeroLanIso, CategoryTheory.Functor.leftKanExtensionUnique,
    CategoryTheory.Functor.leftKanExtensionUniqueOfIso]
  exact CategoryTheory.Functor.descOfIsLeftKanExtension_fac (openExtensionByZeroPresheaf U F)
    (openZeroSeedIso U F).hom (U.isOpenEmbedding.functor.op.lan.obj F.presheaf)
    (U.isOpenEmbedding.functor.op.lanUnit.app F.presheaf)

set_option backward.isDefEq.respectTransparency false in
/-- The independent canonical seed is also natural in the input sheaf. -/
private theorem openZeroSeedIso_naturality {X : TopCat.{u}} (U : Opens X)
    {F G : (TopCat.of U).Sheaf AddCommGrpCat.{u}} (φ : F ⟶ G) :
    φ.hom ≫ (openZeroSeedIso U G).hom = (openZeroSeedIso U F).hom ≫
      Functor.whiskerLeft U.isOpenEmbedding.functor.op (openZeroFunctorMap U φ) := by
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  let a := (eqToIso (Opens.map_functor_eq (U := U) W.unop)).hom.op
  change (G.presheaf.map a).hom ((φ.hom.app W).hom s) =
    (φ.hom.app (op ((Opens.map U.inclusion').obj
      (U.isOpenEmbedding.functor.obj W.unop)))).hom ((F.presheaf.map a).hom s)
  exact (ConcreteCategory.congr_hom (φ.hom.naturality a) s).symm

set_option backward.isDefEq.respectTransparency false in
/-- The seed-preserving Kan comparisons are natural in the input sheaf. -/
private theorem openZeroLanIso_naturality {X : TopCat.{u}} (U : Opens X)
    {F G : (TopCat.of U).Sheaf AddCommGrpCat.{u}} (φ : F ⟶ G) :
    openZeroFunctorMap U φ ≫ (openZeroLanIso U G).hom =
      (openZeroLanIso U F).hom ≫ U.isOpenEmbedding.functor.op.lan.map φ.hom := by
  apply openZeroHom_ext U F (U.isOpenEmbedding.functor.op.lan.obj G.presheaf)
  erw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
  erw [← Category.assoc, ← openZeroSeedIso_naturality U φ, Category.assoc]
  erw [openZeroLanIso_hom_fac U G]
  erw [← Category.assoc, openZeroLanIso_hom_fac U F]
  exact U.isOpenEmbedding.functor.op.lanUnit.naturality φ.hom

/-- The canonical conditional-presheaf/Kan comparison is a natural isomorphism. -/
private noncomputable def openZeroPresheafLanIso {X : TopCat.{u}} (U : Opens X) :
    openZeroFunctor U ≅
      sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u} ⋙
        U.isOpenEmbedding.functor.op.lan :=
  NatIso.ofComponents (openZeroLanIso U) (fun φ => openZeroLanIso_naturality U φ)

/-- Ordinary open extension by zero is functorial, using the original conditional
presheaf and its sheafification on every object. -/
noncomputable def openExtensionByZeroFunctor {X : TopCat.{u}} (U : Opens X) :
    (TopCat.of U).Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} :=
  openZeroFunctor U ⋙ presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- The functor has exactly the original Hartshorne extension-by-zero objects. -/
theorem openExtensionByZeroFunctor_obj {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) :
    (openExtensionByZeroFunctor U).obj F = openExtensionByZero U F := rfl

/-- The genuine conditional construction is naturally isomorphic to the sheafified
left Kan extension, via the independently defined, seed-preserving comparison. -/
noncomputable def openExtensionByZeroLanIso {X : TopCat.{u}} (U : Opens X) :
    openExtensionByZeroFunctor U ≅
      sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u} ⋙
        U.isOpenEmbedding.functor.op.lan ⋙
          presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight (openZeroPresheafLanIso U)
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Canonical restriction is computed from the original conditional presheaf's seed
and sheafification unit, then transported from image-open restriction to native pullback.
It is defined independently of any adjunction. -/
noncomputable def openExtensionByZeroCanonicalRestriction {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (G : X.Sheaf AddCommGrpCat.{u})
    (φ : openExtensionByZero U F ⟶ G) :
    F ⟶ (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj G :=
  (show F ⟶ (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj G from
    { hom := (openZeroSeedIso U F).hom ≫
        Functor.whiskerLeft U.isOpenEmbedding.functor.op
          (toSheafify (Opens.grothendieckTopology X) (openExtensionByZeroPresheaf U F) ≫
            φ.hom) }) ≫
    ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app G).inv

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary open extension by zero is left adjoint to the native sheaf pullback,
transporting the sheafified Kan adjunction through the canonical comparisons. -/
noncomputable def openExtensionByZeroAdjunction {X : TopCat.{u}} (U : Opens X) :
    openExtensionByZeroFunctor U ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion' := by
  letI : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X) :=
    Topology.IsOpenEmbedding.functor_isContinuous (f := U.inclusion') U.isOpenEmbedding
  exact ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U.isOpenEmbedding.functor AddCommGrpCat.{u}
    (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X)).ofNatIsoLeft
      (openExtensionByZeroLanIso U).symm).ofNatIsoRight
        (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).symm

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction's natural Hom equivalence is the independently computed canonical
restriction map from the original conditional presheaf and sheafification unit. -/
theorem openExtensionByZeroAdjunction_homEquiv {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (G : X.Sheaf AddCommGrpCat.{u})
    (φ : openExtensionByZero U F ⟶ G) :
    (openExtensionByZeroAdjunction U).homEquiv F G φ =
      openExtensionByZeroCanonicalRestriction U F G φ := by
  let : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X) :=
    Topology.IsOpenEmbedding.functor_isContinuous (f := U.inclusion') U.isOpenEmbedding
  simp only [openExtensionByZeroAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply, openExtensionByZeroCanonicalRestriction,
    Iso.symm_hom]
  congr 1
  apply Sheaf.hom_ext
  simp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.restrictFullyFaithful_homEquiv_apply]
  dsimp only [ObjectProperty.homMk]
  simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, Iso.refl_hom, NatTrans.id_app,
    Functor.id_map]
  change U.isOpenEmbedding.functor.op.lanUnit.app F.presheaf ≫
      Functor.whiskerLeft U.isOpenEmbedding.functor.op
        (toSheafify (Opens.grothendieckTopology X)
          (U.isOpenEmbedding.functor.op.lan.obj F.presheaf)) ≫
      Functor.whiskerLeft U.isOpenEmbedding.functor.op
        (sheafifyMap (Opens.grothendieckTopology X) (openZeroLanIso U F).inv ≫ φ.hom) = _
  erw [← Functor.whiskerLeft_comp]
  erw [← toSheafify_naturality_assoc (Opens.grothendieckTopology X) (openZeroLanIso U F).inv]
  erw [← openZeroLanIso_hom_fac U F]
  simp only [Category.assoc, ← Functor.whiskerLeft_comp, Iso.hom_inv_id_assoc]

/-- The original extension-by-zero construction admits a genuine adjunction to native
pullback, with its natural Hom equivalence equal to the canonical restriction map. -/
theorem openExtensionByZero_adjunction_canonical {X : TopCat.{u}} (U : Opens X) :
    ∃ a : openExtensionByZeroFunctor U ⊣
        TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion',
      ∀ (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (G : X.Sheaf AddCommGrpCat.{u})
        (φ : openExtensionByZero U F ⟶ G),
        a.homEquiv F G φ = openExtensionByZeroCanonicalRestriction U F G φ :=
  ⟨openExtensionByZeroAdjunction U, openExtensionByZeroAdjunction_homEquiv U⟩

end Hartshorne
