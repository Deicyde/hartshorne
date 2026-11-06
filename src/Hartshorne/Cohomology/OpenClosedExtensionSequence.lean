/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ClosedExtensionByZero
import Hartshorne.Scheme.OpenExtensionByZeroProperties
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Sheafify
import Batteries.Tactic.OpenPrivate

/-!
# The open–closed extension exact sequence

Hartshorne, *Algebraic Geometry*, II.1, Exercise 1.19(c), as used in III.2.

Let `i : Y ⟶ X` be the inclusion of a closed subset and `j : U ⟶ X` the inclusion of its
open complement. For an abelian sheaf `F` on `X` there is a short exact sequence
`0 ⟶ j_!(F|_U) ⟶ F ⟶ i_*(F|_Y) ⟶ 0`, natural in `F`. Here `F|_U` and `F|_Y` are the inverse
images along the two inclusions, the first map is the counit of the adjunction between
extension by zero and restriction, and the second is the unit of the adjunction between
inverse and direct image. The sequence is a short complex in the category of endofunctors of
abelian sheaves on `X`, so naturality in `F` is built in. Exactness is checked on stalks: at a
point of `U` the first map is an isomorphism on stalks and the third term has zero stalk, and at
a point of `Y` the first term has zero stalk and the second map is an isomorphism on stalks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject

namespace Hartshorne

universe u

/-- Mathlib's stalk-pushforward comparison is natural in the presheaf. -/
private theorem stalkPushforward_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    {P Q : X.Presheaf AddCommGrpCat.{u}} (φ : P ⟶ Q) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map φ) ≫
      Q.stalkPushforward AddCommGrpCat.{u} f x =
    P.stalkPushforward AddCommGrpCat.{u} f x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  erw [TopCat.Presheaf.stalkPushforward_germ, TopCat.Presheaf.stalkPushforward_germ_assoc]
  erw [TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Along an inducing map `f`, the unit `F ⟶ f_*(f⁻¹F)` of the sheaf inverse-image adjunction
is invertible on stalks at every point `f x`. The abstract sheaf inverse image is compared with
the sheafified presheaf inverse image, whose stalks are Mathlib's stalk-pullback isomorphism. -/
private theorem stalk_pullbackUnit_isIso {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (F : Y.Sheaf AddCommGrpCat.{u}) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F).hom) := by
  let adjC := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
    AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  let adjA := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f
  have h := Adjunction.unit_leftAdjointUniq_hom_app adjC adjA F
  rw [← h]
  let P := (TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj F.presheaf
  let t := toSheafify (Opens.grothendieckTopology X) P
  have hC : (adjC.unit.app F).hom =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F.presheaf) ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map t := by
    change (sheafToPresheaf _ _).map (adjC.unit.app F) = _
    simp only [adjC, Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
      Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app]
    simp
    rfl
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
      (adjC.unit.app F).hom) := by
    rw [hC, Functor.map_comp]
    have h1 : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f
        (sheafify (Opens.grothendieckTopology X) P) x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u} hf _ x
    have h2 := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
    have key : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
            F.presheaf) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map t)) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f
          (sheafify (Opens.grothendieckTopology X) P) x =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f F.presheaf x).hom ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map t := by
      rw [Category.assoc, stalkPushforward_naturality]
      rfl
    have : IsIso (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
            F.presheaf) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map t)) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f
          (sheafify (Opens.grothendieckTopology X) P) x) := by
      rw [key]; infer_instance
    exact IsIso.of_isIso_comp_right _
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f
          (sheafify (Opens.grothendieckTopology X) P) x)
  rw [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
  infer_instance

variable {X : TopCat.{u}} (Y : Set X) (hY : IsClosed Y)

/-- The open complement of a closed subset. -/
def closedComplementOpens : Opens X := ⟨Yᶜ, hY.isOpen_compl⟩

/-- The functor `F ↦ j_!(F|_U)`, for `U` the open complement of `Y`. -/
def openClosedOpenPart : X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} (closedComplementOpens Y hY).inclusion' ⋙
    openExtensionByZeroFunctor (closedComplementOpens Y hY)

/-- The functor `F ↦ i_*(F|_Y)`, for the inclusion `i` of the closed subset `Y`. -/
def openClosedClosedPart : X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} (closedSubspaceInclusion X Y) ⋙
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Y)

/-- A morphism of abelian sheaves whose stalk maps all vanish is zero. -/
private theorem sheafHom_eq_zero_of_stalk {F G : X.Sheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (h : ∀ x : X, (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.hom = 0) :
    φ = 0 := by
  apply ObjectProperty.hom_ext
  ext U s
  apply TopCat.Presheaf.section_ext G (unop U)
  intro x hx
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_apply (unop U) x hx φ.hom s, h x]
  have h0 : (0 : F ⟶ G).hom = 0 := rfl
  rw [h0]
  simp
  rfl

open private openStalk_map_isIso_of_pullback_map_isIso from
  Hartshorne.Scheme.OpenExtensionByZeroProperties

set_option backward.isDefEq.respectTransparency false in
/-- At a point of the open complement, the extension-by-zero counit is invertible on stalks. -/
private theorem openPart_counit_stalk_isIso (F : X.Sheaf AddCommGrpCat.{u}) (x : X)
    (hx : x ∉ Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((openExtensionByZeroAdjunction (closedComplementOpens Y hY)).counit.app F).hom) := by
  let U := closedComplementOpens Y hY
  let adj := openExtensionByZeroAdjunction U
  have hunit :
      IsIso (adj.unit.app ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj F)) := by
    erw [← openExtensionByZeroRestrictionIso_inv_app]
    infer_instance
  have : IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map (adj.counit.app F)) := by
    have htri : IsIso (adj.unit.app ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj F) ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map (adj.counit.app F)) := by
      erw [adj.right_triangle_components F]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left
      (adj.unit.app ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj F)) _
  exact openStalk_map_isIso_of_pullback_map_isIso U (adj.counit.app F) ⟨x, hx⟩

/-- At a point of the closed subset, `j_!(F|_U)` has zero stalk. -/
private theorem openPart_stalk_isZero (F : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ Y) :
    IsZero (((openClosedOpenPart Y hY).obj F).presheaf.stalk x) :=
  openExtensionByZero_stalk_isZero_of_not_mem (closedComplementOpens Y hY) _ x
    (fun h => h hx)

/-- At a point of the closed subset, the inverse-image unit is invertible on stalks. -/
private theorem closedPart_unit_stalk_isIso (F : X.Sheaf AddCommGrpCat.{u}) (x : X)
    (hx : x ∈ Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (closedSubspaceInclusion X Y)).unit.app F).hom) :=
  stalk_pullbackUnit_isIso (closedSubspaceInclusion X Y)
    Topology.IsEmbedding.subtypeVal.isInducing F (⟨x, hx⟩ : Y)

include hY in
/-- Off the closed subset, `i_*(F|_Y)` has zero stalk. -/
private theorem closedPart_stalk_isZero (F : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∉ Y) :
    IsZero (((openClosedClosedPart Y).obj F).presheaf.stalk x) :=
  (isZero_zero _).of_iso (closedExtensionByZeroOffImageStalkIso Y hY _ x hx)

set_option backward.isDefEq.respectTransparency false in
/-- **Hartshorne II.1.19(c).** The open–closed extension sequence
`j_!(F|_U) ⟶ F ⟶ i_*(F|_Y)`, as a short complex of endofunctors of abelian sheaves on `X`.
Its maps are the extension-by-zero counit and the inverse-image unit. -/
def openClosedExtensionSequence :
    ShortComplex (X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u}) where
  X₁ := openClosedOpenPart Y hY
  X₂ := 𝟭 _
  X₃ := openClosedClosedPart Y
  f := (openExtensionByZeroAdjunction (closedComplementOpens Y hY)).counit
  g := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (closedSubspaceInclusion X Y)).unit
  zero := by
    ext1
    funext F
    rw [NatTrans.comp_app, NatTrans.app_zero]
    apply sheafHom_eq_zero_of_stalk
    intro x
    rw [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
    by_cases hx : x ∈ Y
    · exact (openPart_stalk_isZero Y hY F x hx).eq_of_src _ _
    · exact (closedPart_stalk_isZero Y hY F x hx).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
/-- **Hartshorne II.1.19(c).** For every abelian sheaf `F` on `X`, the sequence
`0 ⟶ j_!(F|_U) ⟶ F ⟶ i_*(F|_Y) ⟶ 0` is short exact. Naturality in `F` is the statement that
these sequences are the values at `F` of one short complex of functors. -/
theorem openClosedExtensionSequence_shortExact (F : X.Sheaf AddCommGrpCat.{u}) :
    ((openClosedExtensionSequence Y hY).map ((evaluation _ _).obj F)).ShortExact := by
  set T := (openClosedExtensionSequence Y hY).map ((evaluation _ _).obj F) with hT
  have hf : ∀ x : X, x ∉ Y →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map T.f.hom) :=
    fun x hx => openPart_counit_stalk_isIso Y hY F x hx
  have hg : ∀ x : X, x ∈ Y →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map T.g.hom) :=
    fun x hx => closedPart_unit_stalk_isIso Y F x hx
  have h₁ : ∀ x : X, x ∈ Y → IsZero (T.X₁.presheaf.stalk x) :=
    fun x hx => openPart_stalk_isZero Y hY F x hx
  have h₃ : ∀ x : X, x ∉ Y → IsZero (T.X₃.presheaf.stalk x) :=
    fun x hx => closedPart_stalk_isZero Y hY F x hx
  have hmono : Mono T.f := by
    rw [TopCat.Presheaf.mono_iff_stalk_mono]
    intro x
    by_cases hx : x ∈ Y
    · exact (h₁ x hx).mono _
    · have := hf x hx
      infer_instance
  have hepi : Epi T.g := by
    let S' := ShortComplex.mk T.g (0 : T.X₃ ⟶ 0) comp_zero
    rw [← S'.exact_iff_epi rfl, TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    intro x
    rw [ShortComplex.exact_iff_epi _ (by simp [S'])]
    by_cases hx : x ∈ Y
    · have := hg x hx
      change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map T.g.hom)
      infer_instance
    · exact (h₃ x hx).epi _
  refine ⟨?_⟩
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  by_cases hx : x ∈ Y
  · rw [ShortComplex.exact_iff_mono _ ((h₁ x hx).eq_of_src _ _)]
    have := hg x hx
    change Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map T.g.hom)
    infer_instance
  · rw [ShortComplex.exact_iff_epi _ ((h₃ x hx).eq_of_tgt _ _)]
    have := hf x hx
    change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map T.f.hom)
    infer_instance

end Hartshorne
