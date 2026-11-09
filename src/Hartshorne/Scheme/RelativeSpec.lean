/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Relative Spec of a quasi-coherent algebra

Hartshorne II, Exercise 5.17(c,d).

## Encoding of quasi-coherent algebras

Following Mathlib (`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean`) and the project's
relative `Proj` (`Hartshorne.Scheme.RelativeProj`), a quasi-coherent `𝒪_Y`-algebra is recorded
through its rings of sections over the affine opens of `Y` (the small affine Zariski site
`Y.AffineZariskiSite`, whose arrows are the basic open inclusions `D(r) ⊆ U`): a functor
`A : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat` with an `𝒪_Y`-algebra structure `Γ(U, 𝒪_Y) → A(U)`
such that `A(D(r)) = A(U)_r` (`NatTrans.Coequifibered`). Morphisms are natural transformations
compatible with the structure maps (the category `QuasiCoherentAlgebra Y`).

## Main results

* `QuasiCoherentAlgebra.relSpec`, `relSpecToBase`: the scheme `Spec_Y A` and the affine morphism
  `Spec_Y A ⟶ Y`, with `relSpecToBase_preimage`, `restrictIso`: over every affine `V ⊆ Y`, the
  inverse image is `Spec A(V)`.
* `QuasiCoherentAlgebra.pushforwardStructureSheafIso`: `f_* 𝒪_{Spec_Y A} ≅ A`.
* `QuasiCoherentAlgebra.ofHom`, `relSpecOfHomIso`: an affine morphism `f : X ⟶ Y` gives the
  quasi-coherent algebra `f_* 𝒪_X`, and `Spec_Y (f_* 𝒪_X) ≅ X` over `Y`.
* `relativeSpecEquiv`: these constructions are mutually inverse bijections between isomorphism
  classes of quasi-coherent `𝒪_Y`-algebras and isomorphism classes of affine schemes over `Y`.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry Scheme.AffineZariskiSite

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

lemma appLE_eq_of_eq {X Z : Scheme.{u}} {f g : X ⟶ Z} (h : f = g) (U : Z.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

@[reassoc]
lemma SpecMap_appLE_top_ΓSpecIso {R S : CommRingCat.{u}} (φ : R ⟶ S) (e) :
    (Spec.map φ).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso S).hom = (Scheme.ΓSpecIso R).hom ≫ φ := by
  change (Spec.map φ).appLE ⊤ (Spec.map φ ⁻¹ᵁ ⊤) le_rfl ≫ _ = _
  rw [Scheme.Hom.appLE_eq_app]
  exact Scheme.ΓSpecIso_naturality φ

variable (Y : Scheme.{u})

/-- A quasi-coherent sheaf of `𝒪_Y`-algebras, recorded through its rings of sections `A(U)` over
the affine opens `U` of `Y` with restrictions along basic opens, together with the
`𝒪_Y`-algebra structure `Γ(U, 𝒪_Y) → A(U)`, such that `A(D(r)) = A(U)_r` (quasi-coherence).
Morphisms are morphisms of `𝒪_Y`-algebras. -/
def QuasiCoherentAlgebra : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun A : Under ((toOpensFunctor Y).op ⋙ Y.presheaf) => NatTrans.Coequifibered A.hom)

instance : Category (QuasiCoherentAlgebra Y) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory _))

namespace QuasiCoherentAlgebra

variable {Y} (A : QuasiCoherentAlgebra Y)

/-- The rings of sections `A(U)` over the affine opens `U`. -/
abbrev sections : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} := A.obj.right

/-- The structure map `Γ(U, 𝒪_Y) → A(U)`. -/
abbrev structureMap : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ A.sections := A.obj.hom

lemma coequifibered : NatTrans.Coequifibered A.structureMap := A.property

/-- The relative gluing datum `U ↦ (Spec A(U) ⟶ U)` over the affine opens of `Y`. -/
abbrev gluingData : (directedCover Y).RelativeGluingData :=
  relativeGluingData A.coequifibered

instance : (A.gluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The relative spectrum `Spec_Y A`: the glued scheme of the `Spec A(U)` over the affine
opens `U` of `Y`. -/
abbrev relSpec : Scheme.{u} := A.gluingData.glued

/-- The structure morphism `Spec_Y A ⟶ Y`. -/
abbrev relSpecToBase : A.relSpec ⟶ Y := A.gluingData.toBase

/-- The open immersion `Spec A(U) ⟶ Spec_Y A` of the piece over an affine open `U`. -/
def ι (U : Y.AffineZariskiSite) : Spec (A.sections.obj (.op U)) ⟶ A.relSpec :=
  A.gluingData.cover.f U

instance isOpenImmersion_ι (U : Y.AffineZariskiSite) : IsOpenImmersion (A.ι U) :=
  A.gluingData.cover.map_prop U

lemma natTrans_app (U : Y.AffineZariskiSite) :
    A.gluingData.natTrans.app U = Spec.map (A.structureMap.app (.op U)) ≫ U.2.isoSpec.inv :=
  rfl

@[reassoc]
lemma ι_relSpecToBase (U : Y.AffineZariskiSite) :
    A.ι U ≫ A.relSpecToBase = Spec.map (A.structureMap.app (.op U)) ≫ U.2.fromSpec := by
  have := A.gluingData.ι_toBase U
  rw [natTrans_app] at this
  exact this.trans (Category.assoc _ _ _)

@[reassoc]
lemma map_ι {U V : Y.AffineZariskiSite} (i : U ⟶ V) :
    Spec.map (A.sections.map i.op) ≫ A.ι V = A.ι U :=
  colimit.w A.gluingData.functor i

lemma relSpecToBase_preimage (U : Y.AffineZariskiSite) :
    A.relSpecToBase ⁻¹ᵁ U.toOpens = (A.ι U).opensRange := by
  have := A.gluingData.toBase_preimage_eq_opensRange_ι U
  simp only [Scheme.Opens.opensRange_ι] at this
  exact this

instance isAffineHom_relSpecToBase : IsAffineHom A.relSpecToBase := by
  refine ⟨fun U hU => ?_⟩
  rw [A.relSpecToBase_preimage ⟨U, hU⟩]
  have := A.isOpenImmersion_ι ⟨U, hU⟩
  exact isAffineOpen_opensRange _

/-- Over every affine open `V ⊆ Y`, `Spec A(V)` is the fibre product `V ×_Y Spec_Y A`. -/
lemma isPullback_ι (U : Y.AffineZariskiSite) :
    IsPullback (Spec.map (A.structureMap.app (.op U)) ≫ U.2.isoSpec.inv) (A.ι U) U.toOpens.ι
      A.relSpecToBase := by
  have := A.gluingData.isPullback_natTrans_ι_toBase U
  rw [natTrans_app] at this
  exact this

/-- The canonical isomorphism `f⁻¹(V) ≅ Spec A(V)` over an affine open `V ⊆ Y`, where
`f : Spec_Y A ⟶ Y`. -/
def restrictIso (U : Y.AffineZariskiSite) :
    (A.relSpecToBase ⁻¹ᵁ U.toOpens).toScheme ≅ Spec (A.sections.obj (.op U)) :=
  A.relSpec.isoOfEq (A.relSpecToBase_preimage U) ≪≫ (A.ι U).isoOpensRange.symm

lemma restrictIso_hom_fromSpec (U : Y.AffineZariskiSite) :
    (A.restrictIso U).hom ≫ Spec.map (A.structureMap.app (.op U)) ≫ U.2.fromSpec =
      (A.relSpecToBase ⁻¹ᵁ U.toOpens).ι ≫ A.relSpecToBase := by
  rw [← ι_relSpecToBase]
  simp [restrictIso]

/-! ### Functoriality in isomorphisms -/

section Iso

variable {A B : QuasiCoherentAlgebra Y}

/-- An isomorphism of quasi-coherent algebras, on rings of sections. -/
def sectionsIso (e : A ≅ B) : A.sections ≅ B.sections :=
  (Under.forget _).mapIso ((ObjectProperty.ι _).mapIso e)

@[reassoc (attr := simp)]
lemma structureMap_sectionsIso_hom (e : A ≅ B) :
    A.structureMap ≫ (sectionsIso e).hom = B.structureMap :=
  Under.w ((ObjectProperty.ι _).map e.hom)

@[reassoc (attr := simp)]
lemma structureMap_sectionsIso_inv (e : A ≅ B) :
    B.structureMap ≫ (sectionsIso e).inv = A.structureMap := by
  rw [← structureMap_sectionsIso_hom e, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The gluing diagrams of isomorphic quasi-coherent algebras are isomorphic. -/
def functorIso (e : A ≅ B) : A.gluingData.functor ≅ B.gluingData.functor :=
  NatIso.ofComponents (fun U => Scheme.Spec.mapIso ((sectionsIso e).app (.op U)).symm.op)
    (fun {U V} i => by
      change Spec.map (A.sections.map i.op) ≫ Spec.map ((sectionsIso e).inv.app (.op V)) =
        Spec.map ((sectionsIso e).inv.app (.op U)) ≫ Spec.map (B.sections.map i.op)
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact ((sectionsIso e).inv.naturality i.op).symm)

/-- Isomorphic quasi-coherent algebras have isomorphic relative spectra. -/
def relSpecIso (e : A ≅ B) : A.relSpec ≅ B.relSpec :=
  HasColimit.isoOfNatIso (functorIso e)

@[reassoc (attr := simp)]
lemma relSpecIso_hom_relSpecToBase (e : A ≅ B) :
    (relSpecIso e).hom ≫ B.relSpecToBase = A.relSpecToBase := by
  refine colimit.hom_ext fun U => ?_
  rw [relSpecIso, HasColimit.isoOfNatIso_ι_hom_assoc]
  change (functorIso e).hom.app U ≫ B.ι U ≫ B.relSpecToBase = A.ι U ≫ A.relSpecToBase
  rw [ι_relSpecToBase, ι_relSpecToBase]
  change Spec.map ((sectionsIso e).inv.app (.op U)) ≫ _ = _
  rw [← Spec.map_comp_assoc, ← NatTrans.comp_app, structureMap_sectionsIso_inv]

end Iso

/-! ### The quasi-coherent algebra `f_* 𝒪_X` -/

section OfHom

variable {X : Scheme.{u}} (f : X ⟶ Y)

lemma coequifibered_pushforward [QuasiCompact f] [QuasiSeparated f] :
    NatTrans.Coequifibered (Functor.whiskerLeft (toOpensFunctor Y).op f.c) := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  change @IsLocalization.Away _ _ (f.app U.1 r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) _ inst
  let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
  dsimp +instances [inst]
  rw! (castMode := .all) [f.preimage_basicOpen r]
  exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
    (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)

/-- For a quasi-compact quasi-separated (e.g. affine) morphism `f : X ⟶ Y`, the quasi-coherent
`𝒪_Y`-algebra `f_* 𝒪_X`: `U ↦ Γ(f⁻¹ U, 𝒪_X)`. -/
def ofHom [QuasiCompact f] [QuasiSeparated f] : QuasiCoherentAlgebra Y :=
  ⟨Under.mk (Functor.whiskerLeft (toOpensFunctor Y).op f.c), coequifibered_pushforward f⟩

end OfHom

/-! ### `f_* 𝒪_{Spec_Y A} ≅ A` -/

section Pushforward

lemma ι_preimage_relSpecToBase_preimage (U : Y.AffineZariskiSite) :
    A.ι U ⁻¹ᵁ A.relSpecToBase ⁻¹ᵁ U.toOpens = ⊤ := by
  have h := congrArg (fun g => g ⁻¹ᵁ U.toOpens) (A.ι_relSpecToBase U)
  simp only [Scheme.Hom.comp_preimage] at h
  rw [h, IsAffineOpen.fromSpec_preimage_self, Scheme.Hom.preimage_top]

/-- The comparison `Γ(f⁻¹ U, 𝒪_{Spec_Y A}) ⟶ A(U)`, restriction to the piece `Spec A(U)`. -/
def pushforwardSectionsHom (U : Y.AffineZariskiSite) :
    Γ(A.relSpec, A.relSpecToBase ⁻¹ᵁ U.toOpens) ⟶ A.sections.obj (.op U) :=
  (A.ι U).appLE _ ⊤ (A.ι_preimage_relSpecToBase_preimage U).ge ≫
    (Scheme.ΓSpecIso (A.sections.obj (.op U))).hom

instance (U : Y.AffineZariskiSite) : IsIso (A.pushforwardSectionsHom U) := by
  have : IsIso ((A.ι U).app (A.relSpecToBase ⁻¹ᵁ U.toOpens)) :=
    Scheme.Hom.isIso_app _ _ (by rw [A.relSpecToBase_preimage U])
  rw [pushforwardSectionsHom, Scheme.Hom.appLE,
    Subsingleton.elim (homOfLE (A.ι_preimage_relSpecToBase_preimage U).ge)
      (eqToHom (A.ι_preimage_relSpecToBase_preimage U).symm)]
  infer_instance

lemma appLE_ι_map {U V : Y.AffineZariskiSite} (i : U ⟶ V) (W : A.relSpec.Opens)
    (e : ⊤ ≤ A.ι U ⁻¹ᵁ W) (e' : ⊤ ≤ A.ι V ⁻¹ᵁ W) :
    (A.ι U).appLE W ⊤ e =
      (A.ι V).appLE W ⊤ e' ≫ (Spec.map (A.sections.map i.op)).appLE ⊤ ⊤ le_top := by
  rw [Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq (A.map_ι i).symm _ _ _

@[reassoc]
lemma pushforwardSectionsHom_naturality {U V : Y.AffineZariskiSite} (i : U ⟶ V) :
    A.relSpec.presheaf.map
        (homOfLE (A.relSpecToBase.preimage_mono (toOpens_mono (leOfHom i)))).op ≫
      A.pushforwardSectionsHom U =
    A.pushforwardSectionsHom V ≫ A.sections.map i.op := by
  rw [pushforwardSectionsHom, pushforwardSectionsHom, Scheme.Hom.map_appLE_assoc,
    A.appLE_ι_map i _ _ (A.ι_preimage_relSpecToBase_preimage V).ge, Category.assoc,
    SpecMap_appLE_top_ΓSpecIso, Category.assoc]

/-- The comparison `f_* 𝒪_{Spec_Y A} ⟶ A` on rings of sections. -/
def pushforwardSectionsNatTrans : (ofHom A.relSpecToBase).sections ⟶ A.sections where
  app U := A.pushforwardSectionsHom U.unop
  naturality {U V} i := by
    exact A.pushforwardSectionsHom_naturality i.unop

lemma pushforward_structureMap_comp :
    (ofHom A.relSpecToBase).structureMap ≫ A.pushforwardSectionsNatTrans = A.structureMap := by
  ext U : 2
  change A.relSpecToBase.app U.unop.toOpens ≫ A.pushforwardSectionsHom U.unop = _
  rw [pushforwardSectionsHom, ← Scheme.Hom.comp_appLE_assoc,
    appLE_eq_of_eq (A.ι_relSpecToBase U.unop), Scheme.Hom.comp_appLE_assoc,
    IsAffineOpen.fromSpec_app_self, Category.assoc, Scheme.Hom.map_appLE_assoc,
    SpecMap_appLE_top_ΓSpecIso]
  exact Iso.inv_hom_id_assoc _ _

/-- **`f_* 𝒪_{Spec_Y A} ≅ A`.** For `f : Spec_Y A ⟶ Y`, the quasi-coherent algebra `f_* 𝒪` is
isomorphic to `A`. -/
def pushforwardStructureSheafIso : ofHom A.relSpecToBase ≅ A :=
  have : ∀ U, IsIso (A.pushforwardSectionsNatTrans.app U) := fun U =>
    (inferInstance : IsIso (A.pushforwardSectionsHom U.unop))
  have : IsIso A.pushforwardSectionsNatTrans := NatIso.isIso_of_isIso_app _
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (Under.isoMk (asIso A.pushforwardSectionsNatTrans) A.pushforward_structureMap_comp)

end Pushforward

/-! ### Every affine morphism is a relative spectrum -/

section Affine

variable {X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

/-- The cocone `Spec Γ(f⁻¹ U, 𝒪_X) ⟶ X` over the gluing diagram of `f_* 𝒪_X`. -/
def toSchemeCocone : Cocone (ofHom f).gluingData.functor where
  pt := X
  ι :=
    { app U := (U.2.preimage f).fromSpec
      naturality {U V} i := by
        exact (IsAffineOpen.map_fromSpec _ _ _).trans (Category.comp_id _).symm }

/-- The canonical morphism `Spec_Y (f_* 𝒪_X) ⟶ X`. -/
def relSpecOfHomHom : (ofHom f).relSpec ⟶ X :=
  colimit.desc _ (toSchemeCocone f)

@[reassoc]
lemma ι_relSpecOfHomHom (U : Y.AffineZariskiSite) :
    (ofHom f).ι U ≫ relSpecOfHomHom f = (U.2.preimage f).fromSpec :=
  colimit.ι_desc _ _

@[reassoc (attr := simp)]
lemma relSpecOfHomHom_comp : relSpecOfHomHom f ≫ f = (ofHom f).relSpecToBase := by
  refine colimit.hom_ext fun U => ?_
  change (ofHom f).ι U ≫ relSpecOfHomHom f ≫ f = (ofHom f).ι U ≫ (ofHom f).relSpecToBase
  rw [ι_relSpecToBase, ι_relSpecOfHomHom_assoc]
  change (U.2.preimage f).fromSpec ≫ f = Spec.map (f.app U.1) ≫ U.2.fromSpec
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f U.2 (U.2.preimage f) le_rfl,
    Scheme.Hom.appLE_eq_app]

instance : IsIso (relSpecOfHomHom f) := by
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _)
    (fun U : Y.affineOpens => f ⁻¹ᵁ U.1)
    (by rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top])]
  intro U
  let V : Y.AffineZariskiSite := ⟨U.1, U.2⟩
  have hpre : relSpecOfHomHom f ⁻¹ᵁ f ⁻¹ᵁ U.1 = ((ofHom f).ι V).opensRange := by
    rw [← Scheme.Hom.comp_preimage, relSpecOfHomHom_comp, (ofHom f).relSpecToBase_preimage V]
  let e := IsOpenImmersion.isoOfRangeEq ((ofHom f).ι V) (relSpecOfHomHom f ⁻¹ᵁ f ⁻¹ᵁ U.1).ι
    (by rw [Scheme.Opens.range_ι, hpre, Scheme.Hom.coe_opensRange])
  have key : e.hom ≫ relSpecOfHomHom f ∣_ (f ⁻¹ᵁ U.1) = (V.2.preimage f).isoSpec.inv := by
    rw [← cancel_mono (f ⁻¹ᵁ U.1).ι, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, ι_relSpecOfHomHom, IsAffineOpen.isoSpec_inv_ι]
  have : relSpecOfHomHom f ∣_ (f ⁻¹ᵁ U.1) = e.inv ≫ (V.2.preimage f).isoSpec.inv := by
    rw [← key, Iso.inv_hom_id_assoc]
  rw [MorphismProperty.isomorphisms.iff, this]
  infer_instance

/-- **Every affine morphism is a relative spectrum.** For an affine morphism `f : X ⟶ Y`,
`Spec_Y (f_* 𝒪_X) ≅ X` over `Y`. -/
def relSpecOfHomIso : (ofHom f).relSpec ≅ X :=
  asIso (relSpecOfHomHom f)

@[reassoc (attr := simp)]
lemma relSpecOfHomIso_hom_comp : (relSpecOfHomIso f).hom ≫ f = (ofHom f).relSpecToBase :=
  relSpecOfHomHom_comp f

end Affine

/-! ### Invariance of `f_* 𝒪_X` under isomorphisms over `Y` -/

section OfHomIso

/-- For an isomorphism `g : X ⟶ X'` and `f' : X' ⟶ Y`, `f'_* 𝒪_{X'} ≅ (g ≫ f')_* 𝒪_X`. -/
def ofHomCompIso {X X' : Scheme.{u}} (g : X ⟶ X') [IsIso g] (f' : X' ⟶ Y) [QuasiCompact f']
    [QuasiSeparated f'] [QuasiCompact (g ≫ f')] [QuasiSeparated (g ≫ f')] :
    ofHom f' ≅ ofHom (g ≫ f') :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (Under.isoMk (NatIso.ofComponents (fun U => asIso (g.app (f' ⁻¹ᵁ U.unop.toOpens)))
      (fun i => g.naturality _)) (by ext U; rfl))

/-- `f_* 𝒪_X` only depends on `f` up to equality. -/
def ofHomCongr {X : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact f'] [QuasiSeparated f'] : ofHom f ≅ ofHom f' := by
  subst h; exact Iso.refl _

end OfHomIso

end QuasiCoherentAlgebra

/-! ### The bijection on isomorphism classes -/

open QuasiCoherentAlgebra

/-- Affine schemes over `Y`: schemes `X` with an affine morphism `X ⟶ Y`; morphisms are
morphisms over `Y`. -/
abbrev AffineOver : Type (u + 1) := MorphismProperty.Over (@IsAffineHom) ⊤ Y

variable {Y}

/-- `Spec_Y A`, as an affine scheme over `Y`. -/
def QuasiCoherentAlgebra.relSpecOver (A : QuasiCoherentAlgebra Y) : AffineOver Y :=
  MorphismProperty.Over.mk ⊤ A.relSpecToBase inferInstance

/-- `f_* 𝒪_X`, for an affine scheme `f : X ⟶ Y` over `Y`. -/
def AffineOver.pushforward (Z : AffineOver Y) : QuasiCoherentAlgebra Y :=
  have : IsAffineHom Z.hom := Z.prop
  ofHom Z.hom

lemma QuasiCoherentAlgebra.relSpecOver_iso {A B : QuasiCoherentAlgebra Y} (e : A ≅ B) :
    Nonempty (A.relSpecOver ≅ B.relSpecOver) :=
  ⟨MorphismProperty.Over.isoMk (relSpecIso e) (relSpecIso_hom_relSpecToBase e)⟩

lemma AffineOver.pushforward_iso {Z Z' : AffineOver Y} (e : Z ≅ Z') :
    Nonempty (Z.pushforward ≅ Z'.pushforward) := by
  have : IsAffineHom Z.hom := Z.prop
  have : IsAffineHom Z'.hom := Z'.prop
  have w : e.hom.left ≫ Z'.hom = Z.hom := Over.w ((MorphismProperty.Over.forget _ _ _).map e.hom)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((MorphismProperty.Over.forget _ _ _ ⋙
    Over.forget _).mapIso e).hom)
  have : IsAffineHom (e.hom.left ≫ Z'.hom) := by rw [w]; infer_instance
  exact ⟨(ofHomCongr w.symm).trans (ofHomCompIso e.hom.left Z'.hom).symm⟩

variable (Y) in
attribute [local instance] isIsomorphicSetoid in
/-- **Hartshorne II, Exercise 5.17(d).** `A ↦ Spec_Y A` and `(f : X ⟶ Y) ↦ f_* 𝒪_X` are mutually
inverse bijections between isomorphism classes of quasi-coherent `𝒪_Y`-algebras and isomorphism
classes of affine schemes over `Y`. -/
def relativeSpecEquiv :
    Quotient (isIsomorphicSetoid (QuasiCoherentAlgebra Y)) ≃
      Quotient (isIsomorphicSetoid (AffineOver Y)) where
  toFun := Quotient.map QuasiCoherentAlgebra.relSpecOver fun _ _ ⟨e⟩ =>
    QuasiCoherentAlgebra.relSpecOver_iso e
  invFun := Quotient.map AffineOver.pushforward fun _ _ ⟨e⟩ => AffineOver.pushforward_iso e
  left_inv := Quotient.ind fun A => Quotient.sound ⟨A.pushforwardStructureSheafIso⟩
  right_inv := Quotient.ind fun Z => by
    have : IsAffineHom Z.hom := Z.prop
    exact Quotient.sound ⟨MorphismProperty.Over.isoMk (relSpecOfHomIso Z.hom)
      (relSpecOfHomIso_hom_comp Z.hom)⟩

lemma relativeSpecEquiv_mk (A : QuasiCoherentAlgebra Y) :
    relativeSpecEquiv Y (Quotient.mk _ A) = Quotient.mk _ A.relSpecOver :=
  rfl

lemma relativeSpecEquiv_symm_mk (Z : AffineOver Y) :
    (relativeSpecEquiv Y).symm (Quotient.mk _ Z) = Quotient.mk _ Z.pushforward :=
  rfl

end

end Hartshorne
