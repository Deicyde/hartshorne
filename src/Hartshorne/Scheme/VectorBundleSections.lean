/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.GeometricVectorBundle
import Hartshorne.Scheme.ProjChartMorphism

/-!
# Sections of a geometric vector bundle

Hartshorne II, Exercise 5.18 (pp. 128–129).

## The sheaf of sections

For a morphism `f : X ⟶ Y` and an open `U ⊆ Y`, a *section of `f` over `U`* is a morphism
`s : U ⟶ X` with `f ∘ s = id_U`. Hartshorne's `𝒮(X/Y)` is the presheaf `U ↦ {sections over U}`,
with restriction along inclusions of opens (`sectionsPresheaf f`); it is a sheaf
(`isSheaf_sectionsPresheaf`), since morphisms of schemes glue along open covers.

## Sections of a relative spectrum

For a quasi-coherent `𝒪_Y`-algebra `A` and an affine open `U ⊆ Y`, the sections of
`Spec_Y A ⟶ Y` over `U` are the `𝒪_Y(U)`-algebra maps `A(U) ⟶ 𝒪_Y(U)` (`RelSpecSections.equiv`),
compatibly with restriction (`RelSpecSections.restriction_equiv`). This supplements Hartshorne II,
Exercise 5.17.

## Sections of `V(E)`

For a locally free sheaf `E` of rank `n` and Hartshorne's `V(E) = Spec_Y Sym(E)`,
`Scheme.Modules.vectorBundleSectionsIso` is the natural isomorphism `𝒮(V(E)/Y) ≅ E^∨` of sheaves of
sets (Hartshorne II, Exercise 5.18(c)): over an affine open `V`, a section is an `𝒪_Y(V)`-algebra
map `Γ(V, Sym(E)) ⟶ 𝒪_Y(V)`, and such a map is determined by the `𝒪_Y(V)`-linear map
`E(V) ⟶ 𝒪_Y(V)` it restricts to (`vectorBundleSectionsIso_hom_eval`). Over the affine opens on which
`E` has a frame, `Γ(V, Sym(E))` is a polynomial ring on the frame, which gives the bijectivity
(`sectionDual_bijective`); the isomorphism is the extension from this basis of `Y`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}}

/-- **The presheaf of sections `𝒮(X/Y)` of a morphism `f : X ⟶ Y`** (Hartshorne II, Exercise
5.18): over an open `U ⊆ Y`, the morphisms `s : U ⟶ X` with `f ∘ s = id_U`, that is,
`s ≫ f = U.ι`; restriction to `V ⊆ U` is precomposition with the inclusion `V ⟶ U`. -/
def sectionsPresheaf (f : X ⟶ Y) : TopCat.Presheaf (Type u) Y where
  obj U := {s : Scheme.Opens.toScheme (X := Y) U.unop ⟶ X // s ≫ f = Scheme.Opens.ι (X := Y) U.unop}
  map {U V} i := TypeCat.ofHom fun s => ⟨Y.homOfLE (leOfHom i.unop) ≫ s.1, by
    rw [Category.assoc, s.2, Scheme.homOfLE_ι]⟩
  map_id U := by
    ext s
    change Y.homOfLE _ ≫ s.1 = s.1
    rw [Scheme.homOfLE_rfl, Category.id_comp]
  map_comp {U V W} i j := by
    ext s
    change Y.homOfLE _ ≫ s.1 = Y.homOfLE _ ≫ Y.homOfLE _ ≫ s.1
    rw [Scheme.homOfLE_homOfLE_assoc]

lemma sectionsPresheaf_map_coe (f : X ⟶ Y) {U V : Y.Opens} (i : V ⟶ U)
    (s : (sectionsPresheaf f).obj (op U)) :
    ((sectionsPresheaf f).map i.op s).1 = Y.homOfLE (leOfHom i) ≫ s.1 := rfl

/-- For opens `U ≤ W` of `Y`, the inclusion `U ⟶ W` identifies `U` with the open `W.ι⁻¹(U)` of
`W`: it factors through `W.ι⁻¹(U)` by a section of the restriction of `W.ι` to `U`. -/
private lemma exists_homOfLE_factor {U W : Y.Opens} (h : U ≤ W) :
    ∃ k : U.toScheme ⟶ (W.ι ⁻¹ᵁ U).toScheme,
      k ≫ (W.ι ⁻¹ᵁ U).ι = Y.homOfLE h ∧ k ≫ (W.ι ∣_ U) = 𝟙 _ := by
  have hrange : Set.range (Y.homOfLE h) ⊆ Set.range (W.ι ⁻¹ᵁ U).ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨Y.homOfLE h x, ?_⟩, rfl⟩
    change W.ι (Y.homOfLE h x) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact x.2
  refine ⟨IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc,
    Scheme.homOfLE_ι, Category.id_comp]

/-- **The sections of a morphism form a sheaf** (Hartshorne II, Exercise 5.18): sections over the
members of an open covering that agree on overlaps glue uniquely. -/
theorem isSheaf_sectionsPresheaf (f : X ⟶ Y) : (sectionsPresheaf f).IsSheaf := by
  refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf hsf => ?_
  set W : Y.Opens := iSup U
  let V : ι → W.toScheme.Opens := fun i => W.ι ⁻¹ᵁ U i
  have hV : IsOpenCover V := by
    refine eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2
    exact ⟨i, hi⟩
  have hle : ∀ i, U i ≤ W := fun i => le_iSup U i
  -- `V i ⟶ U i`, the restriction of `W.ι`
  let r : ∀ i, (V i).toScheme ⟶ (Scheme.Opens.toScheme (X := Y) (U i)) := fun i => W.ι ∣_ U i
  have hr : ∀ i, r i ≫ (Scheme.Opens.ι (X := Y) (U i)) = (V i).ι ≫ W.ι := fun i => morphismRestrict_ι _ _
  have hVι : ∀ i, (V i).ι = r i ≫ Y.homOfLE (hle i) := fun i => by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, hr]
  have hcomp : ∀ i j, W.toScheme.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ r i ≫ (sf i).1 =
      W.toScheme.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ r j ≫ (sf j).1 := by
    intro i j
    have hm : Set.range ((V i ⊓ V j).ι ≫ W.ι) ⊆ Set.range (Scheme.Opens.ι (X := Y) (U i ⊓ U j)) := by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨W.ι ((V i ⊓ V j).ι x), ?_⟩, rfl⟩
      exact ⟨(x.2 : _ ∈ V i ⊓ V j).1, (x.2 : _ ∈ V i ⊓ V j).2⟩
    let m := IsOpenImmersion.lift (Scheme.Opens.ι (X := Y) (U i ⊓ U j)) ((V i ⊓ V j).ι ≫ W.ι) hm
    have hm' : (V i ⊓ V j).ι ≫ W.ι = m ≫ (Scheme.Opens.ι (X := Y) (U i ⊓ U j)) := (IsOpenImmersion.lift_fac _ _ _).symm
    have hi : W.toScheme.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ r i =
        m ≫ Y.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := by
      rw [← cancel_mono (Scheme.Opens.ι (X := Y) (U i)), Category.assoc, hr, Category.assoc, Scheme.homOfLE_ι_assoc,
        Scheme.homOfLE_ι, hm']
    have hj : W.toScheme.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ r j =
        m ≫ Y.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := by
      rw [← cancel_mono (Scheme.Opens.ι (X := Y) (U j)), Category.assoc, hr, Category.assoc, Scheme.homOfLE_ι_assoc,
        Scheme.homOfLE_ι, hm']
    have hc := congrArg Subtype.val (hsf i j)
    simp only [sectionsPresheaf_map_coe] at hc
    rw [← Category.assoc, hi, ← Category.assoc, hj, Category.assoc, Category.assoc]
    exact congrArg (m ≫ ·) hc
  let g : W.toScheme ⟶ X := Hartshorne.glueOpens V hV (fun i => r i ≫ (sf i).1) hcomp
  have hg : ∀ i, (V i).ι ≫ g = r i ≫ (sf i).1 := fun i => Hartshorne.ι_glueOpens _ _ _ _ i
  have hgf : g ≫ f = W.ι := by
    refine (W.toScheme.openCoverOfIsOpenCover V hV).hom_ext _ _ fun i => ?_
    change (V i).ι ≫ g ≫ f = (V i).ι ≫ W.ι
    rw [reassoc_of% (hg i), (sf i).2, hr]
  refine ⟨⟨g, hgf⟩, fun i => Subtype.ext ?_, fun s hs => Subtype.ext ?_⟩
  · change Y.homOfLE (hle i) ≫ g = (sf i).1
    obtain ⟨k, hk, hk'⟩ := exists_homOfLE_factor (hle i)
    rw [← hk, Category.assoc, hg, reassoc_of% hk']
  · refine (W.toScheme.openCoverOfIsOpenCover V hV).hom_ext _ _ fun i => ?_
    change (V i).ι ≫ s.1 = (V i).ι ≫ g
    rw [hg, hVι, Category.assoc]
    have := congrArg Subtype.val (hs i)
    rw [sectionsPresheaf_map_coe] at this
    exact congrArg (r i ≫ ·) this

/-! ### Sections of a relative spectrum over an affine open -/

namespace RelSpecSections

open Hartshorne

variable (A : QuasiCoherentAlgebra Y) (U : Y.AffineZariskiSite)

/-- The section `U ⟶ Spec A(U) ⟶ Spec_Y A` of a ring map `φ : A(U) ⟶ Γ(U, 𝒪_Y)`. -/
def sectionOfHom (φ : A.sections.obj (op U) ⟶ Γ(Y, U.toOpens)) :
    U.toOpens.toScheme ⟶ A.relSpec :=
  U.toOpens.toSpecΓ ≫ Spec.map φ ≫ A.ι U

lemma range_subset (s : U.toOpens.toScheme ⟶ A.relSpec) (hs : s ≫ A.relSpecToBase = U.toOpens.ι) :
    Set.range s ⊆ Set.range (A.ι U) := by
  rintro _ ⟨x, rfl⟩
  have : s x ∈ A.relSpecToBase ⁻¹ᵁ U.toOpens := by
    change (s ≫ A.relSpecToBase) x ∈ U.toOpens
    rw [hs]
    exact x.2
  rw [A.relSpecToBase_preimage U] at this
  exact this

/-- The ring map `A(U) ⟶ Γ(U, 𝒪_Y)` of a section `s` of `Spec_Y A` over an affine open `U`: the
global sections of the factorization `U ⟶ Spec A(U)` of `s`. -/
def homOfSection (s : U.toOpens.toScheme ⟶ A.relSpec)
    (hs : s ≫ A.relSpecToBase = U.toOpens.ι) : A.sections.obj (op U) ⟶ Γ(Y, U.toOpens) :=
  (Scheme.ΓSpecIso _).inv ≫ (IsOpenImmersion.lift (A.ι U) s (range_subset A U s hs)).appTop ≫
    U.toOpens.topIso.hom

/-- A morphism `t : V ⟶ Spec R` from an open `V` of `Y` is determined by the ring map
`R ⟶ Γ(V, 𝒪_Y)` of its global sections. -/
private lemma toSpecΓ_SpecMap_appTop {R : CommRingCat.{u}} (V : Y.Opens) (t : V.toScheme ⟶ Spec R) :
    V.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ t.appTop ≫ V.topIso.hom) = t := by
  rw [Scheme.Opens.toSpecΓ, Category.assoc, ← Spec.map_comp, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private lemma appTop_toSpecΓ_SpecMap {R : CommRingCat.{u}} (V : Y.Opens) (φ : R ⟶ Γ(Y, V)) :
    (Scheme.ΓSpecIso R).inv ≫ (V.toSpecΓ ≫ Spec.map φ).appTop ≫ V.topIso.hom = φ := by
  rw [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

lemma sectionOfHom_homOfSection (s : U.toOpens.toScheme ⟶ A.relSpec)
    (hs : s ≫ A.relSpecToBase = U.toOpens.ι) :
    sectionOfHom A U (homOfSection A U s hs) = s := by
  rw [sectionOfHom, homOfSection, ← Category.assoc, toSpecΓ_SpecMap_appTop,
    IsOpenImmersion.lift_fac]

lemma homOfSection_sectionOfHom (φ : A.sections.obj (op U) ⟶ Γ(Y, U.toOpens)) (hs) :
    homOfSection A U (sectionOfHom A U φ) hs = φ := by
  rw [homOfSection]
  have : IsOpenImmersion.lift (A.ι U) (sectionOfHom A U φ) (range_subset A U _ hs) =
      U.toOpens.toSpecΓ ≫ Spec.map φ :=
    (IsOpenImmersion.lift_uniq _ _ _ _ (Category.assoc _ _ _)).symm
  rw [this, appTop_toSpecΓ_SpecMap]

lemma sectionOfHom_comp_iff (φ : A.sections.obj (op U) ⟶ Γ(Y, U.toOpens)) :
    sectionOfHom A U φ ≫ A.relSpecToBase = U.toOpens.ι ↔ A.structureMap.app (op U) ≫ φ = 𝟙 _ := by
  refine (?_ : _ ↔ Spec.map (A.structureMap.app (op U) ≫ φ) = 𝟙 _).trans ?_
  · rw [sectionOfHom, Category.assoc, Category.assoc, A.ι_relSpecToBase, ← Spec.map_comp_assoc,
      ← U.2.isoSpec_hom_fromSpec, ← U.2.isoSpec_hom, cancel_epi]
    nth_rw 2 [← Category.id_comp U.2.fromSpec]
    exact cancel_mono _
  · rw [← Spec.map_id]
    exact Spec.map_injective.eq_iff

/-- **Sections of a relative spectrum over an affine open** (supplements Hartshorne II, Exercise
5.17): for a quasi-coherent `𝒪_Y`-algebra `A` and an affine open `U ⊆ Y`, the sections of
`Spec_Y A ⟶ Y` over `U` correspond to the `𝒪_Y(U)`-algebra maps `A(U) ⟶ 𝒪_Y(U)`. -/
def equiv : (sectionsPresheaf A.relSpecToBase).obj (op U.toOpens) ≃
    {φ : A.sections.obj (op U) ⟶ Γ(Y, U.toOpens) // A.structureMap.app (op U) ≫ φ = 𝟙 _} where
  toFun s := ⟨homOfSection A U s.1 s.2, (sectionOfHom_comp_iff A U _).mp (by
    rw [sectionOfHom_homOfSection]; exact s.2)⟩
  invFun φ := ⟨sectionOfHom A U φ.1, (sectionOfHom_comp_iff A U _).mpr φ.2⟩
  left_inv s := Subtype.ext (sectionOfHom_homOfSection A U s.1 s.2)
  right_inv φ := Subtype.ext
    (homOfSection_sectionOfHom A U φ.1 ((sectionOfHom_comp_iff A U _).mpr φ.2))

lemma equiv_apply_coe (s : (sectionsPresheaf A.relSpecToBase).obj (op U.toOpens)) :
    (equiv A U s).1 = homOfSection A U s.1 s.2 := by
  rfl

/-- The correspondence `equiv` is natural: restricting a section from `V` to an affine `U ⊆ V`
corresponds to composing with the restriction maps of `A` and of `𝒪_Y`. -/
lemma restriction_equiv {U V : Y.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens)
    (s : (sectionsPresheaf A.relSpecToBase).obj (op V.toOpens)) :
    A.restriction h ≫ (equiv A U ((sectionsPresheaf A.relSpecToBase).map (homOfLE h).op s)).1 =
      (equiv A V s).1 ≫ Y.presheaf.map (homOfLE h).op := by
  set s' := (sectionsPresheaf A.relSpecToBase).map (homOfLE h).op s
  have h1 := sectionOfHom_homOfSection A U s'.1 s'.2
  have h2 := sectionOfHom_homOfSection A V s.1 s.2
  simp only [sectionOfHom] at h1 h2
  rw [equiv_apply_coe, equiv_apply_coe]
  have : IsIso U.toOpens.toSpecΓ := by rw [← IsAffineOpen.isoSpec_hom U.2]; infer_instance
  apply Spec.map_injective
  rw [← cancel_epi U.toOpens.toSpecΓ, ← cancel_mono (A.ι V), Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [A.SpecMap_restriction_ι, h1, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, h2]
  rfl

end RelSpecSections

/-! ### Sections of `V(E)` and the dual `E^∨` -/

namespace Scheme.Modules

open Hartshorne Hartshorne.Ringed Hartshorne.ModuleSheafAlgebra

variable {E : Y.Modules} {n : ℕ} (hE : E.IsLocallyFreeOfRank n)

/-- The `𝒪_Y(V)`-algebra map `Γ(V, Sym(E)) ⟶ Γ(V, 𝒪_Y)` of a section `s` of `V(E) ⟶ Y` over an
affine open `V`. -/
def sectionAlgHom (V : Y.affineOpens)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (V : Y.Opens))) :
    E.symSections V ⟶ Γ(Y, V) :=
  (RelSpecSections.equiv (symmetricQuasiCoherentAlgebra E hE) (affineSite V) s).1

lemma sectionAlgHom_unitRingHom (V : Y.affineOpens)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (V : Y.Opens))) (r : Γ(Y, V)) :
    sectionAlgHom hE V s (unitRingHom _ (V : Y.Opens) r) = r :=
  ConcreteCategory.congr_hom
    (RelSpecSections.equiv (symmetricQuasiCoherentAlgebra E hE) (affineSite V) s).2 r

/-- **The linear form `E(V) ⟶ 𝒪_Y(V)` of a section** `s` of `V(E) ⟶ Y` over an affine open `V`:
the algebra map `Γ(V, Sym(E)) ⟶ Γ(V, 𝒪_Y)` of `s` on the degree-one sections. -/
def sectionLinearForm (V : Y.affineOpens)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (V : Y.Opens))) :
    Γ(E, V) →ₗ[Γ(Y, V)] Γ(Y, V) where
  toFun x := sectionAlgHom hE V s (E.symDegreeOne V x)
  map_add' x y := by rw [symDegreeOne_add, map_add]
  map_smul' r x := by
    rw [symDegreeOne_smul, map_mul, sectionAlgHom_unitRingHom]
    rfl

lemma sectionLinearForm_apply (V : Y.affineOpens)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (V : Y.Opens))) (x : Γ(E, V)) :
    sectionLinearForm hE V s x = sectionAlgHom hE V s (E.symDegreeOne V x) := rfl

/-- The linear forms of sections are compatible with restriction between affine opens. -/
lemma sectionLinearForm_naturality {V V' : Y.affineOpens} (h : (V' : Y.Opens) ≤ V)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (V : Y.Opens))) (x : Γ(E, V)) :
    sectionLinearForm hE V' ((sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE h).op s)
        (E.presheaf.map (homOfLE h).op x) =
      Y.presheaf.map (homOfLE h).op (sectionLinearForm hE V s x) := by
  rw [sectionLinearForm_apply, sectionLinearForm_apply, ← symDegreeOne_naturality,
    ← symmetricQuasiCoherentAlgebra_restriction hE (U := affineSite V') (V := affineSite V) h]
  exact ConcreteCategory.congr_hom
    (RelSpecSections.restriction_equiv (symmetricQuasiCoherentAlgebra E hE) h s) _

/-- The section of the dual `E^∨ = ℋom(E, 𝒪_Y)` over a framed affine open `V` corresponding to a
section `s` of `V(E) ⟶ Y` over `V`: the morphism `E|_V ⟶ 𝒪_V` taking the frame vectors `e_k` to
the values of the linear form of `s`. -/
def sectionDual (c : AffineFrame E n)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (c.V : Y.Opens))) :
    Γ(moduleSheafDual (R := Y.sheaf) E, c.V) :=
  c.isLocalFrame.homOfValues (G := structureModule Y.sheaf) le_rfl
    (fun k => sectionLinearForm hE c.V s (c.e k))

/-- On every affine open `V' ⊆ V`, the morphism `sectionDual c s : E|_V ⟶ 𝒪_V` is the linear form
of the restriction of `s` to `V'`. -/
lemma sectionDual_eval (c : AffineFrame E n)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (c.V : Y.Opens)))
    {V' : Y.affineOpens} (h : (V' : Y.Opens) ≤ c.V) (x : Γ(E, V')) :
    moduleSheafHomEval (sectionDual hE c s) h x =
      sectionLinearForm hE V' ((sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE h).op s)
        x := by
  rw [sectionDual, IsLocalFrame.homOfValues_eval]
  conv_rhs => rw [← c.isLocalFrame.localFrameMap_coord (h.trans le_rfl) x, localFrameMap_apply,
    map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul]
  exact congrArg (_ • ·) (sectionLinearForm_naturality hE h s (c.e k)).symm

lemma localFrameEval_sectionDual (c : AffineFrame E n)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (c.V : Y.Opens))) :
    localFrameEval c.e le_rfl (sectionDual hE c s) =
      fun k => sectionLinearForm hE c.V s (c.e k) :=
  c.isLocalFrame.localFrameEval_homOfValues le_rfl _

/-- `sectionDual` is compatible with restriction between framed affine opens. -/
lemma sectionDual_naturality {c c' : AffineFrame E n} (h : (c'.V : Y.Opens) ≤ c.V)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (c.V : Y.Opens))) :
    (moduleSheafDual (R := Y.sheaf) E).val.presheaf.map (homOfLE h).op (sectionDual hE c s) =
      sectionDual hE c' ((sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE h).op s) := by
  refine c'.isLocalFrame.hom_ext le_rfl ?_
  rw [localFrameEval_sectionDual]
  funext k
  rw [localFrameEval_apply, moduleSheafHomEval_restrict, sectionDual_eval]
  refine congrArg (sectionLinearForm hE c'.V _) ?_
  change E.val.presheaf.map (𝟙 _) (c'.e k) = c'.e k
  simp

/-- Over an affine open `V` on which `E` has a frame `e`, an `𝒪_Y(V)`-algebra map
`Γ(V, Sym(E)) ⟶ Γ(V, 𝒪_Y)` is determined by its values on the frame vectors, which can be
arbitrary: `Γ(V, Sym(E))` is the polynomial ring on `e`. -/
private lemma algHom_values_bijective (V : Y.affineOpens) {e : ULift.{u} (Fin n) → Γ(E, V)}
    (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e) :
    Function.Bijective (fun (φ : {φ : (symmetricQuasiCoherentAlgebra E hE).sections.obj
        (op (affineSite V)) ⟶ Γ(Y, V) // (symmetricQuasiCoherentAlgebra E hE).structureMap.app
          (op (affineSite V)) ≫ φ = 𝟙 _}) (k : ULift.{u} (Fin n)) =>
        φ.1 (E.symDegreeOne V (e k))) := by
  have hχ := E.chartRingHom_bijective V.2 he
  have hunit : ∀ (φ : {φ : (symmetricQuasiCoherentAlgebra E hE).sections.obj
      (op (affineSite V)) ⟶ Γ(Y, V) // (symmetricQuasiCoherentAlgebra E hE).structureMap.app
        (op (affineSite V)) ≫ φ = 𝟙 _}) (r : Γ(Y, V)),
      φ.1 (unitRingHom _ (V : Y.Opens) r) = r := fun φ r => ConcreteCategory.congr_hom φ.2 r
  refine ⟨fun φ φ' hφ => Subtype.ext ?_, fun g => ?_⟩
  · have : φ.1.hom.comp (E.chartRingHom V e) = φ'.1.hom.comp (E.chartRingHom V e) :=
      MvPolynomial.ringHom_ext (fun r =>
          (congrArg φ.1.hom (chartRingHom_C E _ e r)).trans (((hunit φ r).trans
            (hunit φ' r).symm).trans (congrArg φ'.1.hom (chartRingHom_C E _ e r)).symm))
        (fun k => (congrArg φ.1.hom (chartRingHom_X E _ e k)).trans ((congrFun hφ k).trans
            (congrArg φ'.1.hom (chartRingHom_X E _ e k)).symm))
    ext y
    obtain ⟨p, rfl⟩ := hχ.2 y
    exact RingHom.congr_fun this p
  · let χ := RingEquiv.ofBijective (E.chartRingHom V e) hχ
    refine ⟨⟨CommRingCat.ofHom ((MvPolynomial.eval₂Hom (RingHom.id _) g).comp
      χ.symm.toRingHom), ?_⟩, ?_⟩
    · ext r
      change MvPolynomial.eval₂Hom (RingHom.id _) g (χ.symm (unitRingHom _ (V : Y.Opens) r)) = r
      rw [← chartRingHom_C E (V : Y.Opens) e r]
      change MvPolynomial.eval₂Hom (RingHom.id _) g (χ.symm (χ (MvPolynomial.C r))) = r
      rw [RingEquiv.symm_apply_apply, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
    · funext k
      change MvPolynomial.eval₂Hom (RingHom.id _) g (χ.symm (E.symDegreeOne V (e k))) = g k
      rw [← chartRingHom_X E (V : Y.Opens) e k]
      change MvPolynomial.eval₂Hom (RingHom.id _) g (χ.symm (χ (MvPolynomial.X k))) = g k
      rw [RingEquiv.symm_apply_apply, MvPolynomial.eval₂Hom_X']

/-- Over a framed affine open, `s ↦ sectionDual c s` is a bijection from the sections of `V(E)`
onto the sections of `E^∨`. -/
lemma sectionDual_bijective (c : AffineFrame E n) : Function.Bijective (sectionDual hE c) := by
  have hhv : Function.Bijective
      (c.isLocalFrame.homOfValues (G := structureModule Y.sheaf) le_rfl) := by
    refine ⟨fun g g' hg => ?_, fun ψ => ⟨localFrameEval c.e le_rfl ψ,
      c.isLocalFrame.hom_ext le_rfl ?_⟩⟩
    · rw [← c.isLocalFrame.localFrameEval_homOfValues le_rfl g, hg,
        IsLocalFrame.localFrameEval_homOfValues]
    · rw [IsLocalFrame.localFrameEval_homOfValues]
  exact hhv.comp ((algHom_values_bijective hE c.V c.isLocalFrame).comp
    (RelSpecSections.equiv (symmetricQuasiCoherentAlgebra E hE) (affineSite c.V)).bijective)

/-- The framed affine opens form a basis of `Y`. -/
lemma isBasis_affineFrame (hE : E.IsLocallyFreeOfRank n) :
    Opens.IsBasis (Set.range fun c : AffineFrame E n => (c.V : Y.Opens)) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {W y} hy => ?_
  obtain ⟨c, hc⟩ := exists_affineFrame hE y
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (u := ((c.V : Y.Opens) ⊓ W : Y.Opens))
      ⟨hc, hy⟩ ((c.V : Y.Opens) ⊓ W).isOpen
  exact ⟨V, ⟨⟨⟨V, hV⟩, _, c.isLocalFrame.restrictLE fun x hx => (hVW hx).1⟩, rfl⟩, hyV,
    fun x hx => (hVW hx).2⟩

variable (E) in
/-- The dual `E^∨ = ℋom(E, 𝒪_Y)` as a sheaf of sets. -/
def dualTypeSheaf : TopCat.Sheaf (Type u) Y :=
  ⟨(moduleSheafDual (R := Y.sheaf) E).val.presheaf ⋙ CategoryTheory.forget _,
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ (moduleSheafDual (R := Y.sheaf) E).isSheaf⟩

/-- The map from sections of `V(E)` to sections of `E^∨`, on the basis of framed affine opens. -/
def sectionDualBasis :
    (inducedFunctor fun c : AffineFrame E n => (c.V : Y.Opens)).op ⋙
        sectionsPresheaf (vectorBundleProj E hE) ⟶
      (inducedFunctor fun c : AffineFrame E n => (c.V : Y.Opens)).op ⋙ (dualTypeSheaf E).1 where
  app c := TypeCat.ofHom (sectionDual hE c.unop)
  naturality c d f := by
    ext s
    exact (sectionDual_naturality hE (leOfHom f.unop.hom) s).symm

/-- The map `𝒮(V(E)/Y) ⟶ E^∨` of presheaves of sets on `Y`: the extension of `sectionDualBasis` from
the basis of framed affine opens. -/
def sectionsToDual : sectionsPresheaf (vectorBundleProj E hE) ⟶ (dualTypeSheaf E).1 :=
  TopCat.Sheaf.restrictHomEquivHom _ (dualTypeSheaf E) (isBasis_affineFrame hE)
    (sectionDualBasis hE)

lemma sectionsToDual_app (c : AffineFrame E n) :
    (sectionsToDual hE).app (op (c.V : Y.Opens)) = TypeCat.ofHom (sectionDual hE c) :=
  TopCat.Sheaf.extend_hom_app _ _ _ _ c

instance isIso_sectionsToDual : IsIso (sectionsToDual hE) := by
  let F : TopCat.Sheaf (Type u) Y :=
    ⟨sectionsPresheaf (vectorBundleProj E hE), isSheaf_sectionsPresheaf _⟩
  have : IsIso (ObjectProperty.homMk (sectionsToDual hE) : F ⟶ dualTypeSheaf E) :=
    TopCat.Sheaf.isIso_iff_isIso_basis (isBasis_affineFrame hE) fun c => by
      change IsIso ((sectionsToDual hE).app (op (c.V : Y.Opens)))
      rw [sectionsToDual_app, isIso_iff_bijective]
      exact sectionDual_bijective hE c
  exact inferInstanceAs (IsIso ((sheafToPresheaf _ _).map (ObjectProperty.homMk (sectionsToDual hE) :
    F ⟶ dualTypeSheaf E)))

/-- **The sections of `V(E)` are the dual `E^∨`** (Hartshorne II, Exercise 5.18(c)): for a locally
free sheaf `E` of rank `n` on `Y`, with Hartshorne's convention `V(E) = Spec_Y Sym(E)`, the sheaf
of sections `𝒮(V(E)/Y)` is naturally isomorphic to `E^∨ = ℋom(E, 𝒪_Y)` (as sheaves of sets on `Y`).
Over an affine open `V`, a section `s` corresponds to the `𝒪_Y(V)`-algebra map
`Γ(V, Sym(E)) ⟶ 𝒪_Y(V)` (`sectionAlgHom`), which is determined by its restriction to `E(V)`
(`vectorBundleSectionsIso_hom_eval`). -/
def vectorBundleSectionsIso :
    sectionsPresheaf (vectorBundleProj E hE) ≅
      (moduleSheafDual (R := Y.sheaf) E).val.presheaf ⋙ CategoryTheory.forget _ :=
  asIso (sectionsToDual hE)

/-- The isomorphism `vectorBundleSectionsIso` on framed affine opens. -/
private lemma vectorBundleSectionsIso_hom_eval_frame {W : Y.Opens}
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op W)) (c : AffineFrame E n)
    (h : (c.V : Y.Opens) ≤ W) (x : Γ(E, c.V)) :
    moduleSheafHomEval ((vectorBundleSectionsIso hE).hom.app (op W) s) h x =
      sectionLinearForm hE c.V ((sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE h).op s)
        x := by
  have hnat := ConcreteCategory.congr_hom ((sectionsToDual hE).naturality (homOfLE h).op) s
  change (sectionsToDual hE).app (op (c.V : Y.Opens)) _ =
    (moduleSheafDual (R := Y.sheaf) E).val.presheaf.map (homOfLE h).op
      ((sectionsToDual hE).app (op W) s) at hnat
  rw [sectionsToDual_app] at hnat
  change moduleSheafHomEval ((sectionsToDual hE).app (op W) s) ((le_refl _).trans h) x = _
  rw [← moduleSheafHomEval_restrict, ← hnat]
  change moduleSheafHomEval (sectionDual hE c _) (le_refl _) x = _
  rw [sectionDual_eval]
  congr 2
  change (sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE le_rfl).op
    ((sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE h).op s) = _
  rw [show (homOfLE (le_refl (c.V : Y.Opens))).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl
  exact h

/-- **The isomorphism `𝒮(V(E)/Y) ≅ E^∨` explicitly**: a section `s` of `V(E) ⟶ Y` over an open
`W` goes to the morphism `E|_W ⟶ 𝒪_W` whose value on `x ∈ E(V)`, for an affine open `V ⊆ W`, is
`φ(x)`, where `φ : Γ(V, Sym(E)) ⟶ 𝒪_Y(V)` is the `𝒪_Y(V)`-algebra map of the restriction of `s`
to `V`, and `x` is viewed in `Γ(V, Sym(E))` in degree one. -/
theorem vectorBundleSectionsIso_hom_eval {W : Y.Opens}
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op W)) {V : Y.affineOpens}
    (h : (V : Y.Opens) ≤ W) (x : Γ(E, V)) :
    moduleSheafHomEval ((vectorBundleSectionsIso hE).hom.app (op W) s) h x =
      sectionAlgHom hE V ((sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE h).op s)
        (E.symDegreeOne V x) := by
  have hB := isBasis_affineFrame hE
  have hc : ∀ y : (V : Y.Opens), ∃ c : AffineFrame E n, y.1 ∈ (c.V : Y.Opens) ∧
      (c.V : Y.Opens) ≤ V := fun y => by
    obtain ⟨_, ⟨c, rfl⟩, hy, hle⟩ := Opens.isBasis_iff_nbhd.mp hB y.2
    exact ⟨c, hy, hle⟩
  choose c hyc hcV using hc
  refine Y.sheaf.eq_of_locally_eq' (fun y => (c y).V) (V : Y.Opens) (fun y => homOfLE (hcV y))
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyc ⟨y, hy⟩⟩) _ _ fun y => ?_
  change (structureModule Y.sheaf).val.presheaf.map (homOfLE (hcV y)).op
    (moduleSheafHomEval _ h x) = Y.presheaf.map (homOfLE (hcV y)).op
      (sectionLinearForm hE V _ x)
  rw [← moduleSheafHomEval_natural, ← sectionLinearForm_naturality,
    vectorBundleSectionsIso_hom_eval_frame]
  congr 2
  change _ = (sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE (hcV y)).op
    ((sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE h).op s)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end Scheme.Modules

end

end AlgebraicGeometry
