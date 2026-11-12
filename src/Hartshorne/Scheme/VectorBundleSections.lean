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

## Chart coordinates and the module of sections

For a geometric vector bundle `G : GeometricVectorBundle f n` and an open `V ⊆ U_i`, a section `s`
over `V` has coordinates `GeometricVectorBundle.chartCoord i hi s hs ∈ Γ(V, 𝒪)ⁿ`, those of
`ψ_i ∘ s : V ⟶ 𝔸ⁿ_V`. They identify the sections over `V` with `Γ(V, 𝒪)ⁿ`
(`chartCoord_bijective`), are compatible with restriction (`chartCoord_restrict`), and on an affine
`V ⊆ U_i ∩ U_j` the coordinates in the two charts differ by a matrix over `Γ(V, 𝒪)`
(`exists_chartCoord_transition`, from the linearity of the transition automorphisms).

Hence the linear structure of the charts glues: `GeometricVectorBundle.sectionsModule G` is the
`𝒪_Y`-module whose sections over `W` are the sections of `f` over `W`, added and multiplied by
functions in the coordinates of the charts (`coordY_secAdd`, `coordY_secSmul`); it is locally
free of rank `n` (`sectionsModule_isLocallyFreeOfRank`), the chart `ψ_i` giving a frame over
`U_i` (`isLocalFrame_frameSection`). The operations are defined by gluing coordinates on the
affine opens inside the chart domains (`exists_coords_eq`), using the sheaf property of the
sections.

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
(`sectionDual_bijective`); the isomorphism is the extension from this basis of `Y`. The chart
coordinates of a section for the atlas `vectorBundleAtlas` are the values of its linear form on the
frame (`vectorBundleAtlas_chartCoord`), so the isomorphism is `𝒪_Y`-linear:
`Scheme.Modules.vectorBundleSectionsModuleIso` is the isomorphism of `𝒪_Y`-modules
`(vectorBundleAtlas hE).sectionsModule ≅ E^∨`.
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
  have hr : ∀ i, r i ≫ (Scheme.Opens.ι (X := Y) (U i)) = (V i).ι ≫ W.ι :=
    fun i => morphismRestrict_ι _ _
  have hVι : ∀ i, (V i).ι = r i ≫ Y.homOfLE (hle i) := fun i => by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, hr]
  have hcomp : ∀ i j, W.toScheme.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ r i ≫ (sf i).1 =
      W.toScheme.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ r j ≫ (sf j).1 := by
    intro i j
    have hm : Set.range ((V i ⊓ V j).ι ≫ W.ι) ⊆
        Set.range (Scheme.Opens.ι (X := Y) (U i ⊓ U j)) := by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨W.ι ((V i ⊓ V j).ι x), ?_⟩, rfl⟩
      exact ⟨(x.2 : _ ∈ V i ⊓ V j).1, (x.2 : _ ∈ V i ⊓ V j).2⟩
    let m := IsOpenImmersion.lift (Scheme.Opens.ι (X := Y) (U i ⊓ U j)) ((V i ⊓ V j).ι ≫ W.ι) hm
    have hm' : (V i ⊓ V j).ι ≫ W.ι = m ≫ (Scheme.Opens.ι (X := Y) (U i ⊓ U j)) :=
      (IsOpenImmersion.lift_fac _ _ _).symm
    have hi : W.toScheme.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ r i =
        m ≫ Y.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := by
      rw [← cancel_mono (Scheme.Opens.ι (X := Y) (U i)), Category.assoc, hr, Category.assoc,
        Scheme.homOfLE_ι_assoc,
        Scheme.homOfLE_ι, hm']
    have hj : W.toScheme.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ r j =
        m ≫ Y.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := by
      rw [← cancel_mono (Scheme.Opens.ι (X := Y) (U j)), Category.assoc, hr, Category.assoc,
        Scheme.homOfLE_ι_assoc,
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

/-! ### Chart coordinates of sections of a geometric vector bundle -/

namespace GeometricVectorBundle

variable {f : X ⟶ Y} {n : ℕ} (G : GeometricVectorBundle f n)

private lemma range_subset_preimage {i : G.ι} {V : Y.Opens} (hi : V ≤ G.U i)
    (s : V.toScheme ⟶ X) (hs : s ≫ f = V.ι) :
    Set.range s ⊆ Set.range (f ⁻¹ᵁ G.U i).ι := by
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨s x, ?_⟩, rfl⟩
  change (s ≫ f) x ∈ G.U i
  rw [hs]
  exact hi x.2

/-- The restriction `V ⟶ f⁻¹(U_i)` of a section `s` of `f` over an open `V ⊆ U_i`. -/
private def toPreimage {i : G.ι} {V : Y.Opens} (hi : V ≤ G.U i) (s : V.toScheme ⟶ X)
    (hs : s ≫ f = V.ι) : V.toScheme ⟶ (f ⁻¹ᵁ G.U i).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ G.U i).ι s (range_subset_preimage G hi s hs)

private lemma toPreimage_over {i : G.ι} {V : Y.Opens} (hi : V ≤ G.U i) (s : V.toScheme ⟶ X)
    (hs : s ≫ f = V.ι) :
    (toPreimage G hi s hs ≫ (G.ψ i).hom) ≫ 𝔸(ULift.{u} (Fin n); G.U i) ↘ G.U i =
      𝟙 _ ≫ Y.homOfLE hi := by
  rw [Category.assoc, G.ψ_over, Category.id_comp, ← cancel_mono (G.U i).ι, Category.assoc,
    morphismRestrict_ι, toPreimage, IsOpenImmersion.lift_fac_assoc, hs, Scheme.homOfLE_ι]

/-- **A section in the chart `ψ_i`**: for a section `s` of `f` over an open `V ⊆ U_i`, the
morphism `V ⟶ 𝔸ⁿ_V` over `V` corresponding to `ψ_i ∘ s : V ⟶ 𝔸ⁿ_{U_i}`. -/
def chartLift (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) (s : V.toScheme ⟶ X)
    (hs : s ≫ f = V.ι) : V.toScheme ⟶ 𝔸(ULift.{u} (Fin n); V) :=
  (AffineSpace.isPullback_map (Y.homOfLE hi)).lift _ _ (toPreimage_over G hi s hs)

lemma chartLift_over (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) (s : V.toScheme ⟶ X)
    (hs : s ≫ f = V.ι) : G.chartLift i hi s hs ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V = 𝟙 _ :=
  IsPullback.lift_snd _ _ _ _

lemma chartLift_map (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) (s : V.toScheme ⟶ X)
    (hs : s ≫ f = V.ι) :
    G.chartLift i hi s hs ≫ AffineSpace.map _ (Y.homOfLE hi) ≫ (G.ψ i).inv ≫
      (f ⁻¹ᵁ G.U i).ι = s := by
  rw [← Category.assoc, chartLift, IsPullback.lift_fst, Category.assoc, Iso.hom_inv_id_assoc,
    toPreimage, IsOpenImmersion.lift_fac]

/-- **The chart coordinates** `(s_1, …, s_n) ∈ Γ(V, 𝒪)ⁿ` of a section `s` of a geometric vector
bundle over an open `V ⊆ U_i`: the coordinates of `ψ_i ∘ s : V ⟶ 𝔸ⁿ_V`. -/
def chartCoord (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) (s : V.toScheme ⟶ X)
    (hs : s ≫ f = V.ι) (k : ULift.{u} (Fin n)) : Γ(V, ⊤) :=
  (G.chartLift i hi s hs).appTop (AffineSpace.coord _ k)

instance mono_affineSpace_map_homOfLE {V U : Y.Opens} (h : V ≤ U) :
    Mono (AffineSpace.map (ULift.{u} (Fin n)) (Y.homOfLE h)) := by
  refine ⟨fun a b hab => (AffineSpace.isPullback_map (Y.homOfLE h)).hom_ext hab ?_⟩
  rw [← cancel_mono (Y.homOfLE h), Category.assoc, Category.assoc, ← AffineSpace.map_over,
    reassoc_of% hab]

/-- The chart coordinates over an affine open `V ⊆ U_i` through the polynomial-ring chart
`V ⟶ 𝔸ⁿ_V ≅ Spec Γ(V, 𝒪)[x_1, …, x_n]`: the pullback of the variable `x_k`. -/
private lemma chartCoord_eq (i : G.ι) (V : Y.affineOpens) (hi : (V : Y.Opens) ≤ G.U i)
    (s : (V : Y.Opens).toScheme ⟶ X) (hs : s ≫ f = (V : Y.Opens).ι) (k : ULift.{u} (Fin n)) :
    G.chartCoord i hi s hs k = (G.chartLift i hi s hs ≫
      (AffineSpace.isoOfIsAffine (ULift.{u} (Fin n)) (V : Y.Opens).toScheme).hom).appTop
        ((Scheme.ΓSpecIso _).inv (MvPolynomial.X k)) := by
  rw [← AffineSpace.isoOfIsAffine_inv_appTop_coord, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- A section in a polynomial-ring chart is a section of `Spec A[x_1, …, x_n] ⟶ Spec A`: it fixes
the constants. -/
private lemma chartLift_appTop_C (i : G.ι) (V : Y.affineOpens) (hi : (V : Y.Opens) ≤ G.U i)
    (s : (V : Y.Opens).toScheme ⟶ X) (hs : s ≫ f = (V : Y.Opens).ι) (r : Γ(V, ⊤)) :
    (G.chartLift i hi s hs ≫
      (AffineSpace.isoOfIsAffine (ULift.{u} (Fin n)) (V : Y.Opens).toScheme).hom).appTop
        ((Scheme.ΓSpecIso _).inv (MvPolynomial.C r)) = r := by
  have h : (G.chartLift i hi s hs ≫
      (AffineSpace.isoOfIsAffine (ULift.{u} (Fin n)) (V : Y.Opens).toScheme).hom) ≫
        Spec.map (CommRingCat.ofHom MvPolynomial.C) = (V : Y.Opens).toScheme.isoSpec.hom := by
    rw [← cancel_mono (V : Y.Opens).toScheme.isoSpec.inv, Category.assoc, Category.assoc,
      ← AffineSpace.isoOfIsAffine_inv_over, Iso.hom_inv_id_assoc, chartLift_over, Iso.hom_inv_id]
  have h' := congrArg (fun g => g.appTop ((Scheme.ΓSpecIso _).inv r)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h'
  rw [← CommRingCat.comp_apply _ (Spec.map _).appTop, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop] at h'
  exact h'.trans (Iso.inv_hom_id_apply _ _)

/-- **Linear transitions of chart coordinates** (Hartshorne II, Exercise 5.18): for charts
`i, j` and an affine open `V ⊆ U_i ∩ U_j`, there is a matrix `(a_{kl})` over `Γ(V, 𝒪)` with
`s^{(i)}_k = ∑_l a_{kl} s^{(j)}_l` for the chart coordinates of every section `s` over `V`. -/
theorem exists_chartCoord_transition (i j : G.ι) (V : Y.affineOpens) (hi : (V : Y.Opens) ≤ G.U i)
    (hj : (V : Y.Opens) ≤ G.U j) :
    ∃ a : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) Γ(V, ⊤),
      ∀ (s : (V : Y.Opens).toScheme ⟶ X) (hs : s ≫ f = (V : Y.Opens).ι) (k : ULift.{u} (Fin n)),
        G.chartCoord i hi s hs k = ∑ l, a k l * G.chartCoord j hj s hs l := by
  obtain ⟨θ, ⟨a, ha⟩, hθ⟩ := G.linear i j V hi hj
  refine ⟨a, fun s hs k => ?_⟩
  set e := AffineSpace.isoOfIsAffine (ULift.{u} (Fin n)) (V : Y.Opens).toScheme
  have ht : ∀ (i' : G.ι) (hi' : (V : Y.Opens) ≤ G.U i'), (G.chartLift i' hi' s hs ≫ e.hom) ≫
      affineSpaceChart n V hi' ≫ (G.ψ i').inv ≫ (f ⁻¹ᵁ G.U i').ι = s := fun i' hi' => by
    simp only [affineSpaceChart, Category.assoc, e, Iso.hom_inv_id_assoc]
    exact G.chartLift_map i' hi' s hs
  have hmono : Mono (affineSpaceChart n V hi ≫ (G.ψ i).inv ≫ (f ⁻¹ᵁ G.U i).ι) := by
    unfold affineSpaceChart
    infer_instance
  have htij : G.chartLift i hi s hs ≫ e.hom = (G.chartLift j hj s hs ≫ e.hom) ≫
      Spec.map (CommRingCat.ofHom θ.toRingEquiv.toRingHom) := by
    rw [← cancel_mono (affineSpaceChart n V hi ≫ (G.ψ i).inv ≫ (f ⁻¹ᵁ G.U i).ι), ht,
      Category.assoc, ← hθ, ht]
  let φ : MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) →+* Γ(V, ⊤) :=
    ((Scheme.ΓSpecIso _).inv ≫ (G.chartLift j hj s hs ≫ e.hom).appTop).hom
  have hφ : ∀ x, φ x = (G.chartLift j hj s hs ≫ e.hom).appTop ((Scheme.ΓSpecIso _).inv x) :=
    fun _ => rfl
  rw [chartCoord_eq, htij, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply _ (Spec.map _).appTop, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, ← hφ]
  change φ (θ.toAlgHom (MvPolynomial.X k)) = _
  rw [ha k, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, hφ, hφ, chartLift_appTop_C, chartCoord_eq]

/-- **The chart coordinates identify sections with `Γ(V, 𝒪)ⁿ`** (Hartshorne II, Exercise 5.18):
over an open `V ⊆ U_i`, a section of a geometric vector bundle of rank `n` is the same as `n`
functions on `V`, its coordinates in the chart `ψ_i`. -/
theorem chartCoord_bijective (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) :
    Function.Bijective (fun s : (sectionsPresheaf f).obj (op V) => G.chartCoord i hi s.1 s.2) := by
  have hmono : Mono ((G.ψ i).inv ≫ (f ⁻¹ᵁ G.U i).ι) := inferInstance
  refine ⟨fun s s' hss' => Subtype.ext ?_, fun v => ?_⟩
  · have hL : G.chartLift i hi s.1 s.2 = G.chartLift i hi s'.1 s'.2 :=
      AffineSpace.hom_ext (by rw [chartLift_over, chartLift_over]) (congrFun hss')
    rw [← G.chartLift_map i hi s.1 s.2, hL, G.chartLift_map]
  · let w : V.toScheme ⟶ 𝔸(ULift.{u} (Fin n); V) := AffineSpace.homOfVector (𝟙 _) v
    have hψ : (G.ψ i).inv ≫ (f ⁻¹ᵁ G.U i).ι ≫ f =
        𝔸(ULift.{u} (Fin n); G.U i) ↘ G.U i ≫ (G.U i).ι := by
      rw [← morphismRestrict_ι, ← G.ψ_over, Category.assoc, Iso.inv_hom_id_assoc]
    have hs : (w ≫ AffineSpace.map _ (Y.homOfLE hi) ≫ (G.ψ i).inv ≫ (f ⁻¹ᵁ G.U i).ι) ≫ f =
        V.ι := by
      simp only [Category.assoc]
      rw [hψ, AffineSpace.map_over_assoc, AffineSpace.homOfVector_over_assoc, Category.id_comp,
        Scheme.homOfLE_ι]
    refine ⟨⟨_, hs⟩, ?_⟩
    have hL : G.chartLift i hi _ hs = w := by
      refine (AffineSpace.isPullback_map (Y.homOfLE hi)).hom_ext ?_ ?_
      · rw [← cancel_mono ((G.ψ i).inv ≫ (f ⁻¹ᵁ G.U i).ι), Category.assoc, G.chartLift_map,
          Category.assoc]
      · rw [chartLift_over, AffineSpace.homOfVector_over]
    funext k
    change (G.chartLift i hi _ hs).appTop _ = v k
    rw [hL, AffineSpace.homOfVector_appTop_coord]

/-- **Chart coordinates are compatible with restriction**: for opens `V' ⊆ V ⊆ U_i`, the chart
coordinates of the restriction `s|_{V'}` are the restrictions of the chart coordinates of `s`. -/
theorem chartCoord_restrict (i : G.ι) {V V' : Y.Opens} (hi : V ≤ G.U i) (h : V' ≤ V)
    (s : V.toScheme ⟶ X) (hs : s ≫ f = V.ι) (k : ULift.{u} (Fin n)) :
    G.chartCoord i (h.trans hi) (Y.homOfLE h ≫ s) (by rw [Category.assoc, hs, Scheme.homOfLE_ι])
        k = (Y.homOfLE h).appTop (G.chartCoord i hi s hs k) := by
  have hs' : (Y.homOfLE h ≫ s) ≫ f = V'.ι := by rw [Category.assoc, hs, Scheme.homOfLE_ι]
  have hL : G.chartLift i (h.trans hi) _ hs' ≫ AffineSpace.map _ (Y.homOfLE h) =
      Y.homOfLE h ≫ G.chartLift i hi s hs := by
    refine (AffineSpace.isPullback_map (Y.homOfLE hi)).hom_ext ?_ ?_
    · rw [← cancel_mono ((G.ψ i).inv ≫ (f ⁻¹ᵁ G.U i).ι), Category.assoc, Category.assoc,
        ← AffineSpace.map_comp_assoc, Scheme.homOfLE_homOfLE, G.chartLift_map]
      simp only [Category.assoc]
      rw [G.chartLift_map i hi s hs]
    · rw [Category.assoc, AffineSpace.map_over, reassoc_of% (G.chartLift_over i (h.trans hi) _ hs'),
        Category.assoc, G.chartLift_over, Category.comp_id]
  change (G.chartLift i (h.trans hi) _ hs').appTop _ = (Y.homOfLE h).appTop
    ((G.chartLift i hi s hs).appTop _)
  rw [← AffineSpace.map_appTop_coord (Y.homOfLE h), ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, hL, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-! ### The `𝒪_Y`-module of sections of a geometric vector bundle -/

/-- The chart coordinates as sections of `𝒪_Y` over `V`. -/
def coordY (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) (s : (sectionsPresheaf f).obj (op V))
    (k : ULift.{u} (Fin n)) : Γ(Y, V) :=
  V.topIso.hom (G.chartCoord i hi s.1 s.2 k)

lemma coordY_bijective (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) :
    Function.Bijective (G.coordY i hi) := by
  have he : Function.Bijective (fun (x : ULift.{u} (Fin n) → Γ(V, ⊤)) k => V.topIso.hom (x k)) :=
    ⟨fun x y h => funext fun k => (ConcreteCategory.bijective_of_isIso V.topIso.hom).1
      (congrFun h k), fun y => ⟨fun k => V.topIso.inv (y k), funext fun k =>
        Iso.inv_hom_id_apply _ _⟩⟩
  exact he.comp (G.chartCoord_bijective i hi)

lemma coordY_restrict (i : G.ι) {V V' : Y.Opens} (hi : V ≤ G.U i) (h : V' ≤ V)
    (s : (sectionsPresheaf f).obj (op V)) (k : ULift.{u} (Fin n)) :
    G.coordY i (h.trans hi) ((sectionsPresheaf f).map (homOfLE h).op s) k =
      Y.presheaf.map (homOfLE h).op (G.coordY i hi s k) := by
  rw [coordY, coordY]
  change V'.topIso.hom (G.chartCoord i (h.trans hi) (Y.homOfLE h ≫ s.1) _ k) = _
  rw [chartCoord_restrict, ← CommRingCat.comp_apply, Scheme.Modules.homOfLE_appTop_topIso_hom,
    CommRingCat.comp_apply]

lemma exists_coordY_transition (i j : G.ι) (V : Y.affineOpens) (hi : (V : Y.Opens) ≤ G.U i)
    (hj : (V : Y.Opens) ≤ G.U j) :
    ∃ a : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) Γ(Y, V),
      ∀ (s : (sectionsPresheaf f).obj (op (V : Y.Opens))) (k : ULift.{u} (Fin n)),
        G.coordY i hi s k = ∑ l, a k l * G.coordY j hj s l := by
  obtain ⟨a, ha⟩ := G.exists_chartCoord_transition i j V hi hj
  refine ⟨fun k l => (V : Y.Opens).topIso.hom (a k l), fun s k => ?_⟩
  rw [coordY, ha, map_sum]
  simp only [map_mul]
  rfl

/-- A choice of transition matrix for the chart coordinates on an affine `V ⊆ U_i ∩ U_j`. -/
def transMatrix (i j : G.ι) (V : Y.affineOpens) (hi : (V : Y.Opens) ≤ G.U i)
    (hj : (V : Y.Opens) ≤ G.U j) : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) Γ(Y, V) :=
  (G.exists_coordY_transition i j V hi hj).choose

lemma coordY_transMatrix (i j : G.ι) (V : Y.affineOpens) (hi : (V : Y.Opens) ≤ G.U i)
    (hj : (V : Y.Opens) ≤ G.U j) (s : (sectionsPresheaf f).obj (op (V : Y.Opens)))
    (k : ULift.{u} (Fin n)) :
    G.coordY i hi s k = ∑ l, G.transMatrix i j V hi hj k l * G.coordY j hj s l :=
  (G.exists_coordY_transition i j V hi hj).choose_spec s k

/-- An affine open `V ⊆ W` contained in the domain `U_i` of a chart. -/
structure ChartPiece (W : Y.Opens) where
  /-- The chart. -/
  i : G.ι
  /-- The affine open. -/
  V : Y.affineOpens
  hi : (V : Y.Opens) ≤ G.U i
  hW : (V : Y.Opens) ≤ W

/-- The chart pieces of `W` cover `W`. -/
lemma le_iSup_chartPiece (W : Y.Opens) : W ≤ ⨆ p : G.ChartPiece W, (p.V : Y.Opens) := by
  intro y hy
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (G.iSup_eq_top.ge (Set.mem_univ y))
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (u := (G.U i ⊓ W : Y.Opens))
      ⟨hi, hy⟩ (G.U i ⊓ W).isOpen
  exact Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV⟩, fun x hx => (hVW hx).1, fun x hx => (hVW hx).2⟩, hyV⟩

/-- The transfer `Γ(V_p, 𝒪)ⁿ ⟶ Γ(V_q, 𝒪)ⁿ` from the coordinates in the chart of `p` to those in the
chart of `q`, for chart pieces `V_q ⊆ V_p`: restrict, then change chart. -/
def transfer {W : Y.Opens} (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V)
    (x : ULift.{u} (Fin n) → Γ(Y, p.V)) (k : ULift.{u} (Fin n)) : Γ(Y, q.V) :=
  ∑ l, G.transMatrix q.i p.i q.V q.hi (h.trans p.hi) k l * Y.presheaf.map (homOfLE h).op (x l)

lemma coordY_restrict_transfer {W : Y.Opens} (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V)
    (s : (sectionsPresheaf f).obj (op (p.V : Y.Opens))) :
    G.coordY q.i q.hi ((sectionsPresheaf f).map (homOfLE h).op s) =
      G.transfer p q h (G.coordY p.i p.hi s) := by
  funext k
  rw [coordY_transMatrix G q.i p.i q.V q.hi (h.trans p.hi), transfer]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coordY_restrict]

lemma transfer_add {W : Y.Opens} (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V)
    (x y : ULift.{u} (Fin n) → Γ(Y, p.V)) :
    G.transfer p q h (x + y) = G.transfer p q h x + G.transfer p q h y := by
  funext k
  simp only [transfer, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

lemma transfer_smul {W : Y.Opens} (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V)
    (r : Γ(Y, p.V)) (x : ULift.{u} (Fin n) → Γ(Y, p.V)) :
    G.transfer p q h (r • x) = Y.presheaf.map (homOfLE h).op r • G.transfer p q h x := by
  funext k
  simp only [transfer, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The coordinates `Φ(s)` of a section `s` over `W` in all its chart pieces. -/
def coords {W : Y.Opens} (s : (sectionsPresheaf f).obj (op W)) (p : G.ChartPiece W) :
    ULift.{u} (Fin n) → Γ(Y, p.V) :=
  G.coordY p.i p.hi ((sectionsPresheaf f).map (homOfLE p.hW).op s)

lemma coords_transfer {W : Y.Opens} (s : (sectionsPresheaf f).obj (op W)) (p q : G.ChartPiece W)
    (h : (q.V : Y.Opens) ≤ p.V) : G.transfer p q h (G.coords s p) = G.coords s q := by
  rw [coords, coords, ← coordY_restrict_transfer, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

private abbrev sheafOfSections : TopCat.Sheaf (Type u) Y :=
  ⟨sectionsPresheaf f, isSheaf_sectionsPresheaf f⟩

lemma coords_injective (W : Y.Opens) : Function.Injective (G.coords (W := W)) := by
  intro s t hst
  refine (sheafOfSections (f := f)).eq_of_locally_eq' (fun p : G.ChartPiece W => (p.V : Y.Opens))
    W (fun p => homOfLE p.hW) (G.le_iSup_chartPiece W) s t fun p => ?_
  exact (G.coordY_bijective p.i p.hi).1 (congrFun hst p)

/-- **Gluing coordinates**: a family of coordinates on the chart pieces of `W` that is compatible
with the transfers comes from a section over `W`. -/
lemma exists_coords_eq {W : Y.Opens} (x : ∀ p : G.ChartPiece W, ULift.{u} (Fin n) → Γ(Y, p.V))
    (hx : ∀ (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V), G.transfer p q h (x p) = x q) :
    ∃ s : (sectionsPresheaf f).obj (op W), G.coords s = x := by
  choose u hu using fun p : G.ChartPiece W => (G.coordY_bijective p.i p.hi).2 (x p)
  have hcomp : TopCat.Presheaf.IsCompatible (sectionsPresheaf f)
      (fun p : G.ChartPiece W => (p.V : Y.Opens)) u := by
    intro p p'
    refine (sheafOfSections (f := f)).eq_of_locally_eq'
      (fun q : G.ChartPiece ((p.V : Y.Opens) ⊓ p'.V) => (q.V : Y.Opens)) _
      (fun q => homOfLE q.hW) (G.le_iSup_chartPiece _) _ _ fun q => ?_
    let q' : G.ChartPiece W := ⟨p.i, q.V, q.hW.trans (inf_le_left.trans p.hi),
      q.hW.trans (inf_le_left.trans p.hW)⟩
    have h1 : (q.V : Y.Opens) ≤ p.V := q.hW.trans inf_le_left
    have h2 : (q.V : Y.Opens) ≤ p'.V := q.hW.trans inf_le_right
    apply (G.coordY_bijective q'.i q'.hi).1
    change G.coordY q'.i q'.hi ((sectionsPresheaf f).map (homOfLE q.hW).op
      ((sectionsPresheaf f).map (homOfLE inf_le_left).op (u p))) =
      G.coordY q'.i q'.hi ((sectionsPresheaf f).map (homOfLE q.hW).op
      ((sectionsPresheaf f).map (homOfLE inf_le_right).op (u p')))
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    change G.coordY q'.i q'.hi ((sectionsPresheaf f).map (homOfLE h1).op (u p)) =
      G.coordY q'.i q'.hi ((sectionsPresheaf f).map (homOfLE h2).op (u p'))
    rw [G.coordY_restrict_transfer p q' h1, G.coordY_restrict_transfer p' q' h2, hu, hu, hx, hx]
  obtain ⟨s, hs, -⟩ := (sheafOfSections (f := f)).existsUnique_gluing'
    (fun p : G.ChartPiece W => (p.V : Y.Opens)) W (fun p => homOfLE p.hW)
    (G.le_iSup_chartPiece W) u hcomp
  refine ⟨s, funext fun p => ?_⟩
  rw [coords]
  change G.coordY p.i p.hi ((sectionsPresheaf f).map (homOfLE p.hW).op s) = x p
  rw [show (sectionsPresheaf f).map (homOfLE p.hW).op s = u p from hs p, hu]

/-- `transfer` as an additive map. -/
def transferHom {W : Y.Opens} (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V) :
    (ULift.{u} (Fin n) → Γ(Y, p.V)) →+ (ULift.{u} (Fin n) → Γ(Y, q.V)) :=
  AddMonoidHom.mk' (G.transfer p q h) (G.transfer_add p q h)

lemma transferHom_apply {W : Y.Opens} (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V)
    (x : ULift.{u} (Fin n) → Γ(Y, p.V)) : G.transferHom p q h x = G.transfer p q h x := rfl

/-- The restriction `Γ(Y, W) ⟶ Γ(Y, V_p)` to a chart piece. -/
abbrev resPiece {W : Y.Opens} (p : G.ChartPiece W) (r : Γ(Y, W)) : Γ(Y, p.V) :=
  Y.presheaf.map (homOfLE p.hW).op r

lemma map_resPiece {W : Y.Opens} (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V)
    (r : Γ(Y, W)) : Y.presheaf.map (homOfLE h).op (G.resPiece p r) = G.resPiece q r := by
  rw [resPiece, resPiece, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {W : Y.Opens}

private lemma compat_secAdd (s t : (sectionsPresheaf f).obj (op W)) :
    ∀ (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V),
      G.transfer p q h ((G.coords s + G.coords t) p) = (G.coords s + G.coords t) q :=
  fun p q h => by
    rw [Pi.add_apply, transfer_add, coords_transfer, coords_transfer]; rfl

/-- The sum of two sections, in coordinates. -/
def secAdd (s t : (sectionsPresheaf f).obj (op W)) : (sectionsPresheaf f).obj (op W) :=
  (G.exists_coords_eq (G.coords s + G.coords t) (G.compat_secAdd s t)).choose

lemma coords_secAdd (s t : (sectionsPresheaf f).obj (op W)) :
    G.coords (G.secAdd s t) = G.coords s + G.coords t :=
  (G.exists_coords_eq _ (G.compat_secAdd s t)).choose_spec

private lemma compat_secZero (W : Y.Opens) :
    ∀ (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V),
      G.transfer p q h ((0 : ∀ p : G.ChartPiece W, ULift.{u} (Fin n) → Γ(Y, p.V)) p) =
        (0 : ∀ p : G.ChartPiece W, ULift.{u} (Fin n) → Γ(Y, p.V)) q :=
  fun p q h => by
    rw [← transferHom_apply]; exact map_zero _

/-- The zero section, in coordinates. -/
def secZero (W : Y.Opens) : (sectionsPresheaf f).obj (op W) :=
  (G.exists_coords_eq (0 : ∀ p : G.ChartPiece W, ULift.{u} (Fin n) → Γ(Y, p.V))
    (G.compat_secZero W)).choose

lemma coords_secZero (W : Y.Opens) : G.coords (G.secZero W) = 0 :=
  (G.exists_coords_eq _ (G.compat_secZero W)).choose_spec

private lemma compat_secNeg (s : (sectionsPresheaf f).obj (op W)) :
    ∀ (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V),
      G.transfer p q h ((- G.coords s) p) = (- G.coords s) q := fun p q h => by
    rw [Pi.neg_apply, ← transferHom_apply, map_neg, transferHom_apply, coords_transfer]
    rfl

/-- The negative of a section, in coordinates. -/
def secNeg (s : (sectionsPresheaf f).obj (op W)) : (sectionsPresheaf f).obj (op W) :=
  (G.exists_coords_eq (- G.coords s) (G.compat_secNeg s)).choose

lemma coords_secNeg (s : (sectionsPresheaf f).obj (op W)) :
    G.coords (G.secNeg s) = - G.coords s :=
  (G.exists_coords_eq _ (G.compat_secNeg s)).choose_spec

private lemma compat_secSub (s t : (sectionsPresheaf f).obj (op W)) :
    ∀ (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V),
      G.transfer p q h ((G.coords s - G.coords t) p) = (G.coords s - G.coords t) q :=
  fun p q h => by
    rw [Pi.sub_apply, ← transferHom_apply, map_sub, transferHom_apply, transferHom_apply,
      coords_transfer, coords_transfer]
    rfl

/-- The difference of two sections, in coordinates. -/
def secSub (s t : (sectionsPresheaf f).obj (op W)) : (sectionsPresheaf f).obj (op W) :=
  (G.exists_coords_eq (G.coords s - G.coords t) (G.compat_secSub s t)).choose

lemma coords_secSub (s t : (sectionsPresheaf f).obj (op W)) :
    G.coords (G.secSub s t) = G.coords s - G.coords t :=
  (G.exists_coords_eq _ (G.compat_secSub s t)).choose_spec

private lemma compat_secZsmul (m : ℤ) (s : (sectionsPresheaf f).obj (op W)) :
    ∀ (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V),
      G.transfer p q h ((m • G.coords s) p) = (m • G.coords s) q := fun p q h => by
    rw [Pi.smul_apply, ← transferHom_apply, map_zsmul, transferHom_apply, coords_transfer]
    rfl

/-- Integer multiples of a section, in coordinates. -/
def secZsmul (m : ℤ) (s : (sectionsPresheaf f).obj (op W)) : (sectionsPresheaf f).obj (op W) :=
  (G.exists_coords_eq (m • G.coords s) (G.compat_secZsmul m s)).choose

lemma coords_secZsmul (m : ℤ) (s : (sectionsPresheaf f).obj (op W)) :
    G.coords (G.secZsmul m s) = m • G.coords s :=
  (G.exists_coords_eq _ (G.compat_secZsmul m s)).choose_spec

private lemma compat_secNsmul (m : ℕ) (s : (sectionsPresheaf f).obj (op W)) :
    ∀ (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V),
      G.transfer p q h ((m • G.coords s) p) = (m • G.coords s) q := fun p q h => by
    rw [Pi.smul_apply, ← transferHom_apply, map_nsmul, transferHom_apply, coords_transfer]
    rfl

/-- Natural multiples of a section, in coordinates. -/
def secNsmul (m : ℕ) (s : (sectionsPresheaf f).obj (op W)) : (sectionsPresheaf f).obj (op W) :=
  (G.exists_coords_eq (m • G.coords s) (G.compat_secNsmul m s)).choose

lemma coords_secNsmul (m : ℕ) (s : (sectionsPresheaf f).obj (op W)) :
    G.coords (G.secNsmul m s) = m • G.coords s :=
  (G.exists_coords_eq _ (G.compat_secNsmul m s)).choose_spec

private lemma compat_secSmul (r : Γ(Y, W)) (s : (sectionsPresheaf f).obj (op W)) :
    ∀ (p q : G.ChartPiece W) (h : (q.V : Y.Opens) ≤ p.V),
      G.transfer p q h ((fun p => G.resPiece p r • G.coords s p) p) =
        (fun p => G.resPiece p r • G.coords s p) q :=
  fun p q h => by
    rw [transfer_smul, coords_transfer, map_resPiece]

/-- The product of a function `r ∈ 𝒪_Y(W)` with a section, in coordinates. -/
def secSmul (r : Γ(Y, W)) (s : (sectionsPresheaf f).obj (op W)) :
    (sectionsPresheaf f).obj (op W) :=
  (G.exists_coords_eq (fun p => G.resPiece p r • G.coords s p) (G.compat_secSmul r s)).choose

lemma coords_secSmul (r : Γ(Y, W)) (s : (sectionsPresheaf f).obj (op W)) :
    G.coords (G.secSmul r s) = fun p => G.resPiece p r • G.coords s p :=
  (G.exists_coords_eq _ (G.compat_secSmul r s)).choose_spec

variable (W) in
/-- **The additive group of sections** of a geometric vector bundle over `W`, transported from
the chart coordinates. -/
abbrev addCommGroupSections : AddCommGroup ((sectionsPresheaf f).obj (op W)) :=
  letI : Zero ((sectionsPresheaf f).obj (op W)) := ⟨G.secZero W⟩
  letI : Add ((sectionsPresheaf f).obj (op W)) := ⟨G.secAdd⟩
  letI : Neg ((sectionsPresheaf f).obj (op W)) := ⟨G.secNeg⟩
  letI : Sub ((sectionsPresheaf f).obj (op W)) := ⟨G.secSub⟩
  letI : SMul ℕ ((sectionsPresheaf f).obj (op W)) := ⟨G.secNsmul⟩
  letI : SMul ℤ ((sectionsPresheaf f).obj (op W)) := ⟨G.secZsmul⟩
  Function.Injective.addCommGroup (G.coords (W := W)) (G.coords_injective W)
    (G.coords_secZero W) G.coords_secAdd G.coords_secNeg G.coords_secSub
    (fun s m => G.coords_secNsmul m s) (fun s m => G.coords_secZsmul m s)

variable (W) in
/-- **The `𝒪_Y(W)`-module of sections** of a geometric vector bundle over `W`: the module
structure of the chart coordinates (Hartshorne II, Exercise 5.18). -/
abbrev moduleSections :
    letI := G.addCommGroupSections W
    Module Γ(Y, W) ((sectionsPresheaf f).obj (op W)) :=
  letI := G.addCommGroupSections W
  { smul := G.secSmul
    one_smul := fun s => G.coords_injective W (by
      change G.coords (G.secSmul 1 s) = _
      rw [coords_secSmul]; funext p; simp)
    mul_smul := fun r r' s => G.coords_injective W (by
      change G.coords (G.secSmul _ _) = G.coords (G.secSmul _ (G.secSmul _ _))
      rw [coords_secSmul, coords_secSmul, coords_secSmul]; funext p; simp [mul_smul])
    smul_zero := fun r => G.coords_injective W (by
      change G.coords (G.secSmul _ (G.secZero W)) = G.coords (G.secZero W)
      rw [coords_secSmul, coords_secZero]; funext p; simp)
    smul_add := fun r s t => G.coords_injective W (by
      change G.coords (G.secSmul _ (G.secAdd _ _)) =
        G.coords (G.secAdd (G.secSmul _ _) (G.secSmul _ _))
      rw [coords_secSmul, coords_secAdd, coords_secAdd, coords_secSmul, coords_secSmul]
      funext p; simp [smul_add])
    add_smul := fun r r' s => G.coords_injective W (by
      change G.coords (G.secSmul _ _) = G.coords (G.secAdd (G.secSmul _ _) (G.secSmul _ _))
      rw [coords_secSmul, coords_secAdd, coords_secSmul, coords_secSmul]
      funext p; simp [add_smul])
    zero_smul := fun s => G.coords_injective W (by
      change G.coords (G.secSmul _ _) = G.coords (G.secZero W)
      rw [coords_secSmul, coords_secZero]; funext p; simp) }

/-- Coordinates of a restriction: the coordinates on the chart pieces of the smaller open. -/
lemma coords_map {W W' : Y.Opens} (i : op W ⟶ op W') (s : (sectionsPresheaf f).obj (op W))
    (q : G.ChartPiece W') :
    G.coords ((sectionsPresheaf f).map i s) q =
      G.coords s ⟨q.i, q.V, q.hi, q.hW.trans (leOfHom i.unop)⟩ := by
  rw [coords, coords, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The restriction maps of sections, as additive maps. -/
def resHom {W W' : Y.Opens} (i : op W ⟶ op W') :
    letI := G.addCommGroupSections W
    letI := G.addCommGroupSections W'
    (sectionsPresheaf f).obj (op W) →+ (sectionsPresheaf f).obj (op W') :=
  letI := G.addCommGroupSections W
  letI := G.addCommGroupSections W'
  { toFun := (sectionsPresheaf f).map i
    map_zero' := G.coords_injective W' (by
      change G.coords ((sectionsPresheaf f).map i (G.secZero W)) = G.coords (G.secZero W')
      funext q
      rw [coords_map, coords_secZero, coords_secZero]
      rfl)
    map_add' := fun s t => G.coords_injective W' (by
      change G.coords ((sectionsPresheaf f).map i (G.secAdd s t)) =
        G.coords (G.secAdd ((sectionsPresheaf f).map i s) ((sectionsPresheaf f).map i t))
      funext q
      rw [coords_map, coords_secAdd, coords_secAdd, Pi.add_apply, Pi.add_apply, coords_map,
        coords_map]) }

lemma resHom_smul {W W' : Y.Opens} (i : op W ⟶ op W') (r : Γ(Y, W))
    (s : (sectionsPresheaf f).obj (op W)) :
    (sectionsPresheaf f).map i (G.secSmul r s) =
      G.secSmul (Y.presheaf.map i r) ((sectionsPresheaf f).map i s) := by
  refine G.coords_injective W' (funext fun q => ?_)
  rw [coords_map, coords_secSmul, coords_secSmul]
  dsimp only
  rw [coords_map, resPiece, resPiece, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The sections of a geometric vector bundle as a presheaf of abelian groups. -/
def sectionsAb : (Opens Y)ᵒᵖ ⥤ Ab.{u} where
  obj W := @AddCommGrpCat.of ((sectionsPresheaf f).obj W) (G.addCommGroupSections W.unop)
  map {W W'} i := @AddCommGrpCat.ofHom _ _ (G.addCommGroupSections W.unop)
    (G.addCommGroupSections W'.unop) (G.resHom i)
  map_id W := AddCommGrpCat.ext fun s =>
    ConcreteCategory.congr_hom ((sectionsPresheaf f).map_id W) s
  map_comp i j := AddCommGrpCat.ext fun s =>
    ConcreteCategory.congr_hom ((sectionsPresheaf f).map_comp i j) s

/-- **The sheaf of sections of a geometric vector bundle as an `𝒪_Y`-module** (Hartshorne II,
Exercise 5.18): sections of `f` with the module structure of the chart coordinates. -/
def sectionsModule : Y.Modules where
  val := @PresheafOfModules.ofPresheaf _ _ _ G.sectionsAb
    (fun W => G.moduleSections W.unop) (by
      intro W W' i r s
      change (sectionsPresheaf f).map i (G.secSmul r s) =
        G.secSmul (Y.presheaf.map i r) ((sectionsPresheaf f).map i s)
      exact G.resHom_smul i r s)
  isSheaf := by
    have e : G.sectionsAb ⋙ CategoryTheory.forget Ab ≅ sectionsPresheaf f :=
      NatIso.ofComponents (fun W => Iso.refl _) (fun _ => by ext; rfl)
    rw [PresheafOfModules.ofPresheaf_presheaf, Presheaf.isSheaf_iff_isSheaf_comp _ _
      (CategoryTheory.forget Ab), Presheaf.isSheaf_of_iso_iff e]
    exact isSheaf_sectionsPresheaf f

/-- Families of functions on an open `V` agreeing on all chart pieces of `V` are equal. -/
private lemma coordY_eq_of_pieces {V : Y.Opens}
    (x y : ULift.{u} (Fin n) → Γ(Y, V))
    (h : ∀ q : G.ChartPiece V, (fun k => Y.presheaf.map (homOfLE q.hW).op (x k)) =
      fun k => Y.presheaf.map (homOfLE q.hW).op (y k)) : x = y := by
  funext k
  exact Y.sheaf.eq_of_locally_eq' (fun q : G.ChartPiece V => (q.V : Y.Opens)) V
    (fun q => homOfLE q.hW) (G.le_iSup_chartPiece V) _ _ fun q => congrFun (h q) k

/-- The chart piece of `V` with chart `i` on the affine open of a chart piece `q`. -/
private abbrev pieceIn (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) (q : G.ChartPiece V) :
    G.ChartPiece V :=
  ⟨i, q.V, q.hW.trans hi, q.hW⟩

private lemma res_coordY (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i)
    (s : (sectionsPresheaf f).obj (op V)) (q : G.ChartPiece V) :
    (fun k => Y.presheaf.map (homOfLE q.hW).op (G.coordY i hi s k)) =
      G.coords s (G.pieceIn i hi q) := by
  funext k
  rw [← coordY_restrict]
  rfl

/-- **The chart coordinates are additive** for the module structure of the sections. -/
lemma coordY_secAdd (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i)
    (s t : (sectionsPresheaf f).obj (op V)) :
    G.coordY i hi (G.secAdd s t) = G.coordY i hi s + G.coordY i hi t := by
  refine G.coordY_eq_of_pieces _ _ fun q => ?_
  rw [res_coordY, coords_secAdd]
  funext k
  simp only [Pi.add_apply, map_add]
  rw [← res_coordY G i hi s q, ← res_coordY G i hi t q]

/-- **The chart coordinates are `𝒪_Y(V)`-linear** for the module structure of the sections. -/
lemma coordY_secSmul (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) (r : Γ(Y, V))
    (s : (sectionsPresheaf f).obj (op V)) :
    G.coordY i hi (G.secSmul r s) = r • G.coordY i hi s := by
  refine G.coordY_eq_of_pieces _ _ fun q => ?_
  rw [res_coordY, coords_secSmul]
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← res_coordY G i hi s q]

/-- Chart coordinates of the restriction of a sum. -/
lemma coordY_map_secAdd (i : G.ι) {W V : Y.Opens} (hV : V ≤ W) (hi : V ≤ G.U i)
    (s t : (sectionsPresheaf f).obj (op W)) :
    G.coordY i hi ((sectionsPresheaf f).map (homOfLE hV).op (G.secAdd s t)) =
      G.coordY i hi ((sectionsPresheaf f).map (homOfLE hV).op s) +
        G.coordY i hi ((sectionsPresheaf f).map (homOfLE hV).op t) := by
  let _ := G.addCommGroupSections W
  let _ := G.addCommGroupSections V
  have : (sectionsPresheaf f).map (homOfLE hV).op (G.secAdd s t) =
      G.secAdd ((sectionsPresheaf f).map (homOfLE hV).op s)
        ((sectionsPresheaf f).map (homOfLE hV).op t) :=
    (G.resHom (homOfLE hV).op).map_add s t
  rw [this, coordY_secAdd]

/-- Chart coordinates of the restriction of a multiple. -/
lemma coordY_map_secSmul (i : G.ι) {W V : Y.Opens} (hV : V ≤ W) (hi : V ≤ G.U i)
    (r : Γ(Y, W)) (s : (sectionsPresheaf f).obj (op W)) :
    G.coordY i hi ((sectionsPresheaf f).map (homOfLE hV).op (G.secSmul r s)) =
      Y.presheaf.map (homOfLE hV).op r •
        G.coordY i hi ((sectionsPresheaf f).map (homOfLE hV).op s) := by
  rw [resHom_smul, coordY_secSmul]

/-- The frame of the sections over `U_i` given by the chart `ψ_i`: the sections with chart
coordinates the standard basis vectors. -/
def frameSection (i : G.ι) (k : ULift.{u} (Fin n)) : (sectionsPresheaf f).obj (op (G.U i)) :=
  ((G.coordY_bijective i le_rfl).2 (Pi.single k 1)).choose

lemma coordY_frameSection (i : G.ι) (k : ULift.{u} (Fin n)) :
    G.coordY i le_rfl (G.frameSection i k) = Pi.single k 1 :=
  ((G.coordY_bijective i le_rfl).2 (Pi.single k 1)).choose_spec

/-- **The chart `ψ_i` gives a frame of the sheaf of sections over `U_i`.** -/
theorem isLocalFrame_frameSection (i : G.ι) :
    Hartshorne.Ringed.IsLocalFrame (R := Y.sheaf) G.sectionsModule (G.U i) (G.frameSection i) := by
  intro V h
  have key : ∀ a, G.coordY i h
      (Hartshorne.Ringed.localFrameMap (R := Y.sheaf) G.sectionsModule (G.frameSection i) h a) =
        a := fun a => by
    rw [Hartshorne.Ringed.localFrameMap_apply]
    let _ := G.addCommGroupSections V
    let φ : (sectionsPresheaf f).obj (op V) →+ (ULift.{u} (Fin n) → Γ(Y, V)) :=
      AddMonoidHom.mk' (G.coordY i h) (G.coordY_secAdd i h)
    change φ (∑ k, G.secSmul (a k) ((sectionsPresheaf f).map (homOfLE h).op
      (G.frameSection i k))) = a
    rw [map_sum]
    change ∑ k, G.coordY i h (G.secSmul (a k) ((sectionsPresheaf f).map (homOfLE h).op
      (G.frameSection i k))) = a
    simp_rw [coordY_secSmul]
    have hres : ∀ k, G.coordY i h ((sectionsPresheaf f).map (homOfLE h).op
        (G.frameSection i k)) = Pi.single k 1 := fun k => by
      funext l
      have := G.coordY_restrict i (le_refl (G.U i)) h (G.frameSection i k) l
      rw [coordY_frameSection] at this
      refine this.trans ?_
      by_cases hkl : l = k
      · subst hkl; rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne hkl, Pi.single_eq_of_ne hkl, map_zero]
    simp_rw [hres]
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨fun a b hab => (key a).symm.trans ((congrArg _ hab).trans (key b)), fun s => ?_⟩
  exact ⟨G.coordY i h s, (G.coordY_bijective i h).1 (key _)⟩

/-- **The sections of a geometric vector bundle of rank `n` form a locally free `𝒪_Y`-module of
rank `n`** (Hartshorne II, Exercise 5.18): over each `U_i`, the chart `ψ_i` gives a frame. -/
theorem sectionsModule_isLocallyFreeOfRank : G.sectionsModule.IsLocallyFreeOfRank n := by
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed]
  refine Hartshorne.Ringed.isLocallyFreeOfRank_of_isLocalFrame fun y => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (G.iSup_eq_top.ge (Set.mem_univ y))
  exact ⟨G.U i, G.frameSection i, hi, G.isLocalFrame_frameSection i⟩

/-- The sheaf of sets underlying `G.sectionsModule` is the sheaf of sections `𝒮(X/Y)`. -/
def sectionsModuleForgetIso :
    G.sectionsModule.val.presheaf ⋙ CategoryTheory.forget Ab ≅ sectionsPresheaf f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by ext; rfl)

/-- **The chart coordinates are additive** on the sections of `G.sectionsModule`. -/
lemma coordY_add (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) (s t : Γ(G.sectionsModule, V)) :
    G.coordY i hi (s + t) = G.coordY i hi s + G.coordY i hi t :=
  G.coordY_secAdd i hi s t

/-- **The chart coordinates are `𝒪_Y(V)`-linear** on the sections of `G.sectionsModule`. -/
lemma coordY_smul (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i) (r : Γ(Y, V))
    (s : Γ(G.sectionsModule, V)) :
    G.coordY i hi (r • s) = r • G.coordY i hi s :=
  G.coordY_secSmul i hi r s

end GeometricVectorBundle

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

/-- **The chart coordinates of a section of `V(E)` are the values of its linear form on the
frame**: for the atlas `vectorBundleAtlas` of `V(E)`, a frame `e` over `c.V` and an affine open
`V ⊆ c.V`, the `k`-th chart coordinate of a section `s` over `V` is the value of the linear form
`E(V) ⟶ 𝒪_Y(V)` of `s` on `e_k|_V`. Hence the chart-wise linear structure of `𝒮(V(E)/Y)` is the
one of `E^∨` (compare `localFrameEval_sectionDual`). -/
theorem vectorBundleAtlas_chartCoord (c : AffineFrame E n) (V : Y.affineOpens)
    (hV : (V : Y.Opens) ≤ c.V)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (V : Y.Opens)))
    (k : ULift.{u} (Fin n)) :
    (vectorBundleAtlas hE).chartCoord c hV s.1 s.2 k = (V : Y.Opens).topIso.inv
      (sectionLinearForm hE V s (E.presheaf.map (homOfLE hV).op (c.e k))) := by
  have hnat : ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : R),
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (φ x) :=
    fun φ x => by rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
  set G := vectorBundleAtlas hE
  set A := symmetricQuasiCoherentAlgebra E hE
  set he' := c.isLocalFrame.restrictLE hV
  set t := G.chartLift c hV s.1 s.2 ≫
    (AffineSpace.isoOfIsAffine (ULift.{u} (Fin n)) (V : Y.Opens).toScheme).hom
  have ht : t ≫ affineSpaceChart n V hV ≫ (G.ψ c).inv ≫
      (vectorBundleProj E hE ⁻¹ᵁ G.U c).ι = s.1 := by
    simp only [t, affineSpaceChart, Category.assoc, Iso.hom_inv_id_assoc]
    exact G.chartLift_map c hV s.1 s.2
  have h1 : t ≫ Spec.map (frameChartIso hE V he').inv ≫ A.ι (affineSite V) = s.1 := by
    rw [← affineSpaceChart_frameTrivialization_inv hE c.V V hV c.isLocalFrame]
    exact ht
  have h2 := RelSpecSections.sectionOfHom_homOfSection A (affineSite V) s.1 s.2
  rw [RelSpecSections.sectionOfHom] at h2
  have h3 : t ≫ Spec.map (frameChartIso hE V he').inv = (V : Y.Opens).toSpecΓ ≫
      Spec.map (RelSpecSections.homOfSection A (affineSite V) s.1 s.2) := by
    rw [← cancel_mono (A.ι (affineSite V)), Category.assoc, h1, Category.assoc]
    exact h2.symm
  have hX : (frameChartIso hE V he').hom (MvPolynomial.X k) =
      E.symDegreeOne V (E.presheaf.map (homOfLE hV).op (c.e k)) := by
    rw [frameChartIso_hom_apply, MvPolynomial.map_X, chartRingHom_X]
    rfl
  have h4 := congrArg (fun g => g.appTop ((Scheme.ΓSpecIso _).inv
    ((frameChartIso hE V he').hom (MvPolynomial.X k)))) h3
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hnat,
    Scheme.Opens.toSpecΓ_appTop, Iso.hom_inv_id_apply] at h4
  rw [GeometricVectorBundle.chartCoord_eq, h4, hX, hnat, Iso.inv_hom_id_apply]
  rfl

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
  exact inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
    (ObjectProperty.homMk (sectionsToDual hE) :
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

/-- On a framed affine open, the linear form of a section is given by its chart coordinates for
the atlas `vectorBundleAtlas`: `x = ∑ x_k e_k ↦ ∑ x_k s_k`. -/
private lemma sectionLinearForm_eq_sum (c : AffineFrame E n)
    (σ : (sectionsPresheaf (vectorBundleProj E hE)).obj (op (c.V : Y.Opens))) (x : Γ(E, c.V)) :
    sectionLinearForm hE c.V σ x =
      ∑ k, (show Γ(Y, c.V) from c.isLocalFrame.coord le_rfl x k) *
        (show Γ(Y, c.V) from (vectorBundleAtlas hE).coordY c le_rfl σ k) := by
  conv_lhs => rw [← c.isLocalFrame.localFrameMap_coord le_rfl x, localFrameMap_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (vectorBundleAtlas hE).coordY c le_rfl σ k =
      sectionLinearForm hE c.V σ (E.presheaf.map (homOfLE le_rfl).op (c.e k)) := by
    change (c.V : Y.Opens).topIso.hom ((vectorBundleAtlas hE).chartCoord c le_rfl σ.1 σ.2 k) = _
    rw [vectorBundleAtlas_chartCoord hE c c.V le_rfl σ k, Iso.inv_hom_id_apply]
  rw [LinearMap.map_smul]
  change _ = _ * (vectorBundleAtlas hE).coordY c le_rfl σ k
  rw [hk]
  rfl

/-- The image of a section `s` over `W` in `E^∨`, evaluated on `x ∈ E(V)` and restricted to a
framed affine open `c.V ⊆ V`, in terms of the chart coordinates of `s`. -/
private lemma res_eval_vectorBundleSectionsIso {W V : Y.Opens} (h : V ≤ W)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op W)) (x : Γ(E, V))
    (c : AffineFrame E n) (hc : (c.V : Y.Opens) ≤ V) :
    Y.presheaf.map (homOfLE hc).op
        (moduleSheafHomEval ((vectorBundleSectionsIso hE).hom.app (op W) s) h x) =
      ∑ k, (show Γ(Y, c.V) from c.isLocalFrame.coord le_rfl (E.presheaf.map (homOfLE hc).op x) k) *
        (show Γ(Y, c.V) from (vectorBundleAtlas hE).coordY c le_rfl
          ((sectionsPresheaf (vectorBundleProj E hE)).map (homOfLE (hc.trans h)).op s) k) := by
  have := moduleSheafHomEval_natural ((vectorBundleSectionsIso hE).hom.app (op W) s) h hc x
  refine this.symm.trans ?_
  rw [vectorBundleSectionsIso_hom_eval hE s (V := c.V) (hc.trans h)]
  exact sectionLinearForm_eq_sum hE c _ _

include hE in
/-- Elements of `𝒪_Y(V)` agreeing on all framed affine opens inside `V` are equal. -/
private lemma eq_of_framed {V : Y.Opens} (a b : Γ(Y, V))
    (hab : ∀ (c : AffineFrame E n) (hc : (c.V : Y.Opens) ≤ V),
      Y.presheaf.map (homOfLE hc).op a = Y.presheaf.map (homOfLE hc).op b) : a = b := by
  have hB := isBasis_affineFrame hE
  have hc : ∀ y : V, ∃ c : AffineFrame E n, y.1 ∈ (c.V : Y.Opens) ∧ (c.V : Y.Opens) ≤ V :=
    fun y => by
      obtain ⟨_, ⟨c, rfl⟩, hy, hle⟩ := Opens.isBasis_iff_nbhd.mp hB y.2
      exact ⟨c, hy, hle⟩
  choose c hyc hcV using hc
  exact Y.sheaf.eq_of_locally_eq' (fun y => (c y).V) V (fun y => homOfLE (hcV y))
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyc ⟨y, hy⟩⟩) _ _ fun y => hab (c y) (hcV y)

/-- The isomorphism `𝒮(V(E)/Y) ≅ E^∨` on sections over `W`, as an `𝒪_Y(W)`-linear map. -/
def vectorBundleSectionsLinear (W : Y.Opens) :
    Γ((vectorBundleAtlas hE).sectionsModule, W) →ₗ[Γ(Y, W)]
      Γ(moduleSheafDual (R := Y.sheaf) E, W) where
  toFun s := (vectorBundleSectionsIso hE).hom.app (op W) s
  map_add' s t := by
    change (vectorBundleSectionsIso hE).hom.app (op W) ((vectorBundleAtlas hE).secAdd s t) = _
    refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => ?_
    rw [moduleSheafHomEval_add, LinearMap.add_apply]
    refine eq_of_framed hE _ _ fun c hc => ?_
    have h1 := res_eval_vectorBundleSectionsIso hE h ((vectorBundleAtlas hE).secAdd s t) x c hc
    have h2 := res_eval_vectorBundleSectionsIso hE h s x c hc
    have h3 := res_eval_vectorBundleSectionsIso hE h t x c hc
    rw [GeometricVectorBundle.coordY_map_secAdd] at h1
    refine h1.trans ?_
    refine Eq.trans ?_ (map_add (Y.presheaf.map (homOfLE hc).op).hom _ _).symm
    refine Eq.trans ?_ (congrArg₂ (· + ·) h2 h3).symm
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r s := by
    change (vectorBundleSectionsIso hE).hom.app (op W) ((vectorBundleAtlas hE).secSmul r s) = _
    refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => ?_
    rw [RingHom.id_apply, moduleSheafHomEval_smul]
    refine eq_of_framed hE _ _ fun c hc => ?_
    have h1 := res_eval_vectorBundleSectionsIso hE h ((vectorBundleAtlas hE).secSmul r s) x c hc
    have h2 := res_eval_vectorBundleSectionsIso hE h s x c hc
    rw [GeometricVectorBundle.coordY_map_secSmul] at h1
    refine h1.trans ?_
    refine Eq.trans ?_ (map_mul (Y.presheaf.map (homOfLE hc).op).hom _ _).symm
    refine Eq.trans ?_ (congrArg₂ (· * ·) rfl h2).symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm]
    congr 1
    change Y.presheaf.map (homOfLE (hc.trans h)).op r =
      Y.presheaf.map (homOfLE hc).op (Y.presheaf.map (homOfLE h).op r)
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

/-- **The sections of `V(E)` are `E^∨` as `𝒪_Y`-modules** (Hartshorne II, Exercise 5.18(c)):
with the module structure of the chart coordinates of the geometric vector bundle `V(E)`
(`vectorBundleAtlas`), the sheaf of sections of `V(E) = Spec_Y Sym(E)` is isomorphic to
`E^∨ = ℋom(E, 𝒪_Y)`; on sections this is `vectorBundleSectionsIso`. -/
def vectorBundleSectionsModuleIso :
    (vectorBundleAtlas hE).sectionsModule ≅ moduleSheafDual (R := Y.sheaf) E :=
  haveI : IsIso (modulesHomMk (R := Y.sheaf) (vectorBundleSectionsLinear hE) fun _ _ i x =>
      ConcreteCategory.congr_hom ((vectorBundleSectionsIso hE).hom.naturality (homOfLE i).op) x) :=
    modules_isIso_of_locally_bijective _ fun _ => ⟨⊤, trivial, fun V _ =>
      (isIso_iff_bijective ((vectorBundleSectionsIso hE).hom.app (op V))).mp inferInstance⟩
  asIso (modulesHomMk (R := Y.sheaf) (vectorBundleSectionsLinear hE) fun _ _ i x =>
      ConcreteCategory.congr_hom ((vectorBundleSectionsIso hE).hom.naturality (homOfLE i).op) x)

lemma vectorBundleSectionsModuleIso_hom_apply (W : Y.Opens)
    (s : (sectionsPresheaf (vectorBundleProj E hE)).obj (op W)) :
    sectionsMap (vectorBundleSectionsModuleIso hE).hom W s =
      (vectorBundleSectionsIso hE).hom.app (op W) s := rfl

end Scheme.Modules

end

end AlgebraicGeometry
