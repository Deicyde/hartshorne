/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Veronese
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Hartshorne.Scheme.ProjTailIsomorphism

/-!
# `Proj S ≅ Proj S^{(d)}`

Hartshorne, *Algebraic Geometry*, II, Exercise 5.13 (p. 126). Hartshorne assumes `S` generated
by `S₁` as an `S₀`-algebra; the results here hold without that hypothesis.

Let `S` be an `ℕ`-graded ring, `d > 0` and `S^{(d)} = ⊕_n S_{nd}` the Veronese subring. Sending a
relevant homogeneous prime `𝔭` of `S` to `𝔭 ∩ S^{(d)}` defines a morphism of schemes
`Proj S ⟶ Proj S^{(d)}`: on stalks it is the map `S^{(d)}_{(𝔭 ∩ S^{(d)})} → S_{(𝔭)}` sending a
fraction `a / b` with `a, b ∈ S_{nd}` to itself. On the standard chart `D₊(g)` for homogeneous
`g ∈ S^{(d)}` of positive degree, it is the morphism `Spec S_{(g)} ⟶ Spec S^{(d)}_{(g)}` of the
isomorphism `S^{(d)}_{(g)} ≅ S_{(g)}`; since these charts cover `Proj S^{(d)}` and being an
isomorphism is local on the target, the morphism is an isomorphism.

## Main definitions and results

* `Hartshorne.Veronese.comapPoint`: `𝔭 ↦ 𝔭 ∩ S^{(d)}`.
* `Hartshorne.Veronese.toProj`: the morphism `Proj S ⟶ Proj S^{(d)}`.
* `Hartshorne.Veronese.awayι_comp_toProj`: its description on the chart `D₊(g)`.
* `Hartshorne.Veronese.projIso`: the isomorphism `Proj S ≅ Proj S^{(d)}`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomogeneousIdeal HomogeneousLocalization TopologicalSpace
open AlgebraicGeometry ProjectiveSpectrum

universe u

namespace Hartshorne

namespace Veronese

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] (d : ℕ) [NeZero d]

/-! ### Points -/

@[deprecated ProjTail.exists_homogeneous_not_mem (since := "2026-11-09")]
alias exists_homogeneous_notMem := ProjTail.exists_homogeneous_not_mem

/-- The homogeneous ideal `I ∩ S^{(d)}` of `S^{(d)}`, for a homogeneous ideal `I` of `S`. -/
def comapIdeal (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal (veronese 𝒜 d) where
  toSubmodule := I.toIdeal.comap (veroneseSubring 𝒜 d).subtype
  is_homogeneous' i r hr := by
    change ((DirectSum.decompose (veronese 𝒜 d) r i : veroneseSubring 𝒜 d) : A) ∈ I.toIdeal
    rw [coe_decompose]
    exact I.isHomogeneous (i * d) hr

@[simp] theorem mem_comapIdeal {I : HomogeneousIdeal 𝒜} {r : veroneseSubring 𝒜 d} :
    r ∈ comapIdeal d I ↔ (r : A) ∈ I :=
  Iff.rfl

theorem mem_comapIdeal_toIdeal {I : HomogeneousIdeal 𝒜} {r : veroneseSubring 𝒜 d} :
    r ∈ (comapIdeal d I).toIdeal ↔ (r : A) ∈ I.toIdeal :=
  Iff.rfl

/-- The point `𝔭 ∩ S^{(d)}` of `Proj S^{(d)}` for a point `𝔭` of `Proj S`. -/
def comapPoint (x : ProjectiveSpectrum 𝒜) : ProjectiveSpectrum (veronese 𝒜 d) where
  asHomogeneousIdeal := comapIdeal d x.asHomogeneousIdeal
  isPrime := inferInstanceAs ((x.asHomogeneousIdeal.toIdeal.comap
    (veroneseSubring 𝒜 d).subtype).IsPrime)
  not_irrelevant_le h := by
    obtain ⟨e, t, he, ht, htx⟩ := ProjTail.exists_homogeneous_not_mem x
    have htd : t ^ d ∈ 𝒜 (e * d) := by
      simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded d ht
    have hmem := h (mem_irrelevant_of_mem (veronese 𝒜 d) he (ofMem_mem htd))
    exact htx (x.isPrime.mem_of_pow_mem d hmem)

@[simp] theorem comapPoint_asHomogeneousIdeal (x : ProjectiveSpectrum 𝒜) :
    (comapPoint d x).asHomogeneousIdeal = comapIdeal d x.asHomogeneousIdeal :=
  rfl

/-- The continuous map `Proj S → Proj S^{(d)}`, `𝔭 ↦ 𝔭 ∩ S^{(d)}`. -/
def comap : C(ProjectiveSpectrum 𝒜, ProjectiveSpectrum (veronese 𝒜 d)) where
  toFun := comapPoint d
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    refine fun s ↦ ⟨(veroneseSubring 𝒜 d).subtype '' s, ?_⟩
    ext x
    simp only [Set.mem_preimage, mem_zeroLocus, Set.image_subset_iff]
    rfl

@[simp] theorem comap_apply (x : ProjectiveSpectrum 𝒜) : comap d x = comapPoint d x :=
  rfl

/-! ### Stalks -/

/-- The map of stalks `S^{(d)}_{(𝔭 ∩ S^{(d)})} → S_{(𝔭)}`. -/
def atPrimeMap (x : ProjectiveSpectrum 𝒜) :
    AtPrime (veronese 𝒜 d) (comapPoint d x).asHomogeneousIdeal.toIdeal →+*
      AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal :=
  hlMap (fun _ hr => hr)

theorem atPrimeMap_mk (x : ProjectiveSpectrum 𝒜) (c) :
    atPrimeMap d x (HomogeneousLocalization.mk c) =
      HomogeneousLocalization.mk (numDenMap (fun _ hr => hr) c) :=
  rfl

theorem val_atPrimeMap (x : ProjectiveSpectrum 𝒜) (z) :
    (atPrimeMap d x z).val = Localization.localRingHom _ _ (veroneseSubring 𝒜 d).subtype rfl
      z.val :=
  val_hlMap _ z

instance isLocalHom_atPrimeMap (x : ProjectiveSpectrum 𝒜) : IsLocalHom (atPrimeMap d x) where
  map_nonunit z hz := by
    rw [← isUnit_iff_isUnit_val] at hz ⊢
    rw [val_atPrimeMap] at hz
    exact (Localization.isLocalHom_localRingHom (J := x.asHomogeneousIdeal.toIdeal)
      (f := (veroneseSubring 𝒜 d).subtype) (hIJ := rfl)).map_nonunit _ hz

/-! ### The morphism of schemes -/

section structureSheaf

variable (U : Opens (ProjectiveSpectrum (veronese 𝒜 d))) (V : Opens (ProjectiveSpectrum 𝒜))
  (hUV : V.1 ⊆ comap d ⁻¹' U.1)

/-- The underlying function of `Proj S ⟶ Proj S^{(d)}` on the level of structure sheaves. -/
def comapStructureSheafFun (s : ∀ x : U, AtPrime (veronese 𝒜 d) x.1.1.1) (y : V) :
    AtPrime 𝒜 y.1.1.1 :=
  atPrimeMap d y.1 (s ⟨comap d y.1, hUV y.2⟩)

set_option backward.isDefEq.respectTransparency false in
theorem isLocallyFraction_comapStructureSheafFun
    (s : ∀ x : U, AtPrime (veronese 𝒜 d) x.1.1.1)
    (hs : (StructureSheaf.isLocallyFraction (veronese 𝒜 d)).pred s) :
    (StructureSheaf.isLocallyFraction 𝒜).pred (comapStructureSheafFun d U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨comap d p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (comap d) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i * d,
    ⟨(a.1 : A), a.2⟩, ⟨(b.1 : A), b.2⟩, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  specialize h_frac ⟨_, hqW⟩
  exact (congrArg (atPrimeMap d q) h_frac).trans rfl

/-- The underlying ring hom of `Proj S ⟶ Proj S^{(d)}` on the level of structure sheaves. -/
def comapStructureSheaf :
    (Proj.structureSheaf (veronese 𝒜 d)).1.obj (.op U) →+*
      (Proj.structureSheaf 𝒜).1.obj (.op V) where
  toFun s := ⟨comapStructureSheafFun d _ _ hUV s.1,
      isLocallyFraction_comapStructureSheafFun d _ _ hUV _ s.2⟩
  map_one' := Subtype.ext <| funext fun x => map_one (atPrimeMap d x.1)
  map_zero' := Subtype.ext <| funext fun x => map_zero (atPrimeMap d x.1)
  map_add' _ _ := Subtype.ext <| funext fun x => map_add (atPrimeMap d x.1) _ _
  map_mul' _ _ := Subtype.ext <| funext fun x => map_mul (atPrimeMap d x.1) _ _

end structureSheaf

set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying map of `Proj S ⟶ Proj S^{(d)}` on the level of sheafed spaces. -/
@[simps! (isSimp := false)] def sheafedSpaceMap :
    Proj.toSheafedSpace 𝒜 ⟶ Proj.toSheafedSpace (veronese 𝒜 d) where
  hom :=
    { base := TopCat.ofHom <| comap d
      c := { app U := CommRingCat.ofHom <| comapStructureSheaf d _ _ Set.Subset.rfl } }

set_option backward.isDefEq.respectTransparency.types false in
theorem germ_map_sectionInBasicOpen {p : ProjectiveSpectrum 𝒜}
    (c : NumDenSameDeg (veronese 𝒜 d) (comapPoint d p).1.toIdeal.primeCompl) :
    (Proj.toSheafedSpace 𝒜).presheaf.germ
      ((Opens.map (sheafedSpaceMap d).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap d).hom.c.app _ (sectionInBasicOpen (veronese 𝒜 d) _ c)) =
    (Proj.toSheafedSpace 𝒜).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ ((c.den : veroneseSubring 𝒜 d) : A)) p c.4
      (sectionInBasicOpen 𝒜 p (numDenMap (fun _ hr => hr) c)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem atPrimeMap_comp_stalkIso (p : Proj 𝒜) :
    (Proj.stalkIso (veronese 𝒜 d) ((sheafedSpaceMap d).hom.base p)).hom ≫
      CommRingCat.ofHom (atPrimeMap d p) ≫ (Proj.stalkIso 𝒜 p).inv =
      (sheafedSpaceMap d).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, Proj.stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [RingHom.comp_apply]
  erw [Proj.stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen]
  erw [Proj.stalkIso'_germ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The morphism `Proj S ⟶ Proj S^{(d)}`**, `𝔭 ↦ 𝔭 ∩ S^{(d)}`. -/
def toProj : Proj 𝒜 ⟶ Proj (veronese 𝒜 d) where
  __ := (sheafedSpaceMap d).hom
  prop p := .mk fun x hx ↦ by
    rw [← atPrimeMap_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (Proj.stalkIso 𝒜 p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := (isLocalHom_atPrimeMap d p).map_nonunit _ hx
    have : IsLocalHom (Proj.stalkIso (veronese 𝒜 d) ((sheafedSpaceMap d).hom.base p)).hom.hom :=
      isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

theorem toProj_apply (x : Proj 𝒜) : toProj d x = comapPoint d x :=
  rfl

@[simp] theorem toProj_preimage_basicOpen (g : veroneseSubring 𝒜 d) :
    toProj d ⁻¹ᵁ Proj.basicOpen (veronese 𝒜 d) g = Proj.basicOpen 𝒜 (g : A) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem ι_comp_toProj (g : veroneseSubring 𝒜 d) :
    (Proj.basicOpen 𝒜 (g : A)).ι ≫ toProj d =
      (toProj d).resLE _ _ le_rfl ≫ (Proj.basicOpen (veronese 𝒜 d) g).ι := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] theorem awayToSection_comp_appLE {i : ℕ} {g : veroneseSubring 𝒜 d}
    (hg : g ∈ veronese 𝒜 d i) :
    AlgebraicGeometry.Proj.awayToSection (veronese 𝒜 d) g ≫
      (toProj d).appLE (Proj.basicOpen (veronese 𝒜 d) g) (Proj.basicOpen 𝒜 (g : A)) le_rfl =
    CommRingCat.ofHom (awayMap g) ≫ AlgebraicGeometry.Proj.awayToSection 𝒜 (g : A) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective (veronese 𝒜 d) hg x
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    awayMap_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **The morphism `Proj S ⟶ Proj S^{(d)}` on a standard chart**: for homogeneous `g ∈ S^{(d)}_i`
with `i > 0`, its restriction to `D₊(g) ≅ Spec S_{(g)}` is `Spec S_{(g)} ⟶ Spec S^{(d)}_{(g)}`
followed by the chart `Spec S^{(d)}_{(g)} ≅ D₊(g)` of `Proj S^{(d)}`. -/
@[reassoc] theorem awayι_comp_toProj {i : ℕ} (hi : 0 < i) {g : veroneseSubring 𝒜 d}
    (hg : g ∈ veronese 𝒜 d i) :
    Proj.awayι 𝒜 (g : A) (mem_veronese_iff.mp hg) (Nat.mul_pos hi (NeZero.pos d)) ≫ toProj d =
      Spec.map (CommRingCat.ofHom (awayMap g)) ≫ Proj.awayι (veronese 𝒜 d) g hg hi := by
  rw [Proj.awayι, Proj.awayι, Category.assoc, ι_comp_toProj, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (Proj.basicOpen 𝒜 (g : A)).topIso.hom).mp ?_
  simp [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top, awayToSection_comp_appLE _ hg]

/-- Over a standard open `D₊(g)` of `Proj S^{(d)}`, the morphism `Proj S ⟶ Proj S^{(d)}` is an
isomorphism. -/
theorem isIso_morphismRestrict {i : ℕ} (hi : 0 < i) {g : veroneseSubring 𝒜 d}
    (hg : g ∈ veronese 𝒜 d i) :
    IsIso (toProj d ∣_ Proj.basicOpen (veronese 𝒜 d) g) := by
  have : IsIso (CommRingCat.ofHom (awayMap g)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨awayMap_injective g, awayMap_surjective hg⟩
  have key : toProj d ∣_ Proj.basicOpen (veronese 𝒜 d) g =
      (Scheme.isoOfEq _ (toProj_preimage_basicOpen d g)).hom ≫
        (Proj.basicOpenIsoSpec 𝒜 (g : A) (mem_veronese_iff.mp hg)
          (Nat.mul_pos hi (NeZero.pos d))).hom ≫
        Spec.map (CommRingCat.ofHom (awayMap g)) ≫
        (Proj.basicOpenIsoSpec (veronese 𝒜 d) g hg hi).inv := by
    rw [← cancel_mono (Proj.basicOpen (veronese 𝒜 d) g).ι, morphismRestrict_ι]
    simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
    rw [← awayι_comp_toProj d hi hg, Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc,
      Scheme.isoOfEq_hom_ι_assoc]
  rw [key]
  infer_instance

/-- The standard opens `D₊(g)`, `g` homogeneous of positive degree, cover `Proj S`. -/
theorem iSup_basicOpen_eq_top' :
    ⨆ g : Σ' (i : ℕ) (g : A), 0 < i ∧ g ∈ 𝒜 i, Proj.basicOpen 𝒜 g.2.1 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨e, t, he, ht, htx⟩ := ProjTail.exists_homogeneous_not_mem x
  exact Opens.mem_iSup.mpr ⟨⟨e, t, he, ht⟩, (Proj.mem_basicOpen _ _ _).mpr htx⟩

/-- `Proj S ⟶ Proj S^{(d)}` is an isomorphism. -/
instance isIso_toProj : IsIso (toProj (𝒜 := 𝒜) d) := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (f := toProj d) _ (iSup_basicOpen_eq_top' (𝒜 := veronese 𝒜 d))).mpr ?_
  rintro ⟨i, g, hi, hg⟩
  exact isIso_morphismRestrict d hi hg

variable (𝒜) in
/-- **`Proj S ≅ Proj S^{(d)}` (cf. Hartshorne II, Exercise 5.13).** For an `ℕ`-graded ring `S` and
`d > 0`, the morphism `Proj S ⟶ Proj S^{(d)}`, `𝔭 ↦ 𝔭 ∩ S^{(d)}`, is an isomorphism. Hartshorne
assumes `S` generated by `S₁`; the isomorphism here holds without that hypothesis. -/
def projIso : Proj 𝒜 ≅ Proj (veronese 𝒜 d) :=
  asIso (toProj d)

@[simp] theorem projIso_hom : (projIso 𝒜 d).hom = toProj d :=
  rfl

end Veronese

end Hartshorne
