/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VectorBundleSections

/-!
# Isomorphisms of geometric vector bundles

Hartshorne II, Exercise 5.18 (pp. 128–129).

## Isomorphisms of geometric vector bundles

Hartshorne calls an isomorphism `g : X ≅ X'` over `Y` of schemes carrying geometric vector bundle
structures `(X, {U_i}, {ψ_i})` and `(X', {U'_j}, {ψ'_j})` of rank `n` an *isomorphism of geometric
vector bundles* if `X`, the union of the two coverings, and the trivializations `ψ_i` and
`ψ'_j ∘ g` together form a geometric vector bundle structure on `X`.

* `GeometricVectorBundle.transport`: the trivializations `ψ'_j ∘ g` of `X` obtained from a bundle
  structure on `X'` and an isomorphism `g : X ≅ X'` over `Y`.
* `GeometricVectorBundle.Compatible`: two bundle structures on the same `X` are compatible if the
  union of the coverings with all the trivializations satisfies the linearity condition of a
  geometric vector bundle; `GeometricVectorBundle.union` is the combined structure.
* `GeometricVectorBundle.BundleIso`: an isomorphism of geometric vector bundles, with
  `BundleIso.refl` and `BundleIso.symm`.

## Invariance of the sheaf of sections

* `GeometricVectorBundle.BundleIso.sectionsModuleIso`: an isomorphism of geometric vector bundles
  `g` induces the isomorphism `𝒮(X/Y) ≅ 𝒮(X'/Y)`, `s ↦ g ∘ s`, of the sheaves of sections with
  their `𝒪_Y`-module structures given by the charts. Thus the sheaf of sections, as an
  `𝒪_Y`-module, depends only on the isomorphism class of the bundle.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X X' Y : Scheme.{u}} {n : ℕ}

namespace GeometricVectorBundle

variable {f : X ⟶ Y} {f' : X' ⟶ Y}

/-- The chart `ψ_i⁻¹ : 𝔸ⁿ_{U_i} ⟶ X` of a geometric vector bundle, an open immersion onto
`f⁻¹(U_i)`. -/
def chart (G : GeometricVectorBundle f n) (i : G.ι) : 𝔸(ULift.{u} (Fin n); G.U i) ⟶ X :=
  (G.ψ i).inv ≫ (f ⁻¹ᵁ G.U i).ι

/-- The linearity condition of Exercise 5.18 for two charts `c : 𝔸ⁿ_U ⟶ Z`, `c' : 𝔸ⁿ_{U'} ⟶ Z` at
an affine open `V ⊆ U ∩ U'` with ring of sections `A`: on `𝔸ⁿ_V = Spec A[x_1, …, x_n]`, the charts
differ by `Spec θ` for a linear `A`-algebra automorphism `θ` of `A[x_1, …, x_n]`. -/
def IsLinearTransition {Z : Scheme.{u}} (V : Y.affineOpens) {U U' : Y.Opens}
    (h : (V : Y.Opens) ≤ U) (h' : (V : Y.Opens) ≤ U') (c : 𝔸(ULift.{u} (Fin n); U) ⟶ Z)
    (c' : 𝔸(ULift.{u} (Fin n); U') ⟶ Z) : Prop :=
  ∃ θ : MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) ≃ₐ[Γ(V, ⊤)]
      MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤),
    IsLinearPolynomialAlgHom θ.toAlgHom ∧
      affineSpaceChart n V h' ≫ c' =
        Spec.map (CommRingCat.ofHom θ.toRingEquiv.toRingHom) ≫ affineSpaceChart n V h ≫ c

lemma IsLinearTransition.comp {Z Z' : Scheme.{u}} {V : Y.affineOpens} {U U' : Y.Opens}
    {h : (V : Y.Opens) ≤ U} {h' : (V : Y.Opens) ≤ U'} {c : 𝔸(ULift.{u} (Fin n); U) ⟶ Z}
    {c' : 𝔸(ULift.{u} (Fin n); U') ⟶ Z} (hc : IsLinearTransition V h h' c c') (g : Z ⟶ Z') :
    IsLinearTransition V h h' (c ≫ g) (c' ≫ g) := by
  obtain ⟨θ, hθ, e⟩ := hc
  exact ⟨θ, hθ, by simp only [← Category.assoc] at e ⊢; rw [e]⟩

/-- A geometric vector bundle is an affine morphism: over each `U_i` it is `𝔸ⁿ_{U_i} ⟶ U_i`. -/
theorem isAffineHom (G : GeometricVectorBundle f n) : IsAffineHom f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsAffineHom) G.U G.iSup_eq_top]
  intro i
  rw [← G.ψ_over i]
  infer_instance

lemma isLinearTransition_chart (G : GeometricVectorBundle f n) (i j : G.ι) (V : Y.affineOpens)
    (hi : (V : Y.Opens) ≤ G.U i) (hj : (V : Y.Opens) ≤ G.U j) :
    IsLinearTransition V hi hj (G.chart i) (G.chart j) :=
  G.linear i j V hi hj

/-! ### The union of two bundle structures -/

section Union

variable (G G'' : GeometricVectorBundle f n)

/-- The union `{U_i} ∪ {U''_j}` of the coverings of two bundle structures on `X`. -/
def unionU : G.ι ⊕ G''.ι → Y.Opens := Sum.elim G.U G''.U

/-- The trivializations of both bundle structures, indexed by the union of the coverings. -/
def unionψ : ∀ a : G.ι ⊕ G''.ι,
    (f ⁻¹ᵁ unionU G G'' a).toScheme ≅ 𝔸(ULift.{u} (Fin n); unionU G G'' a)
  | .inl i => G.ψ i
  | .inr j => G''.ψ j

/-- **Compatible bundle structures**: two geometric vector bundle structures of rank `n` on
`f : X ⟶ Y` are compatible if the union of their coverings, with all their trivializations,
satisfies the linearity condition of Exercise 5.18, that is, together they form a geometric vector
bundle structure on `X` (`GeometricVectorBundle.union`). -/
def Compatible : Prop :=
  ∀ (a b : G.ι ⊕ G''.ι) (V : Y.affineOpens) (ha : (V : Y.Opens) ≤ unionU G G'' a)
    (hb : (V : Y.Opens) ≤ unionU G G'' b),
    IsLinearTransition V ha hb ((unionψ G G'' a).inv ≫ (f ⁻¹ᵁ unionU G G'' a).ι)
      ((unionψ G G'' b).inv ≫ (f ⁻¹ᵁ unionU G G'' b).ι)

/-- **The union of two compatible bundle structures**: the geometric vector bundle structure on
`X` given by the union of the coverings and all the trivializations. -/
def union (h : Compatible G G'') : GeometricVectorBundle f n where
  ι := G.ι ⊕ G''.ι
  U := unionU G G''
  iSup_eq_top := top_le_iff.mp (G.iSup_eq_top ▸ iSup_le fun i => le_iSup (unionU G G'') (.inl i))
  ψ := unionψ G G''
  ψ_over a := by
    cases a with
    | inl i => exact G.ψ_over i
    | inr j => exact G''.ψ_over j
  linear := h

end Union

/-! ### Transport of a bundle structure along an isomorphism -/

section Transport

variable (G' : GeometricVectorBundle f' n) (g : X ≅ X') (hg : g.hom ≫ f' = f)

private lemma preimage_eq_preimage (g : X ≅ X') (hg : g.hom ≫ f' = f) (U : Y.Opens) : f ⁻¹ᵁ U = g.hom ⁻¹ᵁ (f' ⁻¹ᵁ U) := by
  rw [← hg, Scheme.Hom.comp_preimage]

/-- The restriction `f⁻¹(U) ≅ f'⁻¹(U)` of an isomorphism `g : X ≅ X'` over `Y`. -/
def preimageRestrictIso (g : X ≅ X') (hg : g.hom ≫ f' = f) (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ≅ (f' ⁻¹ᵁ U).toScheme :=
  X.isoOfEq (preimage_eq_preimage g hg U) ≪≫ g.hom.preimageIso (f' ⁻¹ᵁ U)

@[reassoc]
lemma preimageRestrictIso_hom_ι (g : X ≅ X') (hg : g.hom ≫ f' = f) (U : Y.Opens) :
    (preimageRestrictIso g hg U).hom ≫ (f' ⁻¹ᵁ U).ι = (f ⁻¹ᵁ U).ι ≫ g.hom := by
  simp [preimageRestrictIso]

@[reassoc]
lemma preimageRestrictIso_inv_ι (g : X ≅ X') (hg : g.hom ≫ f' = f) (U : Y.Opens) :
    (preimageRestrictIso g hg U).inv ≫ (f ⁻¹ᵁ U).ι = (f' ⁻¹ᵁ U).ι ≫ g.inv := by
  rw [Iso.inv_comp_eq, preimageRestrictIso_hom_ι_assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The transported bundle structure**: for a geometric vector bundle structure
`(X', {U'_j}, {ψ'_j})` and an isomorphism `g : X ≅ X'` over `Y`, the structure on `X` with the
same covering and the trivializations `ψ'_j ∘ g`. -/
def transport : GeometricVectorBundle f n where
  ι := G'.ι
  U := G'.U
  iSup_eq_top := G'.iSup_eq_top
  ψ j := preimageRestrictIso g hg (G'.U j) ≪≫ G'.ψ j
  ψ_over j := by
    rw [← cancel_mono (G'.U j).ι, Iso.trans_hom, Category.assoc, Category.assoc,
      reassoc_of% (G'.ψ_over j)]
    simp only [morphismRestrict_ι]
    rw [preimageRestrictIso_hom_ι_assoc, hg]
  linear i j V hi hj := by
    obtain ⟨θ, hθ, e⟩ := G'.linear i j V hi hj
    refine ⟨θ, hθ, ?_⟩
    simp only [Iso.trans_inv, Category.assoc, preimageRestrictIso_inv_ι]
    simp only [← Category.assoc] at e ⊢
    rw [e]

lemma transport_chart (j : G'.ι) : (G'.transport g hg).chart j = G'.chart j ≫ g.inv := by
  simp only [chart, transport, Iso.trans_inv, Category.assoc, preimageRestrictIso_inv_ι]

end Transport

/-! ### Isomorphisms of geometric vector bundles -/

/-- **An isomorphism of geometric vector bundles** (Hartshorne II, Exercise 5.18): for geometric
vector bundle structures `G = (X, {U_i}, {ψ_i})` on `f : X ⟶ Y` and `G' = (X', {U'_j}, {ψ'_j})` on
`f' : X' ⟶ Y` of rank `n`, an isomorphism `g : X ≅ X'` over `Y` such that `X`, the union of the
coverings, and the trivializations `ψ_i` and `ψ'_j ∘ g` together form a geometric vector bundle
structure on `X`. -/
structure BundleIso (G : GeometricVectorBundle f n) (G' : GeometricVectorBundle f' n) where
  /-- The isomorphism `g : X ≅ X'`. -/
  iso : X ≅ X'
  over : iso.hom ≫ f' = f
  compatible : Compatible G (G'.transport iso over)

namespace BundleIso

/-- The identity isomorphism of a geometric vector bundle. -/
def refl (G : GeometricVectorBundle f n) : BundleIso G G where
  iso := Iso.refl X
  over := Category.id_comp f
  compatible a b V ha hb := by
    have hc : ∀ j, (G.transport (Iso.refl X) (Category.id_comp f)).chart j = G.chart j :=
      fun j => by rw [transport_chart, Iso.refl_inv, Category.comp_id]
    cases a with
    | inl i =>
      cases b with
      | inl j => exact G.linear i j V ha hb
      | inr j =>
        change IsLinearTransition V ha hb (G.chart i)
          ((G.transport (Iso.refl X) (Category.id_comp f)).chart j)
        rw [hc]; exact G.linear i j V ha hb
    | inr i =>
      cases b with
      | inl j =>
        change IsLinearTransition V ha hb
          ((G.transport (Iso.refl X) (Category.id_comp f)).chart i) (G.chart j)
        rw [hc]; exact G.linear i j V ha hb
      | inr j =>
        change IsLinearTransition V ha hb
          ((G.transport (Iso.refl X) (Category.id_comp f)).chart i)
          ((G.transport (Iso.refl X) (Category.id_comp f)).chart j)
        rw [hc, hc]; exact G.linear i j V ha hb

variable {G : GeometricVectorBundle f n} {G' : GeometricVectorBundle f' n}

lemma symm_over (e : BundleIso G G') : e.iso.symm.hom ≫ f = f' := by
  exact (Iso.inv_comp_eq e.iso).mpr e.over.symm

/-- The inverse of an isomorphism of geometric vector bundles. -/
def symm (e : BundleIso G G') : BundleIso G' G where
  iso := e.iso.symm
  over := e.symm_over
  compatible a b V ha hb := by
    have hc : ∀ i, (G.transport e.iso.symm e.symm_over).chart i = G.chart i ≫ e.iso.hom :=
      fun i => by rw [transport_chart, Iso.symm_inv]
    have hc' : ∀ j, (G'.transport e.iso e.over).chart j ≫ e.iso.hom = G'.chart j :=
      fun j => by rw [transport_chart, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        have := (e.compatible (.inr i) (.inr j) V ha hb).comp e.iso.hom
        change IsLinearTransition V ha hb ((G'.transport e.iso e.over).chart i ≫ e.iso.hom)
          ((G'.transport e.iso e.over).chart j ≫ e.iso.hom) at this
        rw [hc', hc'] at this
        exact this
      | inr j =>
        have := (e.compatible (.inr i) (.inl j) V ha hb).comp e.iso.hom
        change IsLinearTransition V ha hb ((G'.transport e.iso e.over).chart i ≫ e.iso.hom)
          (G.chart j ≫ e.iso.hom) at this
        rw [hc'] at this
        change IsLinearTransition V ha hb (G'.chart i)
          ((G.transport e.iso.symm e.symm_over).chart j)
        rw [hc]
        exact this
    | inr i =>
      cases b with
      | inl j =>
        have := (e.compatible (.inl i) (.inr j) V ha hb).comp e.iso.hom
        change IsLinearTransition V ha hb (G.chart i ≫ e.iso.hom)
          ((G'.transport e.iso e.over).chart j ≫ e.iso.hom) at this
        rw [hc'] at this
        change IsLinearTransition V ha hb ((G.transport e.iso.symm e.symm_over).chart i)
          (G'.chart j)
        rw [hc]
        exact this
      | inr j =>
        have := (e.compatible (.inl i) (.inl j) V ha hb).comp e.iso.hom
        change IsLinearTransition V ha hb ((G.transport e.iso.symm e.symm_over).chart i)
          ((G.transport e.iso.symm e.symm_over).chart j)
        rw [hc, hc]
        exact this

end BundleIso

/-! ### Invariance of the sheaf of sections -/

section Sections

open Hartshorne Hartshorne.Ringed

/-- A chart lift is determined by its two defining properties. -/
lemma chartLift_eq_of (G : GeometricVectorBundle f n) (i : G.ι) {V : Y.Opens} (hi : V ≤ G.U i)
    (s : V.toScheme ⟶ X) (hs : s ≫ f = V.ι) (t : V.toScheme ⟶ 𝔸(ULift.{u} (Fin n); V))
    (h₁ : t ≫ AffineSpace.map _ (Y.homOfLE hi) ≫ G.chart i = s)
    (h₂ : t ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V = 𝟙 _) : G.chartLift i hi s hs = t := by
  refine (AffineSpace.isPullback_map (Y.homOfLE hi)).hom_ext ?_ ?_
  · rw [← cancel_mono ((G.ψ i).inv ≫ (f ⁻¹ᵁ G.U i).ι), Category.assoc, G.chartLift_map,
      Category.assoc]
    exact h₁.symm
  · rw [chartLift_over, h₂]

section SameBase

variable (G₁ G₂ : GeometricVectorBundle f n)

/-- If the chart coordinates of `G₁` are additive for the addition of sections defined by `G₂`,
the two additions agree. -/
lemma secAdd_eq_of_coordY
    (hadd : ∀ (i : G₁.ι) {V : Y.Opens} (hi : V ≤ G₁.U i) (s t : (sectionsPresheaf f).obj (op V)),
      G₁.coordY i hi (G₂.secAdd s t) = G₁.coordY i hi s + G₁.coordY i hi t)
    {W : Y.Opens} (s t : (sectionsPresheaf f).obj (op W)) : G₂.secAdd s t = G₁.secAdd s t := by
  refine G₁.coords_injective W (funext fun p => ?_)
  rw [coords_secAdd, Pi.add_apply]
  let _ := G₂.addCommGroupSections W
  let _ := G₂.addCommGroupSections (p.V : Y.Opens)
  have h : (sectionsPresheaf f).map (homOfLE p.hW).op (G₂.secAdd s t) =
      G₂.secAdd ((sectionsPresheaf f).map (homOfLE p.hW).op s)
        ((sectionsPresheaf f).map (homOfLE p.hW).op t) :=
    (G₂.resHom (homOfLE p.hW).op).map_add s t
  rw [coords, h, hadd]
  rfl

/-- If the chart coordinates of `G₁` are linear for the multiplication of sections by functions
defined by `G₂`, the two multiplications agree. -/
lemma secSmul_eq_of_coordY
    (hsmul : ∀ (i : G₁.ι) {V : Y.Opens} (hi : V ≤ G₁.U i) (r : Γ(Y, V))
      (s : (sectionsPresheaf f).obj (op V)), G₁.coordY i hi (G₂.secSmul r s) = r • G₁.coordY i hi s)
    {W : Y.Opens} (r : Γ(Y, W)) (s : (sectionsPresheaf f).obj (op W)) :
    G₂.secSmul r s = G₁.secSmul r s := by
  refine G₁.coords_injective W (funext fun p => ?_)
  rw [coords_secSmul, coords, G₂.resHom_smul, hsmul]
  rfl

/-- Two bundle structures on the same `f` such that the chart coordinates of `G₁` are linear for
the operations of `G₂` define the same `𝒪_Y`-module of sections. -/
def sectionsModuleIsoOfCoordY
    (hadd : ∀ (i : G₁.ι) {V : Y.Opens} (hi : V ≤ G₁.U i) (s t : (sectionsPresheaf f).obj (op V)),
      G₁.coordY i hi (G₂.secAdd s t) = G₁.coordY i hi s + G₁.coordY i hi t)
    (hsmul : ∀ (i : G₁.ι) {V : Y.Opens} (hi : V ≤ G₁.U i) (r : Γ(Y, V))
      (s : (sectionsPresheaf f).obj (op V)), G₁.coordY i hi (G₂.secSmul r s) = r • G₁.coordY i hi s) :
    G₂.sectionsModule ≅ G₁.sectionsModule :=
  let φ : G₂.sectionsModule ⟶ G₁.sectionsModule := modulesHomMk (R := Y.sheaf)
    (fun W =>
      { toFun := fun s => (s : (sectionsPresheaf f).obj (op W))
        map_add' := fun s t => secAdd_eq_of_coordY G₁ G₂ hadd s t
        map_smul' := fun r s => secSmul_eq_of_coordY G₁ G₂ hsmul r s })
    (fun _ _ _ _ => rfl)
  haveI : IsIso φ := modules_isIso_of_locally_bijective _ fun _ =>
    ⟨⊤, _root_.trivial, fun _ _ => Function.bijective_id⟩
  asIso φ

end SameBase

/-- The sheaf of sections of a bundle structure agrees with that of its union with a compatible
one. -/
def unionSectionsModuleIsoLeft (G G'' : GeometricVectorBundle f n) (h : Compatible G G'') :
    (union G G'' h).sectionsModule ≅ G.sectionsModule :=
  sectionsModuleIsoOfCoordY G (union G G'' h)
    (fun i _ hi s t => (union G G'' h).coordY_secAdd (.inl i) hi s t)
    (fun i _ hi r s => (union G G'' h).coordY_secSmul (.inl i) hi r s)

/-- The sheaf of sections of a bundle structure agrees with that of its union with a compatible
one. -/
def unionSectionsModuleIsoRight (G G'' : GeometricVectorBundle f n) (h : Compatible G G'') :
    (union G G'' h).sectionsModule ≅ G''.sectionsModule :=
  sectionsModuleIsoOfCoordY G'' (union G G'' h)
    (fun j _ hj s t => (union G G'' h).coordY_secAdd (.inr j) hj s t)
    (fun j _ hj r s => (union G G'' h).coordY_secSmul (.inr j) hj r s)

section Transport

variable (G' : GeometricVectorBundle f' n) (g : X ≅ X') (hg : g.hom ≫ f' = f)

/-- The section `g ∘ s` of `f'` for a section `s` of `f`. -/
def pushSection {V : Y.Opens} (s : (sectionsPresheaf f).obj (op V)) :
    (sectionsPresheaf f').obj (op V) :=
  ⟨s.1 ≫ g.hom, by rw [Category.assoc, hg, s.2]⟩

lemma pushSection_map {V V' : Y.Opens} (i : op V ⟶ op V') (s : (sectionsPresheaf f).obj (op V)) :
    pushSection g hg ((sectionsPresheaf f).map i s) =
      (sectionsPresheaf f').map i (pushSection g hg s) :=
  Subtype.ext (Category.assoc _ _ _)

lemma transport_chartLift (j : G'.ι) {V : Y.Opens} (hj : V ≤ G'.U j) (s : V.toScheme ⟶ X)
    (hs : s ≫ f = V.ι) (hs' : (s ≫ g.hom) ≫ f' = V.ι) :
    (G'.transport g hg).chartLift j hj s hs = G'.chartLift j hj (s ≫ g.hom) hs' := by
  refine chartLift_eq_of (G'.transport g hg) j hj s hs (G'.chartLift j hj (s ≫ g.hom) hs') ?_
    (G'.chartLift_over j hj (s ≫ g.hom) hs')
  have h := G'.chartLift_map j hj (s ≫ g.hom) hs'
  have e := transport_chart G' g hg j
  simp only [chart] at e
  simp only [chart]
  rw [e]
  simp only [Category.assoc]
  rw [reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

lemma transport_coordY (j : G'.ι) {V : Y.Opens} (hj : V ≤ G'.U j)
    (s : (sectionsPresheaf f).obj (op V)) :
    (G'.transport g hg).coordY j hj s = G'.coordY j hj (pushSection g hg s) := by
  funext k
  simp only [coordY, chartCoord]
  rw [transport_chartLift G' g hg j hj s.1 s.2 (pushSection g hg s).2]
  rfl

lemma coords_pushSection {W : Y.Opens} (s : (sectionsPresheaf f).obj (op W))
    (p : G'.ChartPiece W) :
    G'.coords (pushSection g hg s) p =
      (G'.transport g hg).coordY p.i p.hi ((sectionsPresheaf f).map (homOfLE p.hW).op s) := by
  rw [coords, transport_coordY, pushSection_map]

lemma pushSection_secAdd {W : Y.Opens} (s t : (sectionsPresheaf f).obj (op W)) :
    pushSection g hg ((G'.transport g hg).secAdd s t) =
      G'.secAdd (pushSection g hg s) (pushSection g hg t) := by
  refine G'.coords_injective W (funext fun p => ?_)
  rw [coords_secAdd, Pi.add_apply, coords_pushSection, coords_pushSection, coords_pushSection,
    coordY_map_secAdd]

lemma pushSection_secSmul {W : Y.Opens} (r : Γ(Y, W)) (s : (sectionsPresheaf f).obj (op W)) :
    pushSection g hg ((G'.transport g hg).secSmul r s) =
      G'.secSmul r (pushSection g hg s) := by
  refine G'.coords_injective W (funext fun p => ?_)
  rw [coords_secSmul]
  dsimp only
  rw [coords_pushSection, coords_pushSection, coordY_map_secSmul]

lemma pushSection_bijective (W : Y.Opens) :
    Function.Bijective (pushSection (V := W) g hg) := by
  have hg' : g.inv ≫ f = f' := (Iso.inv_comp_eq g).mpr hg.symm
  refine Function.bijective_iff_has_inverse.mpr ⟨pushSection g.symm hg', fun s => ?_, fun s => ?_⟩
  · exact Subtype.ext (by simp [pushSection])
  · exact Subtype.ext (by simp [pushSection])

/-- **The sections of the transported bundle structure**: `s ↦ g ∘ s` is an isomorphism of
`𝒪_Y`-modules from the sheaf of sections of `X` with the trivializations `ψ'_j ∘ g` to the sheaf
of sections of `X'`. -/
def transportSectionsModuleIso :
    (G'.transport g hg).sectionsModule ≅ G'.sectionsModule :=
  let φ : (G'.transport g hg).sectionsModule ⟶ G'.sectionsModule := modulesHomMk (R := Y.sheaf)
    (fun W =>
      { toFun := fun s => pushSection g hg (s : (sectionsPresheaf f).obj (op W))
        map_add' := fun s t => pushSection_secAdd G' g hg s t
        map_smul' := fun r s => pushSection_secSmul G' g hg r s })
    (fun _ _ i s => pushSection_map g hg (homOfLE i).op s)
  haveI : IsIso φ := modules_isIso_of_locally_bijective _ fun _ =>
    ⟨⊤, _root_.trivial, fun W _ => pushSection_bijective g hg W⟩
  asIso φ

end Transport

/-- **Isomorphic geometric vector bundles have isomorphic sheaves of sections** (Hartshorne II,
Exercise 5.18): an isomorphism `g` of geometric vector bundles induces the isomorphism
`s ↦ g ∘ s` of their sheaves of sections as `𝒪_Y`-modules. -/
def BundleIso.sectionsModuleIso {G : GeometricVectorBundle f n} {G' : GeometricVectorBundle f' n}
    (e : BundleIso G G') : G.sectionsModule ≅ G'.sectionsModule :=
  (unionSectionsModuleIsoLeft G _ e.compatible).symm ≪≫
    unionSectionsModuleIsoRight G _ e.compatible ≪≫ transportSectionsModuleIso G' e.iso e.over

end Sections

/-! ### Composition of isomorphisms of geometric vector bundles -/

section Trans

lemma isLinearPolynomialAlgHom_comp {A : Type u} [CommRing A]
    {θ₁ θ₂ : MvPolynomial (ULift.{u} (Fin n)) A →ₐ[A] MvPolynomial (ULift.{u} (Fin n)) A}
    (h₁ : IsLinearPolynomialAlgHom θ₁) (h₂ : IsLinearPolynomialAlgHom θ₂) :
    IsLinearPolynomialAlgHom (θ₁.comp θ₂) := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  have hC : ∀ c, θ₁ (MvPolynomial.C c) = MvPolynomial.C c := θ₁.commutes
  refine ⟨b * a, fun k => ?_⟩
  rw [AlgHom.comp_apply, hb, map_sum]
  simp only [map_mul, hC, ha, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

lemma IsLinearTransition.trans {Z : Scheme.{u}} {V : Y.affineOpens} {U U' U'' : Y.Opens}
    {h : (V : Y.Opens) ≤ U} {h' : (V : Y.Opens) ≤ U'} {h'' : (V : Y.Opens) ≤ U''}
    {c : 𝔸(ULift.{u} (Fin n); U) ⟶ Z} {c' : 𝔸(ULift.{u} (Fin n); U') ⟶ Z}
    {c'' : 𝔸(ULift.{u} (Fin n); U'') ⟶ Z} (h₁ : IsLinearTransition V h h' c c')
    (h₂ : IsLinearTransition V h' h'' c' c'') : IsLinearTransition V h h'' c c'' := by
  obtain ⟨θ₁, hθ₁, e₁⟩ := h₁
  obtain ⟨θ₂, hθ₂, e₂⟩ := h₂
  refine ⟨θ₁.trans θ₂, isLinearPolynomialAlgHom_comp hθ₂ hθ₁, ?_⟩
  rw [e₂, e₁, ← Spec.map_comp_assoc]
  rfl

/-- The chart of affine space at an affine `W ⊆ V` through the chart at `V`. -/
@[reassoc]
lemma affineSpaceChart_restrict {U : Y.Opens} (V W : Y.affineOpens) (h : (V : Y.Opens) ≤ U)
    (hWV : (W : Y.Opens) ≤ V) :
    affineSpaceChart n W (hWV.trans h) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (Y.homOfLE hWV).appTop.hom)) ≫
        affineSpaceChart n V h := by
  simp only [affineSpaceChart]
  rw [← AffineSpace.isoOfIsAffine_inv_map_hom, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, ← AffineSpace.map_comp, Scheme.homOfLE_homOfLE]

private lemma isOpenImmersion_affineSpaceChart {U : Y.Opens} (V : Y.affineOpens)
    (h : (V : Y.Opens) ≤ U) : IsOpenImmersion (affineSpaceChart n V h) := by
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin n)) (Y.homOfLE h)) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) (Y.homOfLE h)).flip inferInstance
  unfold affineSpaceChart
  infer_instance

lemma chart_comp (G : GeometricVectorBundle f n) (i : G.ι) :
    G.chart i ≫ f = 𝔸(ULift.{u} (Fin n); G.U i) ↘ G.U i ≫ (G.U i).ι := by
  rw [chart, Category.assoc, ← morphismRestrict_ι, ← G.ψ_over, Category.assoc,
    Iso.inv_hom_id_assoc]

lemma affineSpaceChart_chart_comp (G : GeometricVectorBundle f n) (i : G.ι) (V : Y.affineOpens)
    (h : (V : Y.Opens) ≤ G.U i) :
    affineSpaceChart n V h ≫ G.chart i ≫ f =
      (AffineSpace.isoOfIsAffine _ (V : Y.Opens).toScheme).inv ≫
        𝔸(ULift.{u} (Fin n); V) ↘ V ≫ (V : Y.Opens).ι := by
  rw [chart_comp, affineSpaceChart, Category.assoc, AffineSpace.map_over_assoc,
    Scheme.homOfLE_ι]

/-- The chart of a bundle structure at an affine `V ⊆ U_i` is onto `f⁻¹(V)`. -/
private lemma range_affineSpaceChart_chart (G : GeometricVectorBundle f n) (i : G.ι)
    (V : Y.affineOpens) (h : (V : Y.Opens) ≤ G.U i) :
    Set.range (affineSpaceChart n V h ≫ G.chart i) = f ⁻¹' ((V : Y.Opens) : Set Y) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change (affineSpaceChart n V h ≫ G.chart i ≫ f) z ∈ (V : Y.Opens)
    rw [affineSpaceChart_chart_comp]
    exact Subtype.prop _
  · intro hx
    have hxU : x ∈ f ⁻¹ᵁ G.U i := h hx
    let w : (f ⁻¹ᵁ G.U i).toScheme := ⟨x, hxU⟩
    have hz : (𝔸(ULift.{u} (Fin n); G.U i) ↘ G.U i) ((G.ψ i).hom w) =
        Y.homOfLE h ⟨f x, hx⟩ := by
      rw [← Scheme.Hom.comp_apply, G.ψ_over]
      apply (G.U i).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      rfl
    obtain ⟨t, ht, -⟩ := Scheme.exists_preimage_of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) (Y.homOfLE h)) _ _ hz
    refine ⟨(AffineSpace.isoOfIsAffine _ (V : Y.Opens).toScheme).hom t, ?_⟩
    rw [affineSpaceChart, chart, ← Scheme.Hom.comp_apply]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [Scheme.Hom.comp_apply, ht, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    rfl

private lemma coeff_single_linear {A : Type u} [CommRing A] (b : ULift.{u} (Fin n) → A)
    (l : ULift.{u} (Fin n)) :
    MvPolynomial.coeff (Finsupp.single l 1) (∑ m, MvPolynomial.C (b m) * MvPolynomial.X m) =
      b l := by
  classical
  simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
    Finsupp.single_left_inj]

/-- Polynomials over `Γ(V, 𝒪)` whose images over the members of an open covering of `V` agree are
equal. -/
private lemma eq_of_locally_map (V : Y.affineOpens)
    (p p' : MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤))
    (h : ∀ y ∈ (V : Y.Opens), ∃ (W : Y.Opens) (hWV : W ≤ V), y ∈ W ∧
      MvPolynomial.map (Y.homOfLE hWV).appTop.hom p =
        MvPolynomial.map (Y.homOfLE hWV).appTop.hom p') : p = p' := by
  ext m
  apply (ConcreteCategory.bijective_of_isIso (V : Y.Opens).topIso.hom).1
  choose W hWV hyW hW using h
  refine Y.sheaf.eq_of_locally_eq' (fun y : (V : Y.Opens) => W y.1 y.2) V
    (fun y => homOfLE (hWV y.1 y.2)) (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyW _ _⟩) _ _
    fun y => ?_
  have e := congrArg (MvPolynomial.coeff m) (hW y.1 y.2)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at e
  change Y.presheaf.map _ ((V : Y.Opens).topIso.hom _) =
    Y.presheaf.map _ ((V : Y.Opens).topIso.hom _)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Scheme.Modules.homOfLE_appTop_topIso_hom, CommRingCat.comp_apply, CommRingCat.comp_apply]
  exact congrArg _ e

/-- **Linearity of transitions is local**: for two bundle structures on `f`, charts `i`, `k` and an
affine `V ⊆ U_i ∩ U''_k`, if every point of `V` has an affine neighbourhood `W ⊆ V` on which the
transition is linear, then the transition is linear on `V`. -/
theorem isLinearTransition_of_locally (G₁ G₂ : GeometricVectorBundle f n) (i : G₁.ι) (k : G₂.ι)
    (V : Y.affineOpens) (h₁ : (V : Y.Opens) ≤ G₁.U i) (h₂ : (V : Y.Opens) ≤ G₂.U k)
    (hloc : ∀ y ∈ (V : Y.Opens), ∃ (W : Y.affineOpens) (hWV : (W : Y.Opens) ≤ V),
      y ∈ (W : Y.Opens) ∧
        IsLinearTransition W (hWV.trans h₁) (hWV.trans h₂) (G₁.chart i) (G₂.chart k)) :
    IsLinearTransition V h₁ h₂ (G₁.chart i) (G₂.chart k) := by
  set c₁ := affineSpaceChart n V h₁ ≫ G₁.chart i with hc₁
  set c₂ := affineSpaceChart n V h₂ ≫ G₂.chart k with hc₂
  have : IsOpenImmersion (affineSpaceChart n V h₁) := isOpenImmersion_affineSpaceChart V h₁
  have : IsOpenImmersion (affineSpaceChart n V h₂) := isOpenImmersion_affineSpaceChart V h₂
  have : IsOpenImmersion c₁ := by rw [hc₁, chart]; infer_instance
  have : IsOpenImmersion c₂ := by rw [hc₂, chart]; infer_instance
  have r : Set.range c₁ = Set.range c₂ := by
    rw [hc₁, hc₂, range_affineSpaceChart_chart, range_affineSpaceChart_chart]
  let φ := IsOpenImmersion.lift c₁ c₂ r.ge
  let ψ := IsOpenImmersion.lift c₂ c₁ r.le
  have hφ : φ ≫ c₁ = c₂ := IsOpenImmersion.lift_fac _ _ _
  have hψ : ψ ≫ c₂ = c₁ := IsOpenImmersion.lift_fac _ _ _
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    rw [← cancel_mono c₁, Category.assoc, hφ, hψ, Category.id_comp]
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    rw [← cancel_mono c₂, Category.assoc, hψ, hφ, Category.id_comp]
  set θ₀ := Spec.preimage φ with hθ₀
  set θ₀' := Spec.preimage ψ
  have e₁ : θ₀ ≫ θ₀' = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, hψφ, Spec.map_id])
  have e₂ : θ₀' ≫ θ₀ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, hφψ, Spec.map_id])
  -- `φ` lies over `Spec Γ(V, 𝒪)`
  have hover : φ ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
    have h0 : c₁ ≫ f = c₂ ≫ f := by
      rw [hc₁, hc₂, Category.assoc, Category.assoc, affineSpaceChart_chart_comp,
        affineSpaceChart_chart_comp]
    have h1 : φ ≫ c₁ ≫ f = c₁ ≫ f := by rw [← Category.assoc, hφ, h0]
    rw [hc₁, Category.assoc, affineSpaceChart_chart_comp,
      AffineSpace.isoOfIsAffine_inv_over_assoc] at h1
    rw [← cancel_mono ((V : Y.Opens).toScheme.isoSpec.inv ≫ (V : Y.Opens).ι)]
    simpa only [Category.assoc] using h1
  have hC : ∀ a, θ₀.hom (MvPolynomial.C a) = MvPolynomial.C a := by
    have : CommRingCat.ofHom MvPolynomial.C ≫ θ₀ = CommRingCat.ofHom MvPolynomial.C :=
      Spec.map_injective (by rw [Spec.map_comp, hθ₀, Spec.map_preimage, hover])
    exact fun a => congrArg (fun g => g.hom a) this
  let θR : MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) ≃+* MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) :=
    (⟨θ₀, θ₀', e₁, e₂⟩ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤)) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤))).commRingCatIsoToRingEquiv
  let θ : MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) ≃ₐ[Γ(V, ⊤)]
      MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) := AlgEquiv.ofRingEquiv (f := θR) hC
  have hθφ : Spec.map (CommRingCat.ofHom θ.toRingEquiv.toRingHom) = φ := by
    rw [← Spec.map_preimage φ]
    rfl
  refine ⟨θ, ?_, by rw [hθφ]; exact hφ.symm⟩
  refine ⟨fun k' l => MvPolynomial.coeff (Finsupp.single l 1) (θ₀.hom (MvPolynomial.X k')),
    fun k' => ?_⟩
  change θ₀.hom (MvPolynomial.X k') = _
  refine eq_of_locally_map V _ _ fun y hy => ?_
  obtain ⟨W, hWV, hyW, θW, ⟨aW, haW⟩, eW⟩ := hloc y hy
  refine ⟨W, hWV, hyW, ?_⟩
  have key : θ₀ ≫ CommRingCat.ofHom (MvPolynomial.map (Y.homOfLE hWV).appTop.hom) =
      CommRingCat.ofHom (MvPolynomial.map (Y.homOfLE hWV).appTop.hom) ≫
        CommRingCat.ofHom θW.toRingEquiv.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hθ₀, Spec.map_preimage, ← cancel_mono c₁, Category.assoc,
      hφ, Category.assoc, hc₁, hc₂, ← affineSpaceChart_restrict_assoc, eW,
      affineSpaceChart_restrict_assoc]
  have k1 : MvPolynomial.map (Y.homOfLE hWV).appTop.hom (θ₀.hom (MvPolynomial.X k')) =
      ∑ l, MvPolynomial.C (aW k' l) * MvPolynomial.X l := by
    have := congrArg (fun g => g.hom (MvPolynomial.X k')) key
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      MvPolynomial.map_X] at this
    rw [this]
    exact haW k'
  rw [k1, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, ← MvPolynomial.coeff_map, k1,
    coeff_single_linear]

end Trans

namespace BundleIso

variable {X'' : Scheme.{u}} {f'' : X'' ⟶ Y} {G : GeometricVectorBundle f n}
  {G' : GeometricVectorBundle f' n} {G'' : GeometricVectorBundle f'' n}

/-- Every point of an open `V ⊆ Y` has an affine neighbourhood inside `V` and inside a member of
the covering of a bundle structure. -/
private lemma exists_affine_chart (G' : GeometricVectorBundle f' n) {V : Y.Opens} {y : Y}
    (hy : y ∈ V) : ∃ (j : G'.ι) (W : Y.affineOpens), (W : Y.Opens) ≤ V ∧
      y ∈ (W : Y.Opens) ∧ (W : Y.Opens) ≤ G'.U j := by
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (G'.iSup_eq_top.ge (Set.mem_univ y))
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (u := (V ⊓ G'.U j : Y.Opens))
      ⟨hy, hj⟩ (V ⊓ G'.U j).isOpen
  exact ⟨j, ⟨W, hW⟩, fun x hx => (hWle hx).1, hyW, fun x hx => (hWle hx).2⟩

lemma trans_over (e₁ : BundleIso G G') (e₂ : BundleIso G' G'') :
    (e₁.iso ≪≫ e₂.iso).hom ≫ f'' = f := by
  rw [Iso.trans_hom, Category.assoc, e₂.over, e₁.over]

/-- **The composite of two isomorphisms of geometric vector bundles** is an isomorphism of
geometric vector bundles: on an affine `V ⊆ U_i ∩ U''_k`, the transition is linear near every
point, as the composite of two linear transitions through a chart of the middle bundle, hence
linear on `V` (`isLinearTransition_of_locally`). -/
def trans (e₁ : BundleIso G G') (e₂ : BundleIso G' G'') : BundleIso G G'' where
  iso := e₁.iso ≪≫ e₂.iso
  over := trans_over e₁ e₂
  compatible a b V ha hb := by
    have hc : ∀ k, (G''.transport (e₁.iso ≪≫ e₂.iso) (trans_over e₁ e₂)).chart k =
        (G''.chart k ≫ e₂.iso.inv) ≫ e₁.iso.inv := fun k => by
      rw [transport_chart, Iso.trans_inv, Category.assoc]
    have hc₁ : ∀ j, (G'.transport e₁.iso e₁.over).chart j = G'.chart j ≫ e₁.iso.inv :=
      transport_chart G' e₁.iso e₁.over
    have hc₂ : ∀ k, (G''.transport e₂.iso e₂.over).chart k = G''.chart k ≫ e₂.iso.inv :=
      transport_chart G'' e₂.iso e₂.over
    cases a with
    | inl i =>
      cases b with
      | inl j => exact G.linear i j V ha hb
      | inr k =>
        change IsLinearTransition V ha hb (G.chart i)
          ((G''.transport (e₁.iso ≪≫ e₂.iso) (trans_over e₁ e₂)).chart k)
        refine isLinearTransition_of_locally G _ i k V ha hb fun y hy => ?_
        obtain ⟨j, W, hWV, hyW, hWj⟩ := exists_affine_chart G' hy
        refine ⟨W, hWV, hyW, ?_⟩
        have t₁ := e₁.compatible (.inl i) (.inr j) W (hWV.trans ha) hWj
        change IsLinearTransition W _ _ (G.chart i)
          ((G'.transport e₁.iso e₁.over).chart j) at t₁
        have t₂ := (e₂.compatible (.inl j) (.inr k) W hWj (hWV.trans hb)).comp e₁.iso.inv
        change IsLinearTransition W _ _ (G'.chart j ≫ e₁.iso.inv)
          ((G''.transport e₂.iso e₂.over).chart k ≫ e₁.iso.inv) at t₂
        rw [hc₁] at t₁
        rw [hc₂] at t₂
        rw [hc]
        exact t₁.trans t₂
    | inr k =>
      cases b with
      | inl i =>
        change IsLinearTransition V ha hb
          ((G''.transport (e₁.iso ≪≫ e₂.iso) (trans_over e₁ e₂)).chart k) (G.chart i)
        refine isLinearTransition_of_locally _ G k i V ha hb fun y hy => ?_
        obtain ⟨j, W, hWV, hyW, hWj⟩ := exists_affine_chart G' hy
        refine ⟨W, hWV, hyW, ?_⟩
        have t₁ := e₁.compatible (.inr j) (.inl i) W hWj (hWV.trans hb)
        change IsLinearTransition W _ _ ((G'.transport e₁.iso e₁.over).chart j)
          (G.chart i) at t₁
        have t₂ := (e₂.compatible (.inr k) (.inl j) W (hWV.trans ha) hWj).comp e₁.iso.inv
        change IsLinearTransition W _ _ ((G''.transport e₂.iso e₂.over).chart k ≫ e₁.iso.inv)
          (G'.chart j ≫ e₁.iso.inv) at t₂
        rw [hc₁] at t₁
        rw [hc₂] at t₂
        rw [hc]
        exact t₂.trans t₁
      | inr k' =>
        exact (G''.transport (e₁.iso ≪≫ e₂.iso) (trans_over e₁ e₂)).linear k k' V ha hb

end BundleIso

/-! ### Isomorphism classes -/

variable (Y n) in
/-- A geometric vector bundle of rank `n` over `Y`: a scheme over `Y` together with a geometric
vector bundle structure of rank `n`. -/
abbrev Bundled := Σ X : Over Y, GeometricVectorBundle X.hom n

variable (Y n) in
/-- Being isomorphic as geometric vector bundles is an equivalence relation. -/
instance isoSetoid : Setoid (Bundled Y n) where
  r B B' := Nonempty (BundleIso B.2 B'.2)
  iseqv :=
    { refl := fun B => ⟨BundleIso.refl B.2⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩ }

variable (Y n) in
/-- **Isomorphism classes of geometric vector bundles of rank `n` over `Y`** (Hartshorne II,
Exercise 5.18). -/
abbrev IsoClasses := Quotient (isoSetoid Y n)

end GeometricVectorBundle


/-! ### Isomorphism classes of locally free sheaves -/

namespace Scheme.Modules

open Hartshorne Hartshorne.Ringed

variable (Y n) in
/-- Locally free `𝒪_Y`-modules of rank `n`. -/
abbrev LocallyFreeOfRank := {E : Y.Modules // E.IsLocallyFreeOfRank n}

variable (Y n) in
/-- Isomorphism of `𝒪_Y`-modules, on locally free modules of rank `n`. -/
instance locallyFreeIsoSetoid : Setoid (LocallyFreeOfRank Y n) where
  r E E' := Nonempty (E.1 ≅ E'.1)
  iseqv :=
    { refl := fun _ => ⟨Iso.refl _⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁ ≪≫ e₂⟩ }

variable (Y n) in
/-- **Isomorphism classes of locally free `𝒪_Y`-modules of rank `n`.** -/
abbrev LocallyFreeIsoClasses := Quotient (locallyFreeIsoSetoid Y n)

/-- The dual of a locally free module of rank `n` is locally free of rank `n`. -/
private lemma isLocallyFreeOfRank_moduleSheafDual {E : Y.Modules} (hE : E.IsLocallyFreeOfRank n) :
    Scheme.Modules.IsLocallyFreeOfRank (moduleSheafDual (R := Y.sheaf) E) n := by
  classical
  rw [isLocallyFreeOfRank_iff_ringed] at hE ⊢
  intro x
  obtain ⟨U, hx, ⟨α⟩⟩ := hE x
  exact ⟨U, hx, nonempty_over_iso_free_of_isLocalFrame (isLocalFrame_of_over_iso α).dual⟩

end Scheme.Modules

namespace GeometricVectorBundle

open Hartshorne Hartshorne.Ringed Scheme.Modules

/-- **The class of the dual of the sheaf of sections** (Hartshorne II, Exercise 5.18(d)): the map
sending the class of a geometric vector bundle `X` of rank `n` to the class of the locally free
sheaf `𝒮(X/Y)^∨` of rank `n`. It is well defined since isomorphic bundles have isomorphic sheaves
of sections (`BundleIso.sectionsModuleIso`). -/
def sectionsDualClass : IsoClasses Y n → LocallyFreeIsoClasses Y n :=
  Quotient.map
    (fun B => ⟨moduleSheafDual (R := Y.sheaf) B.2.sectionsModule,
      isLocallyFreeOfRank_moduleSheafDual B.2.sectionsModule_isLocallyFreeOfRank⟩)
    (fun _ _ ⟨e⟩ => ⟨moduleSheafDualIsoOfIso e.sectionsModuleIso⟩)

/-- **`V(E)` is sent back to `E`** (Hartshorne II, Exercise 5.18(d)): the dual of the sheaf of
sections of `V(E)` is `(E^∨)^∨ ≅ E`. -/
theorem sectionsDualClass_vectorBundle (E : Y.Modules) (hE : E.IsLocallyFreeOfRank n) :
    sectionsDualClass (Quotient.mk _ ⟨Over.mk (vectorBundleProj E hE), vectorBundleAtlas hE⟩) =
      Quotient.mk _ ⟨E, hE⟩ :=
  Quotient.sound ⟨moduleSheafDualIsoOfIso (vectorBundleSectionsModuleIso hE) ≪≫
    (moduleSheafDoubleDualIso E
      ((isLocallyFreeOfRank_iff_ringed E n).mp hE).isFiniteLocallyFree).symm⟩

/-- Every isomorphism class of locally free sheaves of rank `n` is the class of the dual of the
sheaf of sections of a geometric vector bundle, namely of `V(E)`. -/
theorem sectionsDualClass_surjective :
    Function.Surjective (sectionsDualClass : IsoClasses Y n → LocallyFreeIsoClasses Y n) :=
  fun q => Quotient.inductionOn q fun E => ⟨_, sectionsDualClass_vectorBundle E.1 E.2⟩

end GeometricVectorBundle


/-! ### Functoriality of `V` in isomorphisms -/

namespace Scheme.Modules

open Hartshorne Hartshorne.SheafAlgebraOperations Hartshorne.SheafTensorOperations
  Hartshorne.ModuleSheafAlgebra

section QuasiCoherentAlgebraIso

variable {M M' : Y.Modules} {S : ModuleSheafAlgebra (R := Y.sheaf) M}
  {S' : ModuleSheafAlgebra (R := Y.sheaf) M'} (hS : S.IsCommutative) (hS' : S'.IsCommutative)
  (e : M ≅ M')
  (hmul : ∀ U a b, e.hom.val.app U (S.mul.app U a b) =
    S'.mul.app U (e.hom.val.app U a) (e.hom.val.app U b))
  (hone : ∀ U, e.hom.val.app U (S.one U) = S'.one U)

/-- A multiplicative and unital isomorphism of commutative sheaves of algebras, on rings of
sections. -/
def sectionsRingEquiv (U : Y.Opens) : sectionsRing hS U ≃+* sectionsRing hS' U where
  toFun a := toSectionsRing hS' (e.hom.val.app (op U) (ofSectionsRing hS a))
  invFun a := toSectionsRing hS (e.inv.val.app (op U) (ofSectionsRing hS' a))
  left_inv a := by
    change (e.hom ≫ e.inv).val.app (op U) a = a
    rw [e.hom_inv_id]
    rfl
  right_inv a := by
    change (e.inv ≫ e.hom).val.app (op U) a = a
    rw [e.inv_hom_id]
    rfl
  map_mul' a b := hmul (op U) a b
  map_add' a b := map_add (e.hom.val.app (op U)).hom a b

lemma sectionsRingEquiv_apply (U : Y.Opens) (a : Γ(M, U)) :
    sectionsRingEquiv hS hS' e hmul U (toSectionsRing hS a) =
      toSectionsRing hS' (e.hom.val.app (op U) a) := rfl

variable [M.IsQuasicoherent] [M'.IsQuasicoherent]

open Scheme.AffineZariskiSite in
/-- The natural isomorphism of the rings of sections over the affine opens. -/
def sectionsFunctorIso : sectionsFunctor hS ≅ sectionsFunctor hS' :=
  NatIso.ofComponents
    (fun U => (sectionsRingEquiv hS hS' e hmul ((toOpensFunctor Y).obj U.unop)).toCommRingCatIso)
    (fun {U V} i => by
      ext a
      exact PresheafOfModules.naturality_apply e.hom.val ((toOpensFunctor Y).map i.unop).op
        (ofSectionsRing hS a))

include hone in
/-- **A multiplicative and unital isomorphism of commutative sheaves of algebras on
quasi-coherent modules is an isomorphism of quasi-coherent algebras.** -/
def toQuasiCoherentAlgebraIso : toQuasiCoherentAlgebra hS ≅ toQuasiCoherentAlgebra hS' :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (Under.isoMk (sectionsFunctorIso hS hS' e hmul) (by
      ext U r
      let W : Y.Opens := (Scheme.AffineZariskiSite.toOpensFunctor Y).obj U.unop
      change e.hom.val.app (op W) ((show Γ(Y, W) from r) • oneSection S W) =
        (show Γ(Y, W) from r) • oneSection S' W
      rw [(e.hom.val.app (op W)).hom.map_smul]
      exact congrArg ((show Γ(Y, W) from r) • ·) (hone _)))

end QuasiCoherentAlgebraIso


section SymmetricAlgebraIso

variable {E E' E'' : Y.Modules}

/-- `E` as a sheaf of modules over the ringed space of `Y`. -/
private abbrev ringedModule (E : Y.Modules) : SheafOfModules.{u} (ringCatSheafOf Y.sheaf) := E

/-- `α` as a morphism of sheaves of modules over the ringed space of `Y`. -/
private abbrev ringedHom (α : E ⟶ E') : ringedModule E ⟶ ringedModule E' := α

/-- `Sym(α)` on the presheaf `U ↦ Sym(E(U))`, for a morphism `α : E ⟶ E'`. -/
def symmetricAlgebraPresheafMap (α : E ⟶ E') :
    moduleSheafSymmetricAlgebraPresheaf (R := Y.sheaf) E ⟶
      moduleSheafSymmetricAlgebraPresheaf (R := Y.sheaf) E' where
  app U := ModuleCat.ofHom (symmetricAlgebraMap (RingHom.id _) ((ringedHom α).val.app U).hom)
  naturality {U V} i := by
    ext x
    have h1 := symmetricAlgebraMap_comp (fun _ => rfl) ((ringedHom α).val.app U).hom
      ((ringedModule E').val.restrictₛₗ i)
      (((ringedModule E').val.restrictₛₗ i).comp ((ringedHom α).val.app U).hom) (fun _ => rfl) x
    have h2 := symmetricAlgebraMap_comp (fun _ => rfl) ((ringedModule E).val.restrictₛₗ i)
      ((ringedHom α).val.app V).hom
      (((ringedModule E').val.restrictₛₗ i).comp ((ringedHom α).val.app U).hom)
      (fun m => (PresheafOfModules.naturality_apply (ringedHom α).val i m).symm) x
    exact h2.symm.trans h1

lemma symmetricAlgebraPresheafMap_comp (α : E ⟶ E') (β : E' ⟶ E'') :
    symmetricAlgebraPresheafMap (α ≫ β) =
      symmetricAlgebraPresheafMap α ≫ symmetricAlgebraPresheafMap β := by
  ext U x
  exact symmetricAlgebraMap_comp (fun _ => rfl) _ _ _ (fun _ => rfl) x

lemma symmetricAlgebraPresheafMap_id :
    symmetricAlgebraPresheafMap (𝟙 E) = 𝟙 _ := by
  ext U x
  exact symmetricAlgebraMap_id (fun _ => rfl) _ (fun _ => rfl) x

/-- `Sym(α)` on presheaves, for an isomorphism `α : E ≅ E'`. -/
def symmetricAlgebraPresheafIso (α : E ≅ E') :
    moduleSheafSymmetricAlgebraPresheaf (R := Y.sheaf) E ≅
      moduleSheafSymmetricAlgebraPresheaf (R := Y.sheaf) E' where
  hom := symmetricAlgebraPresheafMap α.hom
  inv := symmetricAlgebraPresheafMap α.inv
  hom_inv_id := by
    rw [← symmetricAlgebraPresheafMap_comp, α.hom_inv_id, symmetricAlgebraPresheafMap_id]
  inv_hom_id := by
    rw [← symmetricAlgebraPresheafMap_comp, α.inv_hom_id, symmetricAlgebraPresheafMap_id]

/-- **`Sym(α) : Sym(E) ≅ Sym(E')`** for an isomorphism `α : E ≅ E'`, the sheafification of
`Sym(α(U)) : Sym(E(U)) ≅ Sym(E'(U))`. -/
def symmetricAlgebraIso (α : E ≅ E') : E.symmetricAlgebra ≅ E'.symmetricAlgebra :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).mapIso
    (symmetricAlgebraPresheafIso α)

lemma symmetricAlgebraIso_hom_mul (α : E ≅ E') (U : Y.Opensᵒᵖ)
    (a b : E.symmetricAlgebra.val.obj U) :
    (symmetricAlgebraIso α).hom.val.app U (E.symmetricAlgebraStructure.mul.app U a b) =
      E'.symmetricAlgebraStructure.mul.app U ((symmetricAlgebraIso α).hom.val.app U a)
        ((symmetricAlgebraIso α).hom.val.app U b) :=
  PresheafAlgebra.sheafifyMap_mul _ _ _ (fun _ x y => symmetricAlgebraMap_mul _ _ x y) U a b

lemma symmetricAlgebraIso_hom_one (α : E ≅ E') (U : Y.Opensᵒᵖ) :
    (symmetricAlgebraIso α).hom.val.app U (E.symmetricAlgebraStructure.one U) =
      E'.symmetricAlgebraStructure.one U :=
  PresheafAlgebra.sheafifyMap_one _ _ _
    (fun _ => map_one (symmetricAlgebraRingHom (RingHom.id _) _)) U

lemma symmetricAlgebraIso_hom_symDegreeOne (α : E ≅ E') (U : Y.Opens) (m : Γ(E, U)) :
    (symmetricAlgebraIso α).hom.val.app (op U) (ofSectionsRing _ (E.symDegreeOne U m)) =
      ofSectionsRing _ (E'.symDegreeOne U (α.hom.val.app (op U) m)) :=
  (sheafifyMap_unit _ (op U) _).trans
    (congrArg _ (symmetricAlgebraRingHom_ι (RingHom.id _)
      ((ringedHom α.hom).val.app (op U)).hom (show (ringedModule E).val.obj (op U) from m)))

variable (hE : E.IsLocallyFreeOfRank n) (hE' : E'.IsLocallyFreeOfRank n)

/-- **`Sym(α)` as an isomorphism of quasi-coherent `𝒪_Y`-algebras**, for an isomorphism
`α : E ≅ E'` of locally free sheaves of rank `n`. -/
def symmetricQuasiCoherentAlgebraIso (α : E ≅ E') :
    symmetricQuasiCoherentAlgebra E hE ≅ symmetricQuasiCoherentAlgebra E' hE' :=
  haveI := symmetricAlgebra_isQuasicoherent_of_isLocallyFreeOfRank hE
  haveI := symmetricAlgebra_isQuasicoherent_of_isLocallyFreeOfRank hE'
  toQuasiCoherentAlgebraIso _ _ (symmetricAlgebraIso α) (symmetricAlgebraIso_hom_mul α)
    (symmetricAlgebraIso_hom_one α)

/-- **`V(α) : V(E) ≅ V(E')`** for an isomorphism `α : E ≅ E'` of locally free sheaves of rank
`n`: the isomorphism of relative spectra induced by `Sym(α)`. -/
def vectorBundleIso (α : E ≅ E') : vectorBundle E hE ≅ vectorBundle E' hE' :=
  QuasiCoherentAlgebra.relSpecIso (symmetricQuasiCoherentAlgebraIso hE hE' α)

lemma vectorBundleIso_hom_proj (α : E ≅ E') :
    (vectorBundleIso hE hE' α).hom ≫ vectorBundleProj E' hE' = vectorBundleProj E hE :=
  QuasiCoherentAlgebra.relSpecIso_hom_relSpecToBase _

end SymmetricAlgebraIso


/-! ### `V(α)` is an isomorphism of geometric vector bundles -/

section VectorBundleBundleIso

variable {E E' : Y.Modules}

private lemma relSpecIso_ι_hom {A B : QuasiCoherentAlgebra Y} (e : A ≅ B)
    (U : Y.AffineZariskiSite) :
    A.ι U ≫ (QuasiCoherentAlgebra.relSpecIso e).hom =
      Spec.map ((QuasiCoherentAlgebra.sectionsIso e).inv.app (op U)) ≫ B.ι U :=
  CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom _ _

private lemma relSpecIso_ι_inv {A B : QuasiCoherentAlgebra Y} (e : A ≅ B)
    (U : Y.AffineZariskiSite) :
    B.ι U ≫ (QuasiCoherentAlgebra.relSpecIso e).inv =
      Spec.map ((QuasiCoherentAlgebra.sectionsIso e).hom.app (op U)) ≫ A.ι U :=
  CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_inv _ _

/-- The change of charts `φ_{e'}⁻¹ ∘ s ∘ φ_e` between frames `e` of `E` and `e'` of `E'` over an
affine open, through a ring isomorphism `s : Γ(V, Sym(E)) ≅ Γ(V, Sym(E'))` of
`Γ(V, 𝒪_Y)`-algebras. -/
private def chartChange {V : Y.affineOpens} {e : ULift.{u} (Fin n) → Γ(E, V)}
    (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e) {e' : ULift.{u} (Fin n) → Γ(E', V)}
    (he' : Ringed.IsLocalFrame (R := Y.sheaf) E' V e')
    (s : E.symSections V ≃+* E'.symSections V)
    (hs : ∀ r, s (unitRingHom E.symmetricAlgebraStructure_isCommutative V r) =
      unitRingHom E'.symmetricAlgebraStructure_isCommutative V r) :
    MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) ≃ₐ[Γ(V, ⊤)] MvPolynomial (ULift.{u} (Fin n)) Γ(V, ⊤) :=
  AlgEquiv.ofRingEquiv
    (f := ((frameChartRingEquiv V he).trans s).trans (frameChartRingEquiv V he').symm) fun a => by
      rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
      change s (E.chartRingHom V e (MvPolynomial.map (V : Y.Opens).topIso.hom.hom
        (MvPolynomial.C a))) = E'.chartRingHom V e' (MvPolynomial.map (V : Y.Opens).topIso.hom.hom
          (MvPolynomial.C a))
      rw [MvPolynomial.map_C, chartRingHom_C, chartRingHom_C, hs]

private lemma isLinearPolynomialAlgHom_chartChange {V : Y.affineOpens}
    {e : ULift.{u} (Fin n) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := Y.sheaf) E V e)
    {e' : ULift.{u} (Fin n) → Γ(E', V)} (he' : Ringed.IsLocalFrame (R := Y.sheaf) E' V e')
    (s : E.symSections V ≃+* E'.symSections V)
    (hs : ∀ r, s (unitRingHom E.symmetricAlgebraStructure_isCommutative V r) =
      unitRingHom E'.symmetricAlgebraStructure_isCommutative V r) (β : Γ(E, V) → Γ(E', V))
    (hβ : ∀ m, s (E.symDegreeOne V m) = E'.symDegreeOne V (β m)) :
    IsLinearPolynomialAlgHom (chartChange he he' s hs).toAlgHom := by
  obtain ⟨a, ha⟩ := E'.chartRingHom_transition he' (fun k => β (e k))
  refine ⟨fun k l => (V : Y.Opens).topIso.inv (a k l), fun k => ?_⟩
  change (frameChartRingEquiv V he').symm (s (frameChartRingEquiv V he (MvPolynomial.X k))) = _
  rw [RingEquiv.symm_apply_eq]
  change s (E.chartRingHom V e (MvPolynomial.map (V : Y.Opens).topIso.hom.hom
    (MvPolynomial.X k))) = E'.chartRingHom V e' (MvPolynomial.map (V : Y.Opens).topIso.hom.hom _)
  rw [MvPolynomial.map_X, chartRingHom_X, hβ, ← chartRingHom_X (e := fun k => β (e k)), ha k]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  congr 2
  exact (ConcreteCategory.congr_hom (V : Y.Opens).topIso.inv_hom_id (a k l)).symm

variable (hE : E.IsLocallyFreeOfRank n) (hE' : E'.IsLocallyFreeOfRank n) (α : E ≅ E')

/-- `Sym(α)` on the ring of sections over an open. -/
private abbrev symSectionsEquiv (α : E ≅ E') (V : Y.Opens) :
    E.symSections V ≃+* E'.symSections V :=
  sectionsRingEquiv _ _ (symmetricAlgebraIso α) (symmetricAlgebraIso_hom_mul α) V

private lemma symSectionsEquiv_unit (α : E ≅ E') (V : Y.Opens) (r : Γ(Y, V)) :
    symSectionsEquiv α V (unitRingHom E.symmetricAlgebraStructure_isCommutative V r) =
      unitRingHom E'.symmetricAlgebraStructure_isCommutative V r := by
  change (symmetricAlgebraIso α).hom.val.app (op V) (r • oneSection E.symmetricAlgebraStructure V) =
    r • oneSection E'.symmetricAlgebraStructure V
  rw [((symmetricAlgebraIso α).hom.val.app (op V)).hom.map_smul]
  exact congrArg (r • ·) (symmetricAlgebraIso_hom_one α (op V))

private lemma symSectionsEquiv_symDegreeOne (α : E ≅ E') (V : Y.Opens) (m : Γ(E, V)) :
    symSectionsEquiv α V (E.symDegreeOne V m) =
      E'.symDegreeOne V (α.hom.val.app (op V) m) :=
  congrArg (toSectionsRing _) (symmetricAlgebraIso_hom_symDegreeOne α V m)

/-- **`V(α)` is an isomorphism of geometric vector bundles** (Hartshorne II, Exercise 5.18): for an
isomorphism `α : E ≅ E'` of locally free sheaves of rank `n`, on an affine open `V` with frames
`e` of `E` and `e'` of `E'`, the charts of `V(E)` and `V(E')` differ by the linear substitution
expressing `α(e)` in the frame `e'`. -/
def vectorBundleBundleIso :
    GeometricVectorBundle.BundleIso (vectorBundleAtlas hE) (vectorBundleAtlas hE') where
  iso := vectorBundleIso hE hE' α
  over := vectorBundleIso_hom_proj hE hE' α
  compatible a b V ha hb := by
    have hc := GeometricVectorBundle.transport_chart (vectorBundleAtlas hE')
      (vectorBundleIso hE hE' α) (vectorBundleIso_hom_proj hE hE' α)
    cases a with
    | inl c =>
      cases b with
      | inl d => exact (vectorBundleAtlas hE).linear c d V ha hb
      | inr d =>
        change GeometricVectorBundle.IsLinearTransition V ha hb ((vectorBundleAtlas hE).chart c)
          ((GeometricVectorBundle.transport (vectorBundleAtlas hE') _ _).chart d)
        rw [hc]
        refine ⟨chartChange (c.isLocalFrame.restrictLE ha) (d.isLocalFrame.restrictLE hb)
          (symSectionsEquiv α V) (symSectionsEquiv_unit α V),
          isLinearPolynomialAlgHom_chartChange _ _ _ _ _ (symSectionsEquiv_symDegreeOne α V), ?_⟩
        simp only [GeometricVectorBundle.chart, vectorBundleAtlas, Category.assoc]
        rw [reassoc_of% (affineSpaceChart_frameTrivialization_inv hE' d.V V hb d.isLocalFrame),
          affineSpaceChart_frameTrivialization_inv hE c.V V ha c.isLocalFrame,
          vectorBundleIso, relSpecIso_ι_inv, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
        congr 2
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change (frameChartRingEquiv V (d.isLocalFrame.restrictLE hb)).symm
            (symSectionsEquiv α V x) =
          (frameChartRingEquiv V (d.isLocalFrame.restrictLE hb)).symm (symSectionsEquiv α V
            (frameChartRingEquiv V (c.isLocalFrame.restrictLE ha)
              ((frameChartRingEquiv V (c.isLocalFrame.restrictLE ha)).symm x)))
        rw [RingEquiv.apply_symm_apply]
    | inr d =>
      cases b with
      | inl c =>
        change GeometricVectorBundle.IsLinearTransition V ha hb
          ((GeometricVectorBundle.transport (vectorBundleAtlas hE') _ _).chart d)
          ((vectorBundleAtlas hE).chart c)
        rw [hc]
        refine ⟨chartChange (d.isLocalFrame.restrictLE ha) (c.isLocalFrame.restrictLE hb)
          (symSectionsEquiv α.symm V) (symSectionsEquiv_unit α.symm V),
          isLinearPolynomialAlgHom_chartChange _ _ _ _ _
            (symSectionsEquiv_symDegreeOne α.symm V), ?_⟩
        simp only [GeometricVectorBundle.chart, vectorBundleAtlas, Category.assoc]
        rw [affineSpaceChart_frameTrivialization_inv hE c.V V hb c.isLocalFrame,
          reassoc_of% (affineSpaceChart_frameTrivialization_inv hE' d.V V ha d.isLocalFrame),
          vectorBundleIso, relSpecIso_ι_inv, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
        congr 2
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change (frameChartRingEquiv V (c.isLocalFrame.restrictLE hb)).symm x =
          (frameChartRingEquiv V (c.isLocalFrame.restrictLE hb)).symm
            ((symSectionsEquiv α V).symm (frameChartRingEquiv V (d.isLocalFrame.restrictLE ha)
              ((frameChartRingEquiv V (d.isLocalFrame.restrictLE ha)).symm
                (symSectionsEquiv α V x))))
        rw [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
      | inr d' =>
        exact (GeometricVectorBundle.transport (vectorBundleAtlas hE') _ _).linear d d' V ha hb

end VectorBundleBundleIso

end Scheme.Modules


/-! ### The two maps on isomorphism classes -/

namespace GeometricVectorBundle

open Scheme.Modules

/-- **The class of `V(E)`** (Hartshorne II, Exercise 5.18(d)): the map sending the class of a
locally free sheaf `E` of rank `n` to the class of the geometric vector bundle `V(E)`. It is well
defined since an isomorphism `E ≅ E'` induces an isomorphism of geometric vector bundles
`V(E) ≅ V(E')` (`Scheme.Modules.vectorBundleBundleIso`). -/
def vectorBundleClass : LocallyFreeIsoClasses Y n → IsoClasses Y n :=
  Quotient.map (fun E => ⟨Over.mk (vectorBundleProj E.1 E.2), vectorBundleAtlas E.2⟩)
    (fun E E' ⟨α⟩ => ⟨vectorBundleBundleIso E.2 E'.2 α⟩)

lemma vectorBundleClass_mk (E : Y.Modules) (hE : E.IsLocallyFreeOfRank n) :
    vectorBundleClass (Quotient.mk _ ⟨E, hE⟩) =
      Quotient.mk _ ⟨Over.mk (vectorBundleProj E hE), vectorBundleAtlas hE⟩ := rfl

/-- **`𝒮(V(E)/Y)^∨ ≅ E`**: the class of the dual of the sheaf of sections is a left inverse of
`E ↦ V(E)` on isomorphism classes. -/
theorem sectionsDualClass_vectorBundleClass (q : LocallyFreeIsoClasses Y n) :
    sectionsDualClass (vectorBundleClass q) = q :=
  Quotient.inductionOn q fun E => sectionsDualClass_vectorBundle E.1 E.2

lemma vectorBundleClass_injective :
    Function.Injective (vectorBundleClass : LocallyFreeIsoClasses Y n → IsoClasses Y n) :=
  Function.LeftInverse.injective sectionsDualClass_vectorBundleClass

end GeometricVectorBundle

end

end AlgebraicGeometry
