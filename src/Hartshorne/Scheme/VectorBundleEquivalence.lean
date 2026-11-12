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

end GeometricVectorBundle

end

end AlgebraicGeometry
