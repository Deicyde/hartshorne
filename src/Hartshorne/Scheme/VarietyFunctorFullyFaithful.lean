/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VarietyToSchemeFunctor
import Hartshorne.Scheme.VarietyClosedPoints
import Mathlib.AlgebraicGeometry.Properties

/-!
# The variety-to-scheme functor is fully faithful

Hartshorne, *Algebraic Geometry*, II.2, Proposition 2.6 and Exercise 2.15(c)
(pp. 78–81).

For varieties `W`, `V` with an affine-open basis over an algebraically closed
field `k`, the map `Hom(W, V) → Hom_k(t(W), t(V))` sending a morphism of
varieties to the induced morphism of associated schemes is bijective.

## Proof

* *Faithfulness.* The induced morphism sends `α_W(x) = closure {x}` to
  `α_V(g x)`, and `α_V` is injective, so `g` is recovered from its induced
  morphism.
* *Values of pulled-back sections.* Let `φ : t(W) → t(V)` be a morphism over
  `k`, let `x ∈ W`, and let `s` be a section of `t(V)` over an open `U`
  containing `φ(α_W x)`. Then `s` takes the constant value `c = (φ^♯ s)(x)` on
  `φ(α_W x) ∩ U`: otherwise `s - c` does not vanish at some point of the
  irreducible closed set `φ(α_W x)`, so its germ there is a unit; its image under
  the stalk map is the germ of `φ^♯ s - c` at `α_W x` (since `φ` commutes with the
  constants, being a morphism over `k`), which is then a unit, so `φ^♯ s - c`
  does not vanish at `x`, a contradiction.
* *Closed points.* Applied to the regular coordinate functions on an affine
  open neighbourhood, which separate points, this shows `φ(α_W x)` has only one
  point, i.e. `φ(α_W x) = α_V(y)` for a unique `y`. This defines a map
  `g : W → V` with `α_V ∘ g = φ ∘ α_W`, continuous since `α_V` is an embedding,
  and the previous point says `(φ^♯ s)(x) = s(g x)`: regular functions pull back
  to regular functions, so `g` is a morphism of varieties.
* *Recovering `φ`.* The induced morphism of `g` and `φ` agree on closed points.
  A point `Z` of `t(W)` lies in the closure of `α_W(Z)`, and `α_W(Z)` lies in the
  closure of `{Z}`; so for any continuous map `F` from `t(W)`, the closures of
  `{F Z}` and `F(α_W(Z))` agree. As `t(V)` is `T₀`, the two point maps agree.
  The sheaf maps agree because both send a section `s` to `s ∘ g`.

## Main results

* `Hartshorne.VarietyHom.associatedSchemeHom_injective`: faithfulness.
* `Hartshorne.VarietyHom.ofSchemeHom`, `Hartshorne.VarietyHom.associatedSchemeHom_ofSchemeHom`:
  the morphism of varieties underlying a morphism of associated schemes over `k`.
* `Hartshorne.varietyToSchemeFunctor_map_bijective`: the map on Hom-sets of the
  variety-to-scheme functor is bijective; hence the functor is full and faithful.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry

namespace Hartshorne

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ### Closures in the generic completion -/

/-- A point `Z` of the associated scheme lies in the closure of the image of the
classical points of `Z`. -/
theorem varietyAssociatedScheme_mem_closure_image_alpha (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) (Z : varietyAssociatedScheme V hV) :
    Z ∈ closure (varietyAssociatedSchemeAlpha V hV ''
      ((show IrreducibleCloseds V.carrier from Z) : Set V.carrier)) := by
  rw [mem_closure_iff]
  rintro o ⟨O, rfl⟩ ⟨p, hpZ, hpO⟩
  exact ⟨varietyAssociatedSchemeAlpha V hV p, ⟨p, subset_closure rfl, hpO⟩, p, hpZ, rfl⟩

/-- The classical points of `Z` lie in the closure of `{Z}`. -/
theorem varietyAssociatedScheme_alpha_mem_closure (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) (Z : varietyAssociatedScheme V hV) {p : V.carrier}
    (hp : p ∈ ((show IrreducibleCloseds V.carrier from Z) : Set V.carrier)) :
    varietyAssociatedSchemeAlpha V hV p ∈ closure ({Z} : Set (varietyAssociatedScheme V hV)) :=
  (genericCompletion_mem_closure_singleton_iff (X := V.carrier)).2
    ((show IrreducibleCloseds V.carrier from Z).isClosed.closure_subset_iff.2
      (Set.singleton_subset_iff.2 hp))

/-- Two continuous maps from the associated scheme to a `T₀` space that agree on
the classical points agree. -/
theorem varietyAssociatedScheme_continuous_ext (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) {Y : Type*} [TopologicalSpace Y] [T0Space Y]
    {F G : varietyAssociatedScheme V hV → Y} (hF : Continuous F) (hG : Continuous G)
    (h : ∀ x, F (varietyAssociatedSchemeAlpha V hV x) = G (varietyAssociatedSchemeAlpha V hV x)) :
    F = G := by
  have key : ∀ {H : varietyAssociatedScheme V hV → Y}, Continuous H → ∀ Z,
      closure {H Z} = closure (H '' (varietyAssociatedSchemeAlpha V hV ''
        ((show IrreducibleCloseds V.carrier from Z) : Set V.carrier))) := by
    intro H hH Z
    apply subset_antisymm
    · exact closure_minimal (Set.singleton_subset_iff.2
        (map_mem_closure hH (varietyAssociatedScheme_mem_closure_image_alpha V hV Z)
          (Set.mapsTo_image _ _))) isClosed_closure
    · refine closure_minimal ?_ isClosed_closure
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact map_mem_closure hH (varietyAssociatedScheme_alpha_mem_closure V hV Z hp)
        (Set.mapsTo_singleton.2 rfl)
  funext Z
  refine Inseparable.eq (inseparable_iff_closure_eq.2 ?_)
  rw [key hF, key hG, Set.image_image, Set.image_image]
  simp_rw [h]

/-! ### Morphisms over `k` and values of sections -/

namespace VarietyHom

variable {W V : Variety.{u, u} k} {hW : W.HasAffineOpenBasis} {hV : V.HasAffineOpenBasis}

/-- A morphism of associated schemes over `k` commutes with the inclusions of
the constant regular functions. -/
theorem constants_comp_appTop_of_comp_structureMorphism
    {φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV}
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW) :
    varietyAssociatedSchemeConstants V hV ≫ φ.appTop = varietyAssociatedSchemeConstants W hW := by
  rw [← varietyAssociatedScheme_structureMorphism_appTop V hV,
    ← varietyAssociatedScheme_structureMorphism_appTop W hW, ← hφ, Scheme.Hom.comp_appTop,
    Category.assoc]

/-- A morphism of associated schemes over `k` sends the restriction of a
constant to the restriction of the same constant. -/
theorem app_res_constants_of_comp_structureMorphism
    {φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV}
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW)
    (U : Opens (varietyAssociatedScheme V hV)) (c : k) :
    φ.app U ((varietyAssociatedScheme V hV).presheaf.map (homOfLE le_top).op
        (varietyAssociatedSchemeConstants V hV c)) =
      (varietyAssociatedScheme W hW).presheaf.map (homOfLE le_top).op
        (varietyAssociatedSchemeConstants W hW c) := by
  have h1 : φ.app U ((varietyAssociatedScheme V hV).presheaf.map (homOfLE le_top).op
        (varietyAssociatedSchemeConstants V hV c)) =
      (varietyAssociatedScheme W hW).presheaf.map
        ((Opens.map φ.base).map (homOfLE (le_top : U ≤ ⊤))).op
        (φ.app ⊤ (varietyAssociatedSchemeConstants V hV c)) :=
    congrArg (fun F => F.hom (varietyAssociatedSchemeConstants V hV c))
      (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  have h2 : φ.app ⊤ (varietyAssociatedSchemeConstants V hV c) =
      varietyAssociatedSchemeConstants W hW c := by
    rw [← constants_comp_appTop_of_comp_structureMorphism hφ]
    rfl
  rw [h1, h2]
  rfl

/-- **Hartshorne II.2, Proposition 2.6.** Let `φ : t(W) → t(V)` be a morphism
over `k` and `x ∈ W`. A section `s` of `t(V)` over an open containing `φ(α_W x)`
takes the value `(φ^♯ s)(x)` at every classical point of `φ(α_W x)` in its
domain. -/
theorem app_apply_of_comp_structureMorphism
    {φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV}
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW)
    (x : W.carrier) {U : Opens (varietyAssociatedScheme V hV)}
    (hx : φ.base (varietyAssociatedSchemeAlpha W hW x) ∈ U)
    (s : Γ(varietyAssociatedScheme V hV, U)) {p : V.carrier}
    (hpZ : p ∈ ((show IrreducibleCloseds V.carrier from
      φ.base (varietyAssociatedSchemeAlpha W hW x)) : Set V.carrier))
    (hp : p ∈ (genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm U) :
    (show W.regular _ from φ.app U s).1 ⟨x, hx⟩ = (show V.regular _ from s).1 ⟨p, hp⟩ := by
  have := W.t1Space_of_hasAffineOpenBasis hW
  by_contra hne
  set c := (show W.regular _ from φ.app U s).1 ⟨x, hx⟩
  let t : Γ(varietyAssociatedScheme V hV, U) :=
    s - (varietyAssociatedScheme V hV).presheaf.map (homOfLE le_top).op
      (varietyAssociatedSchemeConstants V hV c)
  have ht : (show V.regular _ from t).1 ⟨p, hp⟩ ≠ 0 := by
    change (show V.regular _ from s).1 ⟨p, hp⟩ - c ≠ 0
    rw [sub_ne_zero]
    exact Ne.symm hne
  have hunit0 : IsUnit ((varietyAssociatedScheme V hV).presheaf.germ U _ hx t) :=
    isUnit_germ_of_ne_zero (V := V) hx t hpZ hp ht
  have hunit := hunit0.map (φ.stalkMap (varietyAssociatedSchemeAlpha W hW x)).hom
  rw [Scheme.Hom.germ_stalkMap_apply] at hunit
  obtain ⟨q, hq, hqU, hqne⟩ := exists_ne_zero_of_isUnit_germ (V := W) _ _ hunit
  have hqx : q = x := by
    have hq' : q ∈ closure ({x} : Set W.carrier) := hq
    rwa [closure_singleton, Set.mem_singleton_iff] at hq'
  subst hqx
  apply hqne
  have happ : φ.app U t = φ.app U s - (varietyAssociatedScheme W hW).presheaf.map
      (homOfLE le_top).op (varietyAssociatedSchemeConstants W hW c) := by
    rw [map_sub, app_res_constants_of_comp_structureMorphism hφ]
  rw [happ]
  change c - c = 0
  exact sub_self c

/-- **Hartshorne II.2, Proposition 2.6.** A morphism of associated schemes over
`k` sends closed points to closed points: `φ(α_W x) = α_V(y)` for some
`y ∈ V`. -/
theorem exists_alpha_eq_of_comp_structureMorphism
    {φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV}
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW) (x : W.carrier) :
    ∃ y : V.carrier, varietyAssociatedSchemeAlpha V hV y =
      φ.base (varietyAssociatedSchemeAlpha W hW x) := by
  have := V.t1Space_of_hasAffineOpenBasis hV
  let Z : IrreducibleCloseds V.carrier := φ.base (varietyAssociatedSchemeAlpha W hW x)
  obtain ⟨y, hyZ⟩ := Z.isIrreducible.nonempty
  refine ⟨y, ?_⟩
  by_contra hz
  obtain ⟨U, hyU, hsep⟩ := V.exists_open_regular_separating hV y
  -- A second point of `Z ∩ U`.
  obtain ⟨y', hy'Z, hy'U, hy'y⟩ : ∃ y' ∈ (Z : Set V.carrier), y' ∈ U ∧ y' ≠ y := by
    have hne : ((Z : Set V.carrier) ∩ ({y}ᶜ : Set V.carrier)).Nonempty := by
      by_contra hempty
      apply hz
      change genericCompletionAlphaPoint (TopCat.of V.carrier) y = Z
      refine IrreducibleCloseds.ext ?_
      rw [genericCompletionAlphaPoint_coe]
      refine (Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 hyZ)).symm
      intro w hw
      by_contra hwy
      exact hempty ⟨w, hw, hwy⟩
    obtain ⟨w, hwZ, hwU, hwy⟩ :=
      Z.isIrreducible.2 U {y}ᶜ U.isOpen isOpen_compl_singleton ⟨y, hyZ, hyU⟩ hne
    exact ⟨w, hwZ, hwU, hwy⟩
  obtain ⟨f, hf, hfne⟩ := hsep ⟨y, hyU⟩ ⟨y', hy'U⟩ fun h => hy'y (congrArg Subtype.val h).symm
  set e := genericCompletionOpensOrderIso (TopCat.of V.carrier)
  let s : Γ(varietyAssociatedScheme V hV, e U) :=
    (⟨_, V.regular_restrict (e.symm_apply_apply U).le hf⟩ : V.regular (e.symm (e U)))
  have hx : φ.base (varietyAssociatedSchemeAlpha W hW x) ∈ e U := ⟨y, hyZ, hyU⟩
  have hmem : ∀ p ∈ U, p ∈ e.symm (e U) := fun p hp => (e.symm_apply_apply U).ge hp
  have h1 := app_apply_of_comp_structureMorphism hφ x hx s hyZ (hmem y hyU)
  have h2 := app_apply_of_comp_structureMorphism hφ x hx s hy'Z (hmem y' hy'U)
  exact hfne (h1.symm.trans h2)

/-- The map `W → V` underlying a morphism of associated schemes over `k`:
`x` goes to the point `y` with `α_V(y) = φ(α_W x)`. -/
def pointMapOfSchemeHom (φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV)
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW) (x : W.carrier) : V.carrier :=
  (exists_alpha_eq_of_comp_structureMorphism hφ x).choose

theorem alpha_pointMapOfSchemeHom
    (φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV)
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW) (x : W.carrier) :
    varietyAssociatedSchemeAlpha V hV (pointMapOfSchemeHom φ hφ x) =
      φ.base (varietyAssociatedSchemeAlpha W hW x) :=
  (exists_alpha_eq_of_comp_structureMorphism hφ x).choose_spec

/-- The section `φ^♯ s` takes the value `s(g x)` at `x`, where `g` is the
underlying point map. -/
theorem app_apply_eq_pointMapOfSchemeHom
    (φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV)
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW)
    (x : W.carrier) {U : Opens (varietyAssociatedScheme V hV)}
    (hx : φ.base (varietyAssociatedSchemeAlpha W hW x) ∈ U)
    (s : Γ(varietyAssociatedScheme V hV, U)) :
    (show W.regular _ from φ.app U s).1 ⟨x, hx⟩ =
      (show V.regular _ from s).1 ⟨pointMapOfSchemeHom φ hφ x, by
        change varietyAssociatedSchemeAlpha V hV (pointMapOfSchemeHom φ hφ x) ∈ U
        rw [alpha_pointMapOfSchemeHom]
        exact hx⟩ := by
  refine app_apply_of_comp_structureMorphism hφ x hx s ?_ _
  have h := alpha_pointMapOfSchemeHom φ hφ x
  have hmem : pointMapOfSchemeHom φ hφ x ∈ ((show IrreducibleCloseds V.carrier from
      varietyAssociatedSchemeAlpha V hV (pointMapOfSchemeHom φ hφ x)) : Set V.carrier) :=
    subset_closure rfl
  rwa [h] at hmem

theorem continuous_pointMapOfSchemeHom
    (φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV)
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW) :
    Continuous (pointMapOfSchemeHom φ hφ) := by
  rw [(varietyAssociatedScheme_isEmbedding_alpha_and_range V hV).1.isInducing.continuous_iff]
  have : varietyAssociatedSchemeAlpha V hV ∘ pointMapOfSchemeHom φ hφ =
      φ.base ∘ varietyAssociatedSchemeAlpha W hW :=
    funext (alpha_pointMapOfSchemeHom φ hφ)
  rw [this]
  exact φ.base.hom.continuous.comp (genericCompletionAlpha (TopCat.of W.carrier)).hom.continuous

/-- **Hartshorne II.2, Proposition 2.6 and Exercise 2.15(c).** The morphism
of varieties underlying a morphism of associated schemes over `k`. -/
def ofSchemeHom (φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV)
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW) : VarietyHom W V where
  toFun := pointMapOfSchemeHom φ hφ
  continuous_toFun := continuous_pointMapOfSchemeHom φ hφ
  regular_comp O f hf := by
    set eV := genericCompletionOpensOrderIso (TopCat.of V.carrier)
    set eW := genericCompletionOpensOrderIso (TopCat.of W.carrier)
    let s : Γ(varietyAssociatedScheme V hV, eV O) :=
      (⟨_, V.regular_restrict (eV.symm_apply_apply O).le hf⟩ : V.regular (eV.symm (eV O)))
    have hle : Opens.comap ⟨pointMapOfSchemeHom φ hφ, continuous_pointMapOfSchemeHom φ hφ⟩ O ≤
        eW.symm (φ ⁻¹ᵁ eV O) := by
      intro x hx
      change φ.base (varietyAssociatedSchemeAlpha W hW x) ∈ eV O
      rw [← alpha_pointMapOfSchemeHom φ hφ x]
      exact ⟨_, subset_closure rfl, hx⟩
    have hreg := W.regular_restrict hle (show W.regular _ from φ.app (eV O) s).2
    convert hreg using 1
    funext x
    exact (app_apply_eq_pointMapOfSchemeHom φ hφ x.1 (hle x.2) s).symm

/-- **Hartshorne II.2, Proposition 2.6 and Exercise 2.15(c).** Every
morphism of associated schemes over `k` is induced by a morphism of varieties. -/
theorem associatedSchemeHom_ofSchemeHom
    (φ : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV)
    (hφ : φ ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW) :
    (ofSchemeHom φ hφ).associatedSchemeHom hW hV = φ := by
  have hbase : ((ofSchemeHom φ hφ).associatedSchemeHom hW hV).base = φ.base := by
    ext1 z
    refine congrFun (varietyAssociatedScheme_continuous_ext W hW
      ((ofSchemeHom φ hφ).associatedSchemeHom hW hV).base.hom.continuous
      φ.base.hom.continuous fun x =>
        (genericCompletionMap_alpha (ofSchemeHom φ hφ).toTopCatHom x).trans
          (alpha_pointMapOfSchemeHom φ hφ x)) z
  refine Scheme.Hom.ext hbase fun O => ?_
  ext s
  apply Subtype.ext
  funext w
  exact (app_apply_eq_pointMapOfSchemeHom φ hφ w.1 _ s).symm

/-- **Hartshorne II.2, Proposition 2.6.** A morphism of varieties is determined
by the induced morphism of associated schemes. -/
theorem associatedSchemeHom_injective (hW : W.HasAffineOpenBasis) (hV : V.HasAffineOpenBasis) :
    Function.Injective fun g : VarietyHom W V => g.associatedSchemeHom hW hV := by
  intro f g h
  ext x
  apply (varietyAssociatedScheme_isEmbedding_alpha_and_range V hV).1.injective
  have := congrArg (fun F : varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV =>
    F.base (varietyAssociatedSchemeAlpha W hW x)) h
  simp only at this
  exact (genericCompletionMap_alpha f.toTopCatHom x).symm.trans
    (this.trans (genericCompletionMap_alpha g.toTopCatHom x))

end VarietyHom

/-- **Hartshorne II.2, Proposition 2.6 and Exercise 2.15(c) (pp. 78–81).**
For varieties `V`, `W` over an algebraically closed field `k` (with affine-open
bases), the map `Hom(V, W) → Hom_k(t(V), t(W))` given by the variety-to-scheme
functor is bijective. -/
theorem varietyToSchemeFunctor_map_bijective (X Y : SchemeVarietyCat k) :
    Function.Bijective fun f : X ⟶ Y => (varietyToSchemeFunctor k).map f := by
  constructor
  · intro f g h
    exact VarietyHom.associatedSchemeHom_injective X.hasAffineOpenBasis Y.hasAffineOpenBasis
      (congrArg CommaMorphism.left h)
  · intro F
    exact ⟨VarietyHom.ofSchemeHom F.left (Over.w F),
      Over.OverMorphism.ext (VarietyHom.associatedSchemeHom_ofSchemeHom F.left (Over.w F))⟩

/-- The variety-to-scheme functor is faithful. -/
instance varietyToSchemeFunctor_faithful : (varietyToSchemeFunctor k).Faithful :=
  ⟨fun h => (varietyToSchemeFunctor_map_bijective _ _).1 h⟩

/-- The variety-to-scheme functor is full. -/
instance varietyToSchemeFunctor_full : (varietyToSchemeFunctor k).Full :=
  ⟨fun F => (varietyToSchemeFunctor_map_bijective _ _).2 F⟩

end Hartshorne
