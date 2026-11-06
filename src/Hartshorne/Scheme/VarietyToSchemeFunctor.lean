/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VarietySchemeOverK

/-!
# The variety-to-scheme functor

Hartshorne, *Algebraic Geometry*, II.2, the functorial construction in
Proposition 2.6 (pp. 78–79).

A morphism of varieties `g : W → V` induces the morphism of ringed spaces
`(t(W), α_* 𝒪_W) → (t(V), α_* 𝒪_V)` sending an irreducible closed subset `Z` to
the closure of `g(Z)` and pulling regular functions back. For varieties with an
affine-open basis over an algebraically closed field this is a morphism of the
associated schemes over `k`, and the construction is functorial.

## Units in the stalks

A section over an open `U` of `t(V)` is a regular function `f` on the
corresponding open `U₀` of `V`. Its germ at a point `Z ∈ U` is a unit if and
only if `f` does not vanish identically on `Z ∩ U₀`: if `f(p) ≠ 0` for some
`p ∈ Z ∩ U₀`, then `f` is invertible on the open set where it does not vanish,
which meets `Z`; conversely an inverse of the germ is an inverse of `f` on an
open set meeting `Z`. Given this, the stalk maps are local: if the pullback
`f ∘ g` does not vanish identically on `Z`, then `f` does not vanish at some
point `g(p)` with `p ∈ Z`, and this point lies in the closure of `g(Z)`.

## Main definitions and results

* `Hartshorne.VarietyHom.associatedSchemeHom`: the morphism of associated
  schemes `t(W) → t(V)` induced by a morphism of varieties `W → V`; its
  underlying map of ringed spaces is the generic-completion morphism
  (`Hartshorne.VarietyHom.associatedSchemeHom_toShHom`).
* `Hartshorne.VarietyHom.isLocalHom_genericCompletionHom_stalkMap`: the stalk
  maps of the generic-completion morphism are local.
* `Hartshorne.VarietyHom.associatedSchemeHom_comp_structureMorphism`,
  `Hartshorne.VarietyHom.associatedSchemeHom_isOver`: it commutes with the
  structure morphisms to `Spec k`.
* `Hartshorne.VarietyHom.associatedSchemeHom_id`,
  `Hartshorne.VarietyHom.associatedSchemeHom_comp`: identity and composition.
* `Hartshorne.varietyToSchemeFunctor`: the functor from the scheme-variety
  source category to the category of schemes over `k`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry

namespace Hartshorne

universe u

variable {k : Type u} [Field k]

/-! ### Units in the stalks of `(t(V), α_* 𝒪_V)` -/

namespace Variety

variable (V : Variety.{u, u} k)

/-- A regular function that vanishes nowhere on a smaller open subset restricts
to a unit there. -/
theorem isUnit_regularRestriction_of_ne_zero {O O' : Opens V.carrier} (h : O' ≤ O)
    (f : V.regular O) (hf : ∀ x : O', f.1 ⟨x.1, h x.2⟩ ≠ 0) :
    IsUnit (V.regularRestriction h f) := by
  refine IsUnit.of_mul_eq_one ⟨fun x => 1 / f.1 ⟨x.1, h x.2⟩,
    V.regular_div (Subalgebra.one_mem _) (V.regular_restrict h f.2) hf⟩ ?_
  apply Subtype.ext
  funext x
  exact mul_one_div_cancel (hf x)

/-- A unit among the regular functions on an open subset vanishes nowhere. -/
theorem regular_ne_zero_of_isUnit {O : Opens V.carrier} {f : V.regular O} (hf : IsUnit f)
    (x : O) : f.1 x ≠ 0 := by
  obtain ⟨g, hg⟩ := hf.exists_right_inv
  intro h0
  have := congrArg (fun F : V.regular O => F.1 x) hg
  change f.1 x * g.1 x = 1 at this
  rw [h0, zero_mul] at this
  exact zero_ne_one this

/-- The open subset of an open `O` where a regular function on `O` does not
vanish. -/
def nonvanishingOpen {O : Opens V.carrier} (f : V.regular O) : Opens V.carrier :=
  ⟨Subtype.val '' {x : O | f.1 x ≠ 0},
    O.isOpenEmbedding'.isOpenMap _ (V.isClosed_zeroLocus f.2).isOpen_compl⟩

end Variety

namespace VarietyHom

variable {V : Variety.{u, u} k}

/-- If a section of `(t(V), α_* 𝒪_V)` over `U` does not vanish at some point of
an irreducible closed subset `Z ∈ U`, its germ at `Z` is a unit. -/
theorem isUnit_germ_of_ne_zero {U : Opens (genericCompletionSheafedSpace V)}
    {Z : genericCompletionSheafedSpace V} (hZ : Z ∈ U)
    (f : (genericCompletionSheafedSpace V).presheaf.obj (op U)) {p : V.carrier}
    (hpZ : p ∈ ((show IrreducibleCloseds V.carrier from Z) : Set V.carrier))
    (hp : p ∈ (genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm U)
    (hfp : (show V.regular _ from f).1 ⟨p, hp⟩ ≠ 0) :
    IsUnit ((genericCompletionSheafedSpace V).presheaf.germ U Z hZ f) := by
  set e := genericCompletionOpensOrderIso (TopCat.of V.carrier)
  let f' : V.regular (e.symm U) := f
  let D := V.nonvanishingOpen f'
  have hDU : D ≤ e.symm U := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hU' : e D ≤ U := (e.le_symm_apply).1 hDU
  have hZD : Z ∈ e D := ⟨p, hpZ, ⟨p, hp⟩, hfp, rfl⟩
  rw [← (genericCompletionSheafedSpace V).presheaf.germ_res_apply (homOfLE hU') Z hZD f]
  apply IsUnit.map
  apply V.isUnit_regularRestriction_of_ne_zero (e.symm.monotone hU') f'
  rintro ⟨x, hx⟩
  have hx' : x ∈ D := by
    have := hx
    rwa [e.symm_apply_apply] at this
  obtain ⟨y, hy, rfl⟩ := hx'
  exact hy

/-- If the germ at `Z` of a section of `(t(V), α_* 𝒪_V)` is a unit, the section
does not vanish at some point of `Z`. -/
theorem exists_ne_zero_of_isUnit_germ {U : Opens (genericCompletionSheafedSpace V)}
    {Z : genericCompletionSheafedSpace V} (hZ : Z ∈ U)
    (f : (genericCompletionSheafedSpace V).presheaf.obj (op U))
    (hf : IsUnit ((genericCompletionSheafedSpace V).presheaf.germ U Z hZ f)) :
    ∃ p ∈ ((show IrreducibleCloseds V.carrier from Z) : Set V.carrier),
      ∃ hp : p ∈ (genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm U,
        (show V.regular _ from f).1 ⟨p, hp⟩ ≠ 0 := by
  set e := genericCompletionOpensOrderIso (TopCat.of V.carrier)
  obtain ⟨U', i, hZU', hunit⟩ :=
    RingedSpace.isUnit_res_of_isUnit_germ (genericCompletionSheafedSpace V) U f Z hZ hf
  rw [← e.apply_symm_apply U'] at hZU'
  obtain ⟨p, hpZ, hpU'⟩ := hZU'
  refine ⟨p, hpZ, e.symm.monotone i.le hpU', ?_⟩
  exact V.regular_ne_zero_of_isUnit hunit ⟨p, hpU'⟩

variable {W : Variety.{u, u} k} (g : VarietyHom W V)

/-- The stalk maps of the generic-completion morphism induced by a morphism of
varieties are local ring homomorphisms. -/
theorem isLocalHom_genericCompletionHom_stalkMap (Z : genericCompletionSheafedSpace W) :
    IsLocalHom (g.genericCompletionHom.hom.stalkMap Z).hom := by
  constructor
  intro a ha
  obtain ⟨U, hZU, f, rfl⟩ :=
    (genericCompletionSheafedSpace V).presheaf.exists_germ_eq a
  rw [PresheafedSpace.stalkMap_germ_apply] at ha
  obtain ⟨p, hpZ, hp, hfp⟩ := exists_ne_zero_of_isUnit_germ _ _ ha
  exact isUnit_germ_of_ne_zero hZU f (p := g p) (subset_closure ⟨p, hpZ, rfl⟩)
    ((mem_genericCompletionOpensOrderIso_symm_map g.toTopCatHom).1 hp) hfp

variable [IsAlgClosed k]

/-- **Hartshorne II.2, Proposition 2.6 (pp. 78–79).** The morphism of associated
schemes `t(W) → t(V)` induced by a morphism of varieties `g : W → V`: an
irreducible closed subset `Z` goes to the closure of `g(Z)`, and regular
functions are pulled back. -/
def associatedSchemeHom (hW : W.HasAffineOpenBasis) (hV : V.HasAffineOpenBasis) :
    varietyAssociatedScheme W hW ⟶ varietyAssociatedScheme V hV :=
  Scheme.Hom.mk (LocallyRingedSpace.Hom.mk g.genericCompletionHom.hom
    g.isLocalHom_genericCompletionHom_stalkMap)

/-- The underlying morphism of ringed spaces of the induced morphism of
associated schemes is the generic-completion morphism. -/
theorem associatedSchemeHom_toShHom (hW : W.HasAffineOpenBasis) (hV : V.HasAffineOpenBasis) :
    (g.associatedSchemeHom hW hV).toLRSHom.toShHom = g.genericCompletionHom :=
  rfl

/-- **Hartshorne II.2, Proposition 2.6 (pp. 78–79).** The induced morphism of
associated schemes commutes with the structure morphisms to `Spec k`. -/
theorem associatedSchemeHom_comp_structureMorphism (hW : W.HasAffineOpenBasis)
    (hV : V.HasAffineOpenBasis) :
    g.associatedSchemeHom hW hV ≫ varietyAssociatedSchemeStructureMorphism V hV =
      varietyAssociatedSchemeStructureMorphism W hW := by
  apply varietyAssociatedScheme_structureMorphism_unique
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, varietyAssociatedScheme_structureMorphism_appTop]
  ext c
  rfl

/-- The induced morphism of associated schemes is a morphism of schemes over
`k`. -/
instance associatedSchemeHom_isOver (hW : W.HasAffineOpenBasis) (hV : V.HasAffineOpenBasis) :
    (g.associatedSchemeHom hW hV).IsOver (Spec (CommRingCat.of k)) :=
  ⟨g.associatedSchemeHom_comp_structureMorphism hW hV⟩

/-- **Hartshorne II.2, Proposition 2.6.** The identity morphism of a variety
induces the identity of its associated scheme. -/
theorem associatedSchemeHom_id (hV : V.HasAffineOpenBasis) :
    (VarietyHom.id V).associatedSchemeHom hV hV = 𝟙 _ := by
  have hbase : ((VarietyHom.id V).associatedSchemeHom hV hV).base =
      (𝟙 (varietyAssociatedScheme V hV) :).base :=
    genericCompletionFunctor.map_id (TopCat.of V.carrier)
  refine Scheme.Hom.ext hbase fun O => ?_
  ext s
  apply Subtype.ext
  funext w
  rfl

/-- **Hartshorne II.2, Proposition 2.6.** The morphism of associated schemes
induced by a composite is the composite of the induced morphisms. -/
theorem associatedSchemeHom_comp {U : Variety.{u, u} k} (f : VarietyHom U W)
    (hU : U.HasAffineOpenBasis) (hW : W.HasAffineOpenBasis) (hV : V.HasAffineOpenBasis) :
    (g.comp f).associatedSchemeHom hU hV =
      f.associatedSchemeHom hU hW ≫ g.associatedSchemeHom hW hV := by
  have hbase : ((g.comp f).associatedSchemeHom hU hV).base =
      (f.associatedSchemeHom hU hW ≫ g.associatedSchemeHom hW hV).base :=
    genericCompletionFunctor.map_comp f.toTopCatHom g.toTopCatHom
  refine Scheme.Hom.ext hbase fun O => ?_
  ext s
  apply Subtype.ext
  funext w
  rfl

end VarietyHom

variable (k) [IsAlgClosed k]

/-- **Hartshorne II.2, Proposition 2.6 (pp. 78–79).** The functor from the
category of varieties with an affine-open basis to the category of schemes over
`k`: a variety goes to its associated scheme `t(V)` with its structure morphism
to `Spec k`, and a morphism of varieties to the induced morphism of associated
schemes. -/
def varietyToSchemeFunctor : SchemeVarietyCat k ⥤ Over (Spec (CommRingCat.of k)) where
  obj X := X.toScheme.asOver (Spec (CommRingCat.of k))
  map {X Y} f := (VarietyHom.associatedSchemeHom f X.hasAffineOpenBasis
    Y.hasAffineOpenBasis).asOver (Spec (CommRingCat.of k))
  map_id X := by
    ext1
    exact VarietyHom.associatedSchemeHom_id X.hasAffineOpenBasis
  map_comp {X Y Z} f g := by
    ext1
    exact VarietyHom.associatedSchemeHom_comp g f _ _ _

end Hartshorne
