/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AffineVarietySpec
import Hartshorne.Scheme.SchemeVarietyCategory
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# A variety with an affine-open basis has an associated scheme

Hartshorne, *Algebraic Geometry*, II.2, the passage from the affine case to
arbitrary varieties in Proposition 2.6 (p. 78).

For a variety `V` over an algebraically closed field `k` with an affine-open
basis, the ringed space `(t(V), α_* 𝒪_V)` is a scheme.

## Construction

* A morphism of varieties `g : W → V` induces a morphism of the ringed spaces
  `(t(W), α_* 𝒪_W) → (t(V), α_* 𝒪_V)`: on points an irreducible closed subset
  goes to the closure of its image, and regular functions are pulled back.
* If `g` is an open embedding along which every regular function on an open
  subset of `W` descends to a regular function on its image, this morphism is
  an open immersion. On points this is the observation that an irreducible
  closed subset `Z'` of `V` meeting the open image of `g` is the closure of its
  intersection with that image.
* Given a point of `t(V)`, choose a classical point in it, an affine open
  neighbourhood `U ≅ Y` of that point, and compose the inverse of the affine
  comparison `t(Y) ≅ Spec A(Y)` with the open immersion induced by
  `Y ≅ U ⊆ V`. Its image contains the given point, so the stalks of
  `(t(V), α_* 𝒪_V)` are local and it is covered by open immersions from affine
  schemes.

## Main definitions and results

* `Hartshorne.genericCompletionSheafedSpace`: the ringed space
  `(t(V), α_* 𝒪_V)` of any variety.
* `Hartshorne.varietyAssociatedScheme`: for a variety with an affine-open basis
  over an algebraically closed field, the scheme whose underlying ringed space
  is `(t(V), α_* 𝒪_V)`
  (`Hartshorne.varietyAssociatedScheme_toSheafedSpace`,
  `Hartshorne.varietyAssociatedScheme_presheaf`).
* `Hartshorne.SchemeVarietyCat.toScheme`: the same construction on the objects
  of the scheme-variety source category.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry

namespace Hartshorne

universe u v

/-! ### Irreducible closed subsets along an open embedding -/

section OpenEmbedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- The preimage of an irreducible closed subset meeting the image of an open
embedding is an irreducible closed subset. -/
def irreducibleClosedsComapOfIsOpenEmbedding (hf : IsOpenEmbedding f)
    (Z : IrreducibleCloseds Y) (hZ : ((Z : Set Y) ∩ Set.range f).Nonempty) :
    IrreducibleCloseds X where
  carrier := f ⁻¹' Z
  isIrreducible' := Z.isIrreducible.preimage hf hZ
  isClosed' := Z.isClosed.preimage hf.continuous

/-- An irreducible closed subset meeting the image of an open embedding is the
closure of the image of its preimage. -/
theorem irreducibleCloseds_map_comapOfIsOpenEmbedding (hf : IsOpenEmbedding f)
    (Z : IrreducibleCloseds Y) (hZ : ((Z : Set Y) ∩ Set.range f).Nonempty) :
    IrreducibleCloseds.map f hf.continuous (irreducibleClosedsComapOfIsOpenEmbedding hf Z hZ) =
      Z := by
  apply IrreducibleCloseds.ext
  change closure (f '' (f ⁻¹' (Z : Set Y))) = Z
  obtain ⟨-, hy, x, rfl⟩ := hZ
  exact closure_image_preimage_of_isPreirreducible f hf.isOpenMap Z ⟨x, hy⟩
    Z.isIrreducible.2 Z.isClosed

/-- Along an embedding, an irreducible closed subset is determined by the
closure of its image. -/
theorem irreducibleCloseds_map_injective_of_isEmbedding (hf : IsEmbedding f) :
    Function.Injective (IrreducibleCloseds.map f hf.continuous) := by
  have key (Z : IrreducibleCloseds X) :
      (Z : Set X) = f ⁻¹' (IrreducibleCloseds.map f hf.continuous Z : Set Y) := by
    change (Z : Set X) = f ⁻¹' closure (f '' Z)
    rw [← hf.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]
  intro Z₁ Z₂ h
  apply IrreducibleCloseds.ext
  rw [key Z₁, key Z₂, h]

/-- A point whose closure is the closure of the image of a nonempty set under
an open embedding lies in the image. -/
theorem mem_range_of_closure_singleton_eq (hf : IsOpenEmbedding f) {y : Y} {S : Set X}
    (hS : S.Nonempty) (h : closure ({y} : Set Y) = closure (f '' S)) : y ∈ Set.range f := by
  obtain ⟨x, hx⟩ := hS
  have hne : (closure ({y} : Set Y) ∩ Set.range f).Nonempty :=
    ⟨f x, h ▸ subset_closure ⟨x, hx, rfl⟩, x, rfl⟩
  rw [closure_inter_open_nonempty_iff hf.isOpen_range] at hne
  obtain ⟨_, rfl, hy⟩ := hne
  exact hy

end OpenEmbedding

/-! ### The generic completion of an open embedding -/

section GenericCompletionMap

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The generic completion of a map sends the closure of a point to the
closure of its image. -/
theorem genericCompletionMap_alpha (x : X) :
    genericCompletionMap f (genericCompletionAlpha X x) = genericCompletionAlpha Y (f x) := by
  apply IrreducibleCloseds.ext
  change closure (f '' closure {x}) = closure {f x}
  rw [closure_image_closure f.hom.continuous, Set.image_singleton]

/-- The open subset of `X` corresponding to the preimage of an open subset of
`t(Y)` is the preimage of the corresponding open subset of `Y`. -/
theorem mem_genericCompletionOpensOrderIso_symm_map {O : Opens (genericCompletionObj Y)}
    {x : X} :
    x ∈ (genericCompletionOpensOrderIso X).symm
        ((Opens.map (genericCompletionMap f)).obj O) ↔
      f x ∈ (genericCompletionOpensOrderIso Y).symm O := by
  change genericCompletionMap f (genericCompletionAlpha X x) ∈ O ↔
    genericCompletionAlpha Y (f x) ∈ O
  rw [genericCompletionMap_alpha]

/-- The generic completion of an open embedding is an open embedding. -/
theorem isOpenEmbedding_genericCompletionMap (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (genericCompletionMap f) := by
  refine .of_continuous_injective_isOpenMap (genericCompletionMap f).hom.continuous
    (irreducibleCloseds_map_injective_of_isEmbedding hf.isEmbedding) ?_
  rintro s ⟨O, rfl⟩
  refine ⟨⟨f '' O, hf.isOpenMap _ O.isOpen⟩, ?_⟩
  ext Z'
  constructor
  · rintro ⟨Z, ⟨x, hxZ, hxO⟩, rfl⟩
    exact ⟨f x, subset_closure ⟨x, hxZ, rfl⟩, x, hxO, rfl⟩
  · rintro ⟨_, hyZ, x, hxO, rfl⟩
    exact ⟨irreducibleClosedsComapOfIsOpenEmbedding hf Z' ⟨f x, hyZ, x, rfl⟩,
      ⟨x, hyZ, hxO⟩, irreducibleCloseds_map_comapOfIsOpenEmbedding hf Z' _⟩

end GenericCompletionMap

/-! ### The ringed space of a variety and the morphisms induced by varieties -/

variable {k : Type u} [Field k]

/-- **Hartshorne II.2, p. 78.** The ringed space `(t(V), α_* 𝒪_V)` of a
variety `V`. -/
def genericCompletionSheafedSpace (V : Variety.{u, v} k) :
    SheafedSpace CommRingCat.{max u v} where
  carrier := genericCompletionObj (TopCat.of V.carrier)
  presheaf := (genericCompletionRegularSheaf V).obj
  IsSheaf := (genericCompletionRegularSheaf V).property

namespace VarietyHom

variable {W V : Variety.{u, v} k} (g : VarietyHom W V)

/-- The underlying continuous map of a morphism of varieties. -/
def toTopCatHom : TopCat.of W.carrier ⟶ TopCat.of V.carrier :=
  TopCat.ofHom ⟨g, g.continuous_toFun⟩

/-- Pulling regular functions back along a morphism of varieties. -/
def regularPullback {O : Opens V.carrier} {O' : Opens W.carrier} (h : ∀ w ∈ O', g w ∈ O) :
    V.regular O →+* W.regular O' where
  toFun f := ⟨fun w => f.1 ⟨g w.1, h w.1 w.2⟩,
    W.regular_restrict (U := Opens.comap ⟨g, g.continuous_toFun⟩ O) (fun w hw => h w hw)
      (g.regular_comp O f.1 f.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem regularPullback_apply {O : Opens V.carrier} {O' : Opens W.carrier}
    (h : ∀ w ∈ O', g w ∈ O) (f : V.regular O) (w : O') :
    (g.regularPullback h f).1 w = f.1 ⟨g w.1, h w.1 w.2⟩ :=
  rfl

/-- Pulling back is bijective onto the regular functions of an open subset of
`W` mapped onto an open subset of the image, provided regular functions on open
subsets of `W` descend along `g`. -/
theorem regularPullback_bijective
    (hreg : ∀ O : Opens V.carrier, (O : Set V.carrier) ⊆ Set.range g →
      ∀ h : W.regular (Opens.comap ⟨g, g.continuous_toFun⟩ O), ∃ f : V.regular O,
        ∀ w : Opens.comap ⟨g, g.continuous_toFun⟩ O, f.1 ⟨g w.1, w.2⟩ = h.1 w)
    {O : Opens V.carrier} {O' : Opens W.carrier} (h : ∀ w ∈ O', g w ∈ O)
    (h' : ∀ w, g w ∈ O → w ∈ O') (hO : (O : Set V.carrier) ⊆ Set.range g) :
    Function.Bijective (g.regularPullback h) := by
  constructor
  · intro f₁ f₂ hf
    apply Subtype.ext
    funext y
    obtain ⟨y, hyO⟩ := y
    obtain ⟨w, rfl⟩ := hO hyO
    exact congrArg (fun F : W.regular O' => F.1 ⟨w, h' w hyO⟩) hf
  · intro F
    obtain ⟨f, hf⟩ := hreg O hO ⟨fun w => F.1 ⟨w.1, h' w.1 w.2⟩,
      W.regular_restrict (fun w hw => h' w hw) F.2⟩
    exact ⟨f, Subtype.ext (funext fun w => hf ⟨w.1, h w.1 w.2⟩)⟩

/-- The morphism of ringed spaces `(t(W), α_* 𝒪_W) → (t(V), α_* 𝒪_V)` induced
by a morphism of varieties: closure of the image on points, pullback on
regular functions. -/
def genericCompletionHom : genericCompletionSheafedSpace W ⟶ genericCompletionSheafedSpace V :=
  InducedCategory.homMk
    { base := genericCompletionMap g.toTopCatHom
      c :=
        { app := fun O => CommRingCat.ofHom (g.regularPullback
            (O := (genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm O.unop)
            (O' := (genericCompletionOpensOrderIso (TopCat.of W.carrier)).symm
              ((Opens.map (genericCompletionMap g.toTopCatHom)).obj O.unop))
            fun _ hw => (mem_genericCompletionOpensOrderIso_symm_map g.toTopCatHom).1 hw)
          naturality := fun _ _ _ => by
            ext
            rfl } }

/-- The morphism induced by an open embedding of varieties along which regular
functions descend is an open immersion. -/
theorem isOpenImmersion_genericCompletionHom (hg : IsOpenEmbedding g)
    (hreg : ∀ O : Opens V.carrier, (O : Set V.carrier) ⊆ Set.range g →
      ∀ h : W.regular (Opens.comap ⟨g, g.continuous_toFun⟩ O), ∃ f : V.regular O,
        ∀ w : Opens.comap ⟨g, g.continuous_toFun⟩ O, f.1 ⟨g w.1, w.2⟩ = h.1 w) :
    SheafedSpace.IsOpenImmersion g.genericCompletionHom := by
  have hbase : IsOpenEmbedding (genericCompletionMap g.toTopCatHom) :=
    isOpenEmbedding_genericCompletionMap _ hg
  refine { base_open := hbase, c_iso := fun U => ?_ }
  have hO : ∀ y ∈ (genericCompletionOpensOrderIso (TopCat.of V.carrier)).symm
      (hbase.functor.obj U), y ∈ Set.range g := by
    intro y hy
    obtain ⟨Z, -, hZ⟩ := hy
    exact mem_range_of_closure_singleton_eq hg Z.isIrreducible.nonempty
      (congrArg (fun T : IrreducibleCloseds V.carrier => (T : Set V.carrier)) hZ).symm
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact g.regularPullback_bijective hreg
    (fun _ hw => (mem_genericCompletionOpensOrderIso_symm_map g.toTopCatHom).1 hw)
    (fun _ hw => (mem_genericCompletionOpensOrderIso_symm_map g.toTopCatHom).2 hw) hO

end VarietyHom

/-! ### Affine charts -/

section AlgClosed

variable [IsAlgClosed k]

/-- Every point of `t(V)` lies in the image of an open immersion from the
spectrum of a ring: the coordinate ring of an affine open neighbourhood of a
classical point of the given irreducible closed subset. -/
theorem exists_isOpenImmersion_spec (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis)
    (z : genericCompletionSheafedSpace V) :
    ∃ (R : CommRingCat.{u}) (F : Spec.sheafedSpaceObj R ⟶ genericCompletionSheafedSpace V),
      z ∈ Set.range F.hom.base ∧ SheafedSpace.IsOpenImmersion F := by
  let z' : IrreducibleCloseds V.carrier := z
  obtain ⟨x, hxz⟩ := z'.isIrreducible.nonempty
  obtain ⟨U, hU, hxU, -, σ, hσ, Y, hY, φ, ψ, hψφ, hφψ⟩ := hV ⊤ x trivial
  have hψφ' (p : (V.restrict U hU).carrier) : ψ (φ p) = p :=
    congrArg (fun q : VarietyHom _ _ => q p) hψφ
  have hφψ' (p : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier) : φ (ψ p) = p :=
    congrArg (fun q : VarietyHom _ _ => q p) hφψ
  let g : VarietyHom (Variety.ofQuasiAffine hY.isQuasiAffineVariety) V :=
    (V.inclHom U hU).comp ψ
  let e : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).carrier ≃ₜ U :=
    { toFun := ψ
      invFun := φ
      left_inv := hφψ'
      right_inv := hψφ'
      continuous_toFun := ψ.continuous_toFun
      continuous_invFun := φ.continuous_toFun }
  have hg : IsOpenEmbedding g := U.isOpenEmbedding'.comp e.isOpenEmbedding
  have hrange : Set.range g = U := by
    ext y
    refine ⟨?_, fun hy => ⟨φ ⟨y, hy⟩, congrArg Subtype.val (hψφ' ⟨y, hy⟩)⟩⟩
    rintro ⟨p, rfl⟩
    exact (ψ p).2
  have hreg : ∀ O : Opens V.carrier, (O : Set V.carrier) ⊆ Set.range g →
      ∀ h : (Variety.ofQuasiAffine hY.isQuasiAffineVariety).regular
          (Opens.comap ⟨g, g.continuous_toFun⟩ O), ∃ f : V.regular O,
        ∀ w : Opens.comap ⟨g, g.continuous_toFun⟩ O, f.1 ⟨g w.1, w.2⟩ = h.1 w := by
    intro O hO h
    have hle : O ≤ pushOpens U (Opens.comap ⟨φ, φ.continuous_toFun⟩
        (Opens.comap ⟨g, g.continuous_toFun⟩ O)) := by
      intro y hy
      have hyU : y ∈ Set.range g := hO hy
      rw [hrange] at hyU
      refine ⟨hyU, fun hyU' => ?_⟩
      have h1 : g (φ ⟨y, hyU'⟩) = y := congrArg Subtype.val (hψφ' ⟨y, hyU'⟩)
      change g (φ ⟨y, hyU'⟩) ∈ O
      rw [h1]
      exact hy
    refine ⟨⟨_, V.regular_restrict hle (φ.regular_comp _ h.1 h.2)⟩, fun w => ?_⟩
    change h.1 ⟨φ (ψ w.1), _⟩ = h.1 w
    rcases w with ⟨w, hw⟩
    exact congrArg h.1 (Subtype.ext (hφψ' w))
  have := hσ
  have := g.isOpenImmersion_genericCompletionHom hg hreg
  let iso : genericCompletionSheafedSpace (Variety.ofQuasiAffine hY.isQuasiAffineVariety) ≅
      Spec.sheafedSpaceObj (CommRingCat.of (coordinateRing Y)) :=
    affineVarietyGenericCompletionSheafedSpaceIsoSpec hY
  refine ⟨CommRingCat.of (coordinateRing Y), iso.inv ≫ g.genericCompletionHom, ?_, inferInstance⟩
  have hz : ((z' : Set V.carrier) ∩ Set.range g).Nonempty := ⟨x, hxz, hrange ▸ hxU⟩
  refine ⟨iso.hom.hom.base (irreducibleClosedsComapOfIsOpenEmbedding hg z' hz), ?_⟩
  have hinv : iso.inv.hom.base (iso.hom.hom.base
      (irreducibleClosedsComapOfIsOpenEmbedding hg z' hz)) =
        irreducibleClosedsComapOfIsOpenEmbedding hg z' hz := by
    have := congrArg (fun F => F.hom.base (irreducibleClosedsComapOfIsOpenEmbedding hg z' hz))
      iso.hom_inv_id
    exact this
  change g.genericCompletionHom.hom.base (iso.inv.hom.base (iso.hom.hom.base
      (irreducibleClosedsComapOfIsOpenEmbedding hg z' hz))) = z
  rw [hinv]
  exact irreducibleCloseds_map_comapOfIsOpenEmbedding hg z' hz

/-- The stalks of `(t(V), α_* 𝒪_V)` are local rings, being stalks of
spectra along open immersions. -/
theorem genericCompletionSheafedSpace_isLocalRing (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) (z : genericCompletionSheafedSpace V) :
    IsLocalRing ((genericCompletionSheafedSpace V).presheaf.stalk z) := by
  obtain ⟨R, F, ⟨x, rfl⟩, hF⟩ := exists_isOpenImmersion_spec V hV z
  exact @RingEquiv.isLocalRing _ _ _ ((Spec.locallyRingedSpaceObj R).isLocalRing x) _
    (asIso (F.hom.stalkMap x)).symm.commRingCatIsoToRingEquiv

/-- The locally ringed space `(t(V), α_* 𝒪_V)` of a variety with an affine-open
basis. -/
def genericCompletionLocallyRingedSpace (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    LocallyRingedSpace.{u} where
  toSheafedSpace := genericCompletionSheafedSpace V
  isLocalRing := genericCompletionSheafedSpace_isLocalRing V hV

/-- **Hartshorne II.2, Proposition 2.6 (p. 78).** For a variety `V` with an
affine-open basis over an algebraically closed field, the ringed space
`(t(V), α_* 𝒪_V)` is a scheme. -/
def varietyAssociatedScheme (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme (genericCompletionLocallyRingedSpace V hV)
    fun z => by
      obtain ⟨R, F, hz, hF⟩ := exists_isOpenImmersion_spec V hV z
      refine ⟨R, ⟨F.hom, fun x => ?_⟩, hz, hF⟩
      have : IsIso (F.hom.stalkMap x) :=
        PresheafedSpace.IsOpenImmersion.stalk_iso (H := hF) F.hom x
      exact isLocalHom_of_isIso (F.hom.stalkMap x)

/-- The underlying ringed space of the associated scheme is
`(t(V), α_* 𝒪_V)`. -/
theorem varietyAssociatedScheme_toSheafedSpace (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) :
    (varietyAssociatedScheme V hV).toSheafedSpace = genericCompletionSheafedSpace V :=
  rfl

/-- The structure sheaf of the associated scheme is the pushforward `α_* 𝒪_V`
of the sheaf of regular functions along `α : V → t(V)`. -/
theorem varietyAssociatedScheme_presheaf (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    (varietyAssociatedScheme V hV).presheaf =
      genericCompletionAlpha (TopCat.of V.carrier) _* V.regularPresheaf :=
  rfl

/-- The scheme associated to an object of the scheme-variety source category. -/
def SchemeVarietyCat.toScheme (X : SchemeVarietyCat k) : Scheme.{u} :=
  varietyAssociatedScheme X.toVariety X.hasAffineOpenBasis

end AlgClosed

end Hartshorne
