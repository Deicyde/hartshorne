/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletion

/-!
# Noetherian formal schemes

Hartshorne, *Algebraic Geometry*, II.9, definition of a Noetherian formal scheme (p. 194).

A Noetherian formal scheme is a locally ringed space admitting a finite open cover whose members
are isomorphic, as locally ringed spaces, to formal completions of Noetherian schemes along closed
subschemes. The ambient Noetherian schemes need not be affine, and the structure sheaf is a sheaf
of rings, with no topology on the section rings. Morphisms of Noetherian formal schemes are
morphisms of locally ringed spaces.

Closed subschemes of a scheme `X` are represented by quasi-coherent ideal subsheaves of `𝒪_X`, and
the completion along one is `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletion`.

* `Hartshorne.IsNoetherianFormalScheme X`: the locally ringed space `X` is a Noetherian formal
  scheme.
* `Hartshorne.IsNoetherianFormalScheme.of_iso`: the property is invariant under isomorphisms of
  locally ringed spaces.
* `Hartshorne.NoetherianFormalScheme`: the category of Noetherian formal schemes, a structure
  extending `LocallyRingedSpace` whose morphisms are morphisms of locally ringed spaces.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hartshorne

universe u

/-- Two open immersions of locally ringed spaces with the same image have isomorphic sources. -/
private def isoOfRangeEqOpenImmersion {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := LocallyRingedSpace.IsOpenImmersion.lift g f e.le
  inv := LocallyRingedSpace.IsOpenImmersion.lift f g e.ge
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

/-- Restricting along the preimage of an open under an isomorphism of locally ringed spaces gives
an isomorphic locally ringed space. -/
private def restrictPreimageIso {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (V : Opens Y.carrier) :
    X.restrict ((Opens.map e.hom.base).obj V).isOpenEmbedding ≅ Y.restrict V.isOpenEmbedding :=
  isoOfRangeEqOpenImmersion (X.ofRestrict _ ≫ e.hom) (Y.ofRestrict V.isOpenEmbedding) <| by
    have hbij : Function.Bijective e.hom.base :=
      (TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso e)).bijective
    ext y
    simp only [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]
    change y ∈ e.hom.base '' Set.range (Opens.inclusion' _) ↔ y ∈ Set.range (Opens.inclusion' V)
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hbij.2 y
      exact ⟨x, hy, rfl⟩

/-- **Noetherian formal schemes** (Hartshorne II.9, p. 194): a locally ringed space `X` is a
Noetherian formal scheme when it has a finite open cover `X = ⋃ Uᵢ` such that each `Uᵢ`, with the
restricted structure sheaf, is isomorphic as a locally ringed space to the formal completion of a
Noetherian scheme along a closed subscheme (given by a quasi-coherent ideal subsheaf). The ambient
schemes need not be affine, and no topology is put on the section rings. -/
def IsNoetherianFormalScheme (X : LocallyRingedSpace.{u}) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (U : ι → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i, ∃ (Y : Scheme.{u}) (_ : IsNoetherian Y) (I : QuasicoherentIdealSubsheaf Y),
      Nonempty (X.restrict (U i).isOpenEmbedding ≅ I.formalCompletion)

/-- Being a Noetherian formal scheme is invariant under isomorphisms of locally ringed spaces:
a finite cover by completions of Noetherian schemes transports along the isomorphism. -/
theorem IsNoetherianFormalScheme.of_iso {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y)
    (hY : IsNoetherianFormalScheme Y) : IsNoetherianFormalScheme X := by
  obtain ⟨ι, hι, V, hV, hchart⟩ := hY
  refine ⟨ι, hι, fun i => (Opens.map e.hom.base).obj (V i), ?_, fun i => ?_⟩
  · exact (Opens.map_iSup e.hom.base V).symm.trans (by rw [hV]; rfl)
  · obtain ⟨Z, hZ, I, ⟨f⟩⟩ := hchart i
    exact ⟨Z, hZ, I, ⟨restrictPreimageIso e (V i) ≪≫ f⟩⟩

/-- Being a Noetherian formal scheme is invariant under isomorphisms of locally ringed spaces. -/
theorem IsNoetherianFormalScheme.iso_iff {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    IsNoetherianFormalScheme X ↔ IsNoetherianFormalScheme Y :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

/-- **The category of Noetherian formal schemes** (Hartshorne II.9, p. 194): a Noetherian formal
scheme is a locally ringed space that is a Noetherian formal scheme in the sense of
`IsNoetherianFormalScheme`. -/
structure NoetherianFormalScheme extends LocallyRingedSpace.{u} where
  /-- The underlying locally ringed space has a finite cover by completions of Noetherian
  schemes along closed subschemes. -/
  isNoetherianFormalScheme : IsNoetherianFormalScheme toLocallyRingedSpace

namespace NoetherianFormalScheme

/-- Morphisms of Noetherian formal schemes are exactly morphisms of the underlying locally ringed
spaces (Hartshorne II.9, p. 194). -/
instance category : Category NoetherianFormalScheme.{u} where
  Hom X Y := X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace
  id X := 𝟙 X.toLocallyRingedSpace
  comp f g := f ≫ g

/-- The forgetful functor from Noetherian formal schemes to locally ringed spaces. -/
@[simps]
def forgetToLocallyRingedSpace : NoetherianFormalScheme.{u} ⥤ LocallyRingedSpace.{u} where
  obj X := X.toLocallyRingedSpace
  map f := f

/-- The forgetful functor to locally ringed spaces is fully faithful. -/
def fullyFaithfulForgetToLocallyRingedSpace : forgetToLocallyRingedSpace.{u}.FullyFaithful where
  preimage f := f

instance : forgetToLocallyRingedSpace.{u}.Full :=
  fullyFaithfulForgetToLocallyRingedSpace.full

instance : forgetToLocallyRingedSpace.{u}.Faithful :=
  fullyFaithfulForgetToLocallyRingedSpace.faithful

end NoetherianFormalScheme

end Hartshorne
