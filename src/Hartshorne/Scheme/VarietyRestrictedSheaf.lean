/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VarietyClosedPoints
import Hartshorne.Scheme.GenericCompletionSheaf

/-!
# Restricting the structure sheaf recovers regular functions

Hartshorne, *Algebraic Geometry*, II.2, the restricted-sheaf clause of
Proposition 2.6 (p. 78).

Let `V` be a variety with an affine-open basis over an algebraically closed
field `k`, and identify `V` with the subspace of closed points of its associated
scheme `t(V)` via the homeomorphism induced by `α_V`. Then the inverse image of
the structure sheaf of `t(V)`, first to the closed-point subspace and then along
this homeomorphism, is canonically isomorphic to the sheaf of regular functions
on `V`.

## Proof

* The composite of the homeomorphism `V ≃ {closed points}` with the inclusion
  of the closed points is `α_V : V → t(V)` itself.
* Taking preimages under `α_V` is an order isomorphism from the opens of `t(V)`
  to the opens of `V`, so the functor `Opens.map α_V` is an equivalence; hence
  pushforward of presheaves along `α_V` (precomposition with this equivalence)
  is an equivalence, and pushforward of sheaves along `α_V` is fully faithful.
* The structure sheaf of `t(V)` is by definition `α_* 𝒪_V`. For the
  inverse image/pushforward adjunction along `α_V`, full faithfulness of the
  right adjoint makes the counit `α⁻¹ α_* 𝒪_V → 𝒪_V` an isomorphism (both for
  presheaf and for sheaf inverse images).
* Sheaf inverse images compose (up to canonical isomorphism) by uniqueness of
  left adjoints, which splits the inverse image along `α_V` into the inverse
  image to the closed-point subspace followed by the inverse image along the
  homeomorphism.

## Main definitions and results

* `Hartshorne.varietyClosedPointsInclusion`: the inclusion of the subspace of
  closed points into `t(V)`, and `Hartshorne.varietyClosedPointsTopIso`: the
  homeomorphism `V ≃ {closed points}` as an isomorphism of topological spaces.
* `Hartshorne.varietyRestrictedSheafIso`: the isomorphism of sheaves of rings on
  `V` between the inverse image of the structure sheaf of `t(V)` (to the closed
  points, then along the homeomorphism) and the sheaf of regular functions.
* `Hartshorne.varietyRestrictedPresheafIso`: the same identification for the
  presheaf inverse image along `α_V`; open-set-wise it identifies the
  sections over an open `U` of `V` with the regular functions on `U`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry

namespace Hartshorne

universe u

/-- Taking preimages under `α : X → t(X)` is an equivalence from the opens of
`t(X)` to the opens of `X` (it is the inverse of the order isomorphism of
opens). -/
instance isEquivalence_opensMap_genericCompletionAlpha (X : TopCat.{u}) :
    (Opens.map (genericCompletionAlpha X)).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
      (genericCompletionOpensOrderIso X).symm.equivalence.functor ≅ _)

/-- Pushforward of presheaves along `α : X → t(X)` is an equivalence. -/
instance isEquivalence_presheafPushforward_genericCompletionAlpha (X : TopCat.{u}) :
    (TopCat.Presheaf.pushforward CommRingCat.{u} (genericCompletionAlpha X)).IsEquivalence :=
  inferInstanceAs
    ((Functor.whiskeringLeft _ _ _).obj (Opens.map (genericCompletionAlpha X)).op).IsEquivalence

/-- Pushforward of sheaves along `α : X → t(X)` is full. -/
instance full_sheafPushforward_genericCompletionAlpha (X : TopCat.{u}) :
    (TopCat.Sheaf.pushforward CommRingCat.{u} (genericCompletionAlpha X)).Full :=
  have : (TopCat.Sheaf.pushforward CommRingCat.{u} (genericCompletionAlpha X) ⋙
      TopCat.Sheaf.forget _ _).Full :=
    inferInstanceAs (TopCat.Sheaf.forget _ _ ⋙ TopCat.Presheaf.pushforward _ _).Full
  Functor.Full.of_comp_faithful _ (TopCat.Sheaf.forget _ _)

/-- Pushforward of sheaves along `α : X → t(X)` is faithful. -/
instance faithful_sheafPushforward_genericCompletionAlpha (X : TopCat.{u}) :
    (TopCat.Sheaf.pushforward CommRingCat.{u} (genericCompletionAlpha X)).Faithful :=
  have : (TopCat.Sheaf.pushforward CommRingCat.{u} (genericCompletionAlpha X) ⋙
      TopCat.Sheaf.forget _ _).Faithful :=
    inferInstanceAs (TopCat.Sheaf.forget _ _ ⋙ TopCat.Presheaf.pushforward _ _).Faithful
  Functor.Faithful.of_comp _ (TopCat.Sheaf.forget _ _)

/-- Inverse images of sheaves of rings compose: `(g ∘ f)⁻¹ ≅ f⁻¹ ∘ g⁻¹`, by
uniqueness of left adjoints of the pushforward `(g ∘ f)_* = g_* ∘ f_*`. -/
def sheafPullbackCompIso {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g) ≅
      TopCat.Sheaf.pullback CommRingCat g ⋙ TopCat.Sheaf.pullback CommRingCat f :=
  Adjunction.leftAdjointUniq (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat (f ≫ g))
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f))

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The inclusion of the subspace of closed points into the associated scheme
`t(V)`. -/
def varietyClosedPointsInclusion (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    TopCat.of
        {z : varietyAssociatedScheme V hV // IsClosed ({z} : Set (varietyAssociatedScheme V hV))} ⟶
      TopCat.of (varietyAssociatedScheme V hV) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val (X := varietyAssociatedScheme V hV)⟩

/-- The homeomorphism `V ≃ {closed points of t(V)}` induced by `α_V`, as an
isomorphism of topological spaces. -/
def varietyClosedPointsTopIso (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    TopCat.of V.carrier ≅
      TopCat.of
        {z : varietyAssociatedScheme V hV // IsClosed ({z} : Set (varietyAssociatedScheme V hV))} :=
  TopCat.isoOfHomeo (varietyClosedPointsHomeomorph V hV)

/-- The homeomorphism `V ≃ {closed points of t(V)}` followed by the inclusion of
the closed points is `α_V`. -/
theorem varietyClosedPointsHomeomorph_comp_inclusion (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) :
    (varietyClosedPointsTopIso V hV).hom ≫
        varietyClosedPointsInclusion V hV =
      genericCompletionAlpha (TopCat.of V.carrier) :=
  rfl

/-- **Hartshorne II.2, Proposition 2.6 (p. 78).** For a variety `V` over an
algebraically closed field (with an affine-open basis), the presheaf inverse
image of the structure sheaf of the associated scheme along `α_V`, i.e. along
the homeomorphism onto the closed points followed by their inclusion, is
canonically isomorphic to the presheaf of regular functions on `V`. -/
def varietyRestrictedPresheafIso (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    (TopCat.Presheaf.pullback CommRingCat
        ((varietyClosedPointsTopIso V hV).hom ≫
          varietyClosedPointsInclusion V hV)).obj (varietyAssociatedScheme V hV).presheaf ≅
      V.regularPresheaf :=
  (asIso (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (genericCompletionAlpha (TopCat.of V.carrier))).counit).app V.regularPresheaf

/-- **Hartshorne II.2, Proposition 2.6 (p. 78).** For a variety `V` over an
algebraically closed field (with an affine-open basis), identify `V` with the
subspace of closed points of its associated scheme via `α_V`. The inverse image
of the structure sheaf of the associated scheme, first to the closed-point
subspace and then along this homeomorphism, is canonically isomorphic to the
sheaf of regular functions on `V`. -/
def varietyRestrictedSheafIso (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    (TopCat.Sheaf.pullback CommRingCat (varietyClosedPointsTopIso V hV).hom).obj
        ((TopCat.Sheaf.pullback CommRingCat (varietyClosedPointsInclusion V hV)).obj
          (varietyAssociatedScheme V hV).sheaf) ≅
      V.regularSheaf :=
  ((sheafPullbackCompIso (varietyClosedPointsTopIso V hV).hom
      (varietyClosedPointsInclusion V hV)).app _).symm ≪≫
    (asIso (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
      (genericCompletionAlpha (TopCat.of V.carrier))).counit).app V.regularSheaf

end Hartshorne
