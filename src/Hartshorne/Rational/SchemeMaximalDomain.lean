/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# The maximal domain of a rational map of schemes

Hartshorne, *Algebraic Geometry*, V.5, the maximal domain of definition and the
fundamental points of a birational transformation, p. 410, in the language of
schemes.

A rational map `T : X ⤏ Y` of schemes is an equivalence class of morphisms
defined on dense open subschemes. Its maximal domain `Dom(T)` is the union of
the domains of all its representatives. When `X` is reduced and `Y` is
separated, two representatives agree on their common domain, so they glue to a
morphism `Dom(T) ⟶ Y` representing `T`; `Dom(T)` is then the largest open
subscheme carrying a representative, and the morphism on it is unique. The
fundamental locus is the closed complement `X \ Dom(T)`, and the fundamental
points are its closed points.

The statements are made for an arbitrary rational map from a reduced scheme to
a separated scheme. This contains Hartshorne's setting: projective varieties
over a field are integral, hence reduced, and separated, and a birational
transformation is in particular a rational map. The definition of `Dom(T)`
itself uses no hypothesis on `X`, `Y` or `T`.

The underlying construction is Mathlib's `Scheme.RationalMap.domain` and
`Scheme.RationalMap.toPartialMap`; this file packages it with the properties
stated by Hartshorne.

## Main definitions and results

* `Hartshorne.SchemeRationalMap.dom`: the maximal domain `Dom(T)`, an open
  subscheme of `X`.
* `Hartshorne.SchemeRationalMap.domRep`, `Hartshorne.SchemeRationalMap.domHom`:
  the representative of `T` on `Dom(T)` and its morphism `Dom(T) ⟶ Y`.
* `Hartshorne.SchemeRationalMap.domRep_represents`: it represents `T`.
* `Hartshorne.SchemeRationalMap.homOfLE_domHom`: it restricts to every
  representative.
* `Hartshorne.SchemeRationalMap.le_dom`, `Hartshorne.SchemeRationalMap.isGreatest_dom`:
  maximality.
* `Hartshorne.SchemeRationalMap.domHom_unique`: uniqueness of the morphism.
* `Hartshorne.SchemeRationalMap.fundamentalLocus`,
  `Hartshorne.SchemeRationalMap.fundamentalPoints`.
-/

namespace Hartshorne

namespace SchemeRationalMap

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- **Hartshorne V.5, p. 410.** The maximal domain `Dom(T)` of a rational map
`T : X ⤏ Y`: the union of the domains of all partial maps representing `T`. -/
def dom (T : X ⤏ Y) : X.Opens :=
  T.domain

theorem mem_dom_iff {T : X ⤏ Y} {x : X} :
    x ∈ dom T ↔ ∃ g : X.PartialMap Y, x ∈ g.domain ∧ g.toRationalMap = T :=
  Scheme.RationalMap.mem_domain

theorem dense_dom (T : X ⤏ Y) : Dense (dom T : Set X) :=
  T.dense_domain

/-- **Maximality.** The domain of every partial map representing `T` lies in
`Dom(T)`. -/
theorem le_dom {T : X ⤏ Y} (g : X.PartialMap Y) (hg : g.toRationalMap = T) :
    g.domain ≤ dom T :=
  hg ▸ g.le_domain_toRationalMap

/-- **Hartshorne V.5, p. 410.** For `X` reduced and `Y` separated, the
representatives of `T` glue to a partial map defined on all of `Dom(T)`. -/
noncomputable def domRep [IsReduced X] [Y.IsSeparated] (T : X ⤏ Y) : X.PartialMap Y :=
  T.toPartialMap

theorem domRep_domain [IsReduced X] [Y.IsSeparated] (T : X ⤏ Y) :
    (domRep T).domain = dom T :=
  rfl

/-- **Hartshorne V.5, p. 410.** The morphism `Dom(T) ⟶ Y` obtained by gluing the
representatives of `T`. -/
noncomputable def domHom [IsReduced X] [Y.IsSeparated] (T : X ⤏ Y) : (dom T).toScheme ⟶ Y :=
  (domRep T).hom

/-- The glued morphism on `Dom(T)` represents `T`. -/
theorem domRep_represents [IsReduced X] [Y.IsSeparated] (T : X ⤏ Y) :
    (domRep T).toRationalMap = T :=
  T.toRationalMap_toPartialMap

/-- The glued morphism on `Dom(T)` restricts to every representative of `T`. -/
theorem homOfLE_domHom [IsReduced X] [Y.IsSeparated] {T : X ⤏ Y} (g : X.PartialMap Y)
    (hg : g.toRationalMap = T) :
    X.homOfLE (le_dom g hg) ≫ domHom T = g.hom := by
  subst hg
  exact g.toPartialMap_toRationalMap_restrict

/-- `Dom(T)` is the largest open subscheme of `X` on which `T` is represented by
a morphism. -/
theorem isGreatest_dom [IsReduced X] [Y.IsSeparated] (T : X ⤏ Y) :
    IsGreatest {U : X.Opens | ∃ g : X.PartialMap Y, g.toRationalMap = T ∧ g.domain = U}
      (dom T) :=
  ⟨⟨domRep T, domRep_represents T, rfl⟩, fun _ ⟨g, hg, hU⟩ => hU ▸ le_dom g hg⟩

/-- **Uniqueness.** A morphism on `Dom(T)` representing `T` is the glued one. -/
theorem domHom_unique [IsReduced X] [Y.IsSeparated] (T : X ⤏ Y) (φ : (dom T).toScheme ⟶ Y)
    (hφ : (⟨dom T, dense_dom T, φ⟩ : X.PartialMap Y).toRationalMap = T) :
    φ = domHom T := by
  have h : (⟨dom T, dense_dom T, φ⟩ : X.PartialMap Y) = domRep T := by
    rw [← Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ _)
      (f := ⟨dom T, dense_dom T, φ⟩) (g := domRep T) rfl,
      ← Scheme.PartialMap.toRationalMap_eq_iff, hφ, domRep_represents]
  exact eq_of_heq (Scheme.PartialMap.mk.inj h).2

/-- **Hartshorne V.5, p. 410.** The fundamental locus `X \ Dom(T)` of a rational
map, a closed subset of `X`. -/
def fundamentalLocus (T : X ⤏ Y) : Closeds X :=
  (dom T).compl

theorem coe_fundamentalLocus (T : X ⤏ Y) :
    (fundamentalLocus T : Set X) = (dom T : Set X)ᶜ :=
  rfl

/-- **Hartshorne V.5, p. 410.** The fundamental points of a rational map: the
closed points of its fundamental locus. -/
def fundamentalPoints (T : X ⤏ Y) : Set X :=
  {x | x ∈ fundamentalLocus T ∧ IsClosed ({x} : Set X)}

theorem mem_fundamentalPoints {T : X ⤏ Y} {x : X} :
    x ∈ fundamentalPoints T ↔ x ∉ dom T ∧ IsClosed ({x} : Set X) :=
  Iff.rfl

end SchemeRationalMap

end Hartshorne
