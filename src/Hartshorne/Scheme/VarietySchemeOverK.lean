/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VarietyAssociatedScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Over

/-!
# The associated scheme is a scheme over the base field

Hartshorne, *Algebraic Geometry*, II.2, the structure morphism in
Proposition 2.6 (pp. 78–79).

For a variety `V` with an affine-open basis over an algebraically closed field
`k`, the global sections of the associated scheme `t(V)` are the regular
functions on `V`, which form a `k`-algebra. The inclusion of the constant
functions `k → Γ(t(V), 𝒪)` corresponds, under the global-sections–spectrum
adjunction, to a morphism `t(V) → Spec k`; it is the unique morphism whose map
on global sections is this inclusion. This makes `t(V)` a scheme over `k`.

## Main definitions and results

* `Hartshorne.varietyAssociatedSchemeConstants`: the inclusion of constant
  regular functions `k → Γ(t(V), 𝒪)`.
* `Hartshorne.varietyAssociatedSchemeStructureMorphism`: the structure morphism
  `t(V) → Spec k`.
* `Hartshorne.varietyAssociatedScheme_structureMorphism_appTop`: its map on
  global sections is the inclusion of constants.
* `Hartshorne.varietyAssociatedScheme_structureMorphism_unique`: it is the only
  morphism with this map on global sections.
* `Hartshorne.varietyAssociatedSchemeCanonicallyOver`: the associated scheme is
  a scheme over `Spec k` via this structure morphism
  (`Hartshorne.varietyAssociatedScheme_over`), and likewise for the objects of
  the scheme-variety source category
  (`Hartshorne.SchemeVarietyCat.toSchemeCanonicallyOver`).
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

namespace Hartshorne

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Hartshorne II.2, Proposition 2.6 (p. 78).** The inclusion of constant
regular functions `k → Γ(t(V), 𝒪)`: the global sections of the associated
scheme are the regular functions on `V`, a `k`-algebra. -/
def varietyAssociatedSchemeConstants (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    CommRingCat.of k ⟶ Γ(varietyAssociatedScheme V hV, ⊤) :=
  CommRingCat.ofHom (algebraMap k (V.regular _))

/-- **Hartshorne II.2, Proposition 2.6 (pp. 78–79).** The structure morphism
`t(V) → Spec k` of the associated scheme: the morphism corresponding to the
inclusion of constant regular functions under the global-sections–spectrum
adjunction. -/
def varietyAssociatedSchemeStructureMorphism (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) : varietyAssociatedScheme V hV ⟶ Spec (CommRingCat.of k) :=
  ΓSpec.adjunction.homEquiv (varietyAssociatedScheme V hV) (op (CommRingCat.of k))
    (varietyAssociatedSchemeConstants V hV).op

/-- The map on global sections of the structure morphism `t(V) → Spec k` is
the inclusion of constant regular functions (after identifying the global
sections of `Spec k` with `k`). -/
theorem varietyAssociatedScheme_structureMorphism_appTop (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (varietyAssociatedSchemeStructureMorphism V hV).appTop =
      varietyAssociatedSchemeConstants V hV :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

/-- The structure morphism `t(V) → Spec k` is the unique morphism whose map on
global sections is the inclusion of constant regular functions. -/
theorem varietyAssociatedScheme_structureMorphism_unique (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) (f : varietyAssociatedScheme V hV ⟶ Spec (CommRingCat.of k))
    (hf : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop =
      varietyAssociatedSchemeConstants V hV) :
    f = varietyAssociatedSchemeStructureMorphism V hV :=
  ext_to_Spec (hf.trans (varietyAssociatedScheme_structureMorphism_appTop V hV).symm)

/-- **Hartshorne II.2, Proposition 2.6 (pp. 78–79).** The associated scheme
`t(V)` is a scheme over `k`, with structure morphism `t(V) → Spec k` induced by
the constant regular functions. -/
instance varietyAssociatedSchemeCanonicallyOver (V : Variety.{u, u} k)
    (hV : V.HasAffineOpenBasis) :
    (varietyAssociatedScheme V hV).CanonicallyOver (Spec (CommRingCat.of k)) where
  hom := varietyAssociatedSchemeStructureMorphism V hV

/-- The structure morphism of the associated scheme as a scheme over `k`. -/
theorem varietyAssociatedScheme_over (V : Variety.{u, u} k) (hV : V.HasAffineOpenBasis) :
    varietyAssociatedScheme V hV ↘ Spec (CommRingCat.of k) =
      varietyAssociatedSchemeStructureMorphism V hV :=
  rfl

/-- The scheme associated to an object of the scheme-variety source category is
a scheme over `k`. -/
instance SchemeVarietyCat.toSchemeCanonicallyOver (X : SchemeVarietyCat k) :
    X.toScheme.CanonicallyOver (Spec (CommRingCat.of k)) :=
  varietyAssociatedSchemeCanonicallyOver X.toVariety X.hasAffineOpenBasis

end Hartshorne
