/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Over

/-!
# Morphisms over a field preserve points with residue field `k`

Hartshorne, *Algebraic Geometry*, II, Exercise 2.15(b).

For a field `k` and a scheme `X` over `Spec k`, `Hartshorne.residueFieldStructureMap k X P` is the
ring homomorphism `k → κ(P)` induced by the structure morphism `X → Spec k`: the composite
`k ≅ Γ(Spec k, 𝒪) → Γ(X, 𝒪) → κ(P)`. The point `P` has residue field `k` when this map is
bijective.

* `Hartshorne.residueFieldStructureMap_comp`: for a morphism `f : X ⟶ Y` over `Spec k`, the map
  `k → κ(P)` factors as `k → κ(f(P)) → κ(P)`.
* `Hartshorne.bijective_residueFieldStructureMap_map`: if `P` has residue field `k`, so does
  `f(P)`. Hartshorne takes `k` algebraically closed in this exercise; the result holds for every
  field `k`.
-/

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

universe u

variable (k : Type u) [Field k]

/-- The ring homomorphism `k → κ(P)` induced by the structure morphism `X → Spec k`, i.e. the
composite `k ≅ Γ(Spec k, 𝒪) → Γ(X, 𝒪) → κ(P)`. -/
noncomputable def residueFieldStructureMap (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    (P : X) : k →+* X.residueField P :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
    X.Γevaluation P).hom

variable {k}

/-- For a morphism `f : X ⟶ Y` over `Spec k`, the map `k → κ(P)` is the composite of
`k → κ(f(P))` with the induced map of residue fields `κ(f(P)) → κ(P)`. -/
theorem residueFieldStructureMap_comp {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    (P : X) :
    residueFieldStructureMap k X P =
      (f.residueFieldMap P).hom.comp (residueFieldStructureMap k Y (f P)) := by
  have hf : f ≫ Y ↘ Spec (CommRingCat.of k) = X ↘ Spec (CommRingCat.of k) :=
    (Scheme.Hom.isOver_iff _).1 inferInstance
  rw [residueFieldStructureMap, residueFieldStructureMap, ← CommRingCat.hom_comp, Category.assoc,
    Category.assoc, Scheme.Γevaluation_naturality, ← hf, Scheme.Hom.comp_appTop, Category.assoc]

/-- **Hartshorne II, Exercise 2.15(b).** Let `f : X ⟶ Y` be a morphism of schemes over a field
`k`. If a point `P` of `X` has residue field `k`, i.e. `k → κ(P)` is bijective, then `f(P)` has
residue field `k`. -/
theorem bijective_residueFieldStructureMap_map {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k))] {P : X}
    (hP : Function.Bijective (residueFieldStructureMap k X P)) :
    Function.Bijective (residueFieldStructureMap k Y (f P)) := by
  rw [residueFieldStructureMap_comp f P, RingHom.coe_comp] at hP
  have hinj : Function.Injective (f.residueFieldMap P).hom := (f.residueFieldMap P).hom.injective
  refine ⟨hP.1.of_comp, fun z => ?_⟩
  obtain ⟨c, hc⟩ := hP.2 ((f.residueFieldMap P).hom z)
  exact ⟨c, hinj hc⟩

end Hartshorne
