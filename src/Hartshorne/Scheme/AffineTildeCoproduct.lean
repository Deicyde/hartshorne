/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AffineTildeLocalization
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The affine tilde functor preserves direct sums

The affine tilde functor is a left adjoint, so it preserves arbitrary
same-universe coproducts.  We record both the natural isomorphism of colimit
functors and its source-facing component for a family of modules.
-/

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- Naturality, in a discrete diagram, of the fact that affine tilde
preserves coproducts. -/
noncomputable def affineTildeCoproductNatIso
    (R : CommRingCat.{u}) (ι : Type u) :
    (colim : Functor (Functor (Discrete ι) (ModuleCat.{u} R))
      (ModuleCat.{u} R)) ⋙
        tilde.functor R ≅
      (Functor.whiskeringRight (Discrete ι) (ModuleCat.{u} R)
        ((Spec R).Modules)).obj (tilde.functor R) ⋙
        (colim : Functor (Functor (Discrete ι) (Spec R).Modules)
          (Spec R).Modules) :=
  preservesColimitNatIso (J := Discrete ι) (tilde.functor R)

/-- For every family of `R`-modules, tilde of its direct sum is canonically
isomorphic to the direct sum of the associated tilde sheaves. -/
noncomputable def affineTildeCoproductIso
    {R : CommRingCat.{u}} {ι : Type u}
    (M : ι → ModuleCat.{u} R) :
    tilde (∐ M) ≅ ∐ fun i ↦ tilde (M i) :=
  PreservesCoproduct.iso (tilde.functor R) M

end Hartshorne
