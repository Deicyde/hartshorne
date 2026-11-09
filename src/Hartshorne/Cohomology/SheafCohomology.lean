/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Sheaf cohomology

Hartshorne, *Algebraic Geometry*, III.2, definition on p. 207.

For a topological space `X : TopCat.{u}`, the category `TopCat.Sheaf AddCommGrpCat.{u} X` of
abelian sheaves on `X` is a Grothendieck abelian category, hence has enough injectives and
injective resolutions. The functor of sections over an open subset `V`,
`Hartshorne.sheafSectionsOver V`, is additive and left exact; for `V = ⊤` it is the global
section functor `Γ(X,-)`.

`Hartshorne.sheafCohomology X n` is the `n`-th right derived functor `H^n(X,-) = R^nΓ(X,-)` of
global sections, computed from injective resolutions, and `Hartshorne.sheafCohomologyZeroIso`
is the natural isomorphism `H^0(X,-) ≅ Γ(X,-)`.

`sheafCohomology X n` is reducibly `(sheafSectionsOver ⊤).rightDerived n`, so the results stated
for that functor elsewhere in the project (the long exact sequence via `Hartshorne.rightDerivedδ`,
cohomology with supports, Mayer–Vietoris) apply to it directly.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Hartshorne

variable {X : TopCat.{u}}

/-- Sections over an open subset, as a functor on abelian sheaves. -/
noncomputable abbrev sheafSectionsOver (V : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ (evaluation _ _).obj (op V)

/-- Sections over an open subset preserve finite limits. -/
noncomputable instance sheafSectionsOver_preservesFiniteLimits (V : Opens X) :
    PreservesFiniteLimits (sheafSectionsOver V) := by
  have h₁ : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X) := inferInstance
  have h₂ : PreservesFiniteLimits ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)) :=
    inferInstance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂

/-- Sections over an open subset are additive. -/
instance sheafSectionsOver_additive (V : Opens X) : (sheafSectionsOver V).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (X)

/-- **Sheaf cohomology** (Hartshorne III.2, p. 207). For `n : ℕ`, the functor
`H^n(X,-) : 𝔄𝔟(X) ⥤ 𝔄𝔟` is the `n`-th right derived functor of the global section functor
`Γ(X,-)`, computed from injective resolutions of abelian sheaves. -/
noncomputable abbrev sheafCohomology (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  (sheafSectionsOver (X := X) ⊤).rightDerived n

/-- The degree-zero sheaf cohomology is the global section functor: `H^0(X,-) ≅ Γ(X,-)`,
naturally, because `Γ(X,-)` is left exact. -/
noncomputable def sheafCohomologyZeroIso :
    sheafCohomology X 0 ≅ sheafSectionsOver (X := X) ⊤ :=
  (sheafSectionsOver (X := X) ⊤).rightDerivedZeroIsoSelf

end Hartshorne
