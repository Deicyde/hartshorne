/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SheafCohomology
import Hartshorne.Cohomology.RightDerivedLongExactSequence

/-!
# The long exact sequence of sheaf cohomology

Hartshorne, *Algebraic Geometry*, III.2, p. 207: since `H^n(X,-) = R^nΓ(X,-)` is a right derived
functor, a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of abelian sheaves on `X` gives
connecting homomorphisms `H^n(X,F'') ⟶ H^{n+1}(X,F')` (`Hartshorne.sheafCohomologyδ`), natural
in morphisms of short exact sequences (`Hartshorne.sheafCohomologyδ_naturality`), and an exact
sequence

`0 ⟶ H^0(X,F') ⟶ H^0(X,F) ⟶ H^0(X,F'') ⟶ H^1(X,F') ⟶ ⋯`

(`Hartshorne.sheafCohomology_mono_map_f`, `Hartshorne.sheafCohomology_exact₂`,
`Hartshorne.sheafCohomology_exact₃`, `Hartshorne.sheafCohomology_exact₁`).

These are the statements of `Hartshorne.rightDerivedδ` and its companions, specialised to the
global section functor `Γ(X,-) = Hartshorne.sheafSectionsOver ⊤`.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Hartshorne

open RightDerivedLES

variable {X : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
  (hS : S.ShortExact)

/-- The connecting homomorphism `H^n(X,F'') ⟶ H^{n+1}(X,F')` of sheaf cohomology attached to a
short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of abelian sheaves. -/
noncomputable def sheafCohomologyδ (n : ℕ) :
    (sheafCohomology X n).obj S.X₃ ⟶ (sheafCohomology X (n + 1)).obj S.X₁ :=
  rightDerivedδ (sheafSectionsOver (X := X) ⊤) hS n

/-- `H^n(X,F) ⟶ H^n(X,F'') ⟶ H^{n+1}(X,F')` composes to zero. -/
@[reassoc (attr := simp)]
theorem sheafCohomology_map_g_comp_δ (n : ℕ) :
    (sheafCohomology X n).map S.g ≫ sheafCohomologyδ hS n = 0 :=
  Horseshoe.map_g_comp_δ _ hS _ _ n

/-- `H^n(X,F'') ⟶ H^{n+1}(X,F') ⟶ H^{n+1}(X,F)` composes to zero. -/
@[reassoc (attr := simp)]
theorem sheafCohomologyδ_comp_map_f (n : ℕ) :
    sheafCohomologyδ hS n ≫ (sheafCohomology X (n + 1)).map S.f = 0 :=
  Horseshoe.δ_comp_map_f _ hS _ _ n

include hS in
/-- The long exact sequence of sheaf cohomology starts with `0`:
`H^0(X,F') ⟶ H^0(X,F)` is a monomorphism. -/
theorem sheafCohomology_mono_map_f : Mono ((sheafCohomology X 0).map S.f) :=
  rightDerived_mono_map_f _ hS

include hS in
/-- Exactness of `H^n(X,F') ⟶ H^n(X,F) ⟶ H^n(X,F'')`. -/
theorem sheafCohomology_exact₂ (n : ℕ) :
    (ShortComplex.mk ((sheafCohomology X n).map S.f) ((sheafCohomology X n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact :=
  rightDerived_exact₂ _ hS n

/-- Exactness of `H^n(X,F) ⟶ H^n(X,F'') ⟶ H^{n+1}(X,F')`. -/
theorem sheafCohomology_exact₃ (n : ℕ) :
    (ShortComplex.mk ((sheafCohomology X n).map S.g) (sheafCohomologyδ hS n)
      (sheafCohomology_map_g_comp_δ hS n)).Exact :=
  rightDerived_exact₃ _ hS n

/-- Exactness of `H^n(X,F'') ⟶ H^{n+1}(X,F') ⟶ H^{n+1}(X,F)`. -/
theorem sheafCohomology_exact₁ (n : ℕ) :
    (ShortComplex.mk (sheafCohomologyδ hS n) ((sheafCohomology X (n + 1)).map S.f)
      (sheafCohomologyδ_comp_map_f hS n)).Exact :=
  rightDerived_exact₁ _ hS n

/-- The connecting homomorphisms of sheaf cohomology are natural in morphisms of short exact
sequences of abelian sheaves. -/
theorem sheafCohomologyδ_naturality {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n : ℕ) :
    sheafCohomologyδ hS₁ n ≫ (sheafCohomology X (n + 1)).map φ.τ₁ =
      (sheafCohomology X n).map φ.τ₃ ≫ sheafCohomologyδ hS₂ n :=
  rightDerivedδ_naturality _ φ hS₁ hS₂ n

end Hartshorne
