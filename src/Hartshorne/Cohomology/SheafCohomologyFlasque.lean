/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SheafCohomology
import Hartshorne.Cohomology.CohomologyWithSupports

/-!
# Flasque sheaves are acyclic

Hartshorne, *Algebraic Geometry*, III.2, Proposition 2.5 (p. 208): if `F` is a flasque abelian
sheaf on a topological space `X`, then `H^n(X,F) = 0` for every `n > 0`
(`Hartshorne.sheafCohomology_isZero_of_isFlasque`).

The proof is dimension shifting (`Hartshorne.isRightAcyclic_of_shortExact_injective`): embed `F`
into an injective sheaf `I`, which is flasque (`Hartshorne.injectiveAbelianSheaf_isFlasque`);
the quotient `I/F` is flasque, and `Γ(X,I) ⟶ Γ(X,I/F)` is surjective because `F` is flasque.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Hartshorne

variable {X : TopCat.{u}}

/-- Flasque abelian sheaves are acyclic for the global section functor `Γ(X,-)`. -/
theorem isRightAcyclic_sheafSectionsOver_top_of_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] : IsRightAcyclic (sheafSectionsOver (X := X) ⊤) F :=
  isRightAcyclic_of_shortExact_injective (sheafSectionsOver (X := X) ⊤) (fun G => G.IsFlasque)
    (fun S hS h₁ h₂ => by
      have := h₁
      have := injectiveAbelianSheaf_isFlasque S.X₂
      exact ⟨TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS,
        TopCat.Sheaf.IsFlasque.epi_of_shortExact hS⟩) F inferInstance

/-- **Flasque sheaves are acyclic** (Hartshorne III.2, Proposition 2.5). If `F` is a flasque
abelian sheaf on `X`, then `H^n(X,F) = 0` for every positive degree `n`, here written `n + 1`. -/
theorem sheafCohomology_isZero_of_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] (n : ℕ) : IsZero ((sheafCohomology X (n + 1)).obj F) :=
  isRightAcyclic_sheafSectionsOver_top_of_isFlasque F n

end Hartshorne
