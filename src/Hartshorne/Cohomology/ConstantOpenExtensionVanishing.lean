/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.OpenClosedExtensionSequence
import Hartshorne.Cohomology.ClosedPushforwardCohomology
import Hartshorne.Cohomology.SheafCohomologyFlasque
import Hartshorne.Cohomology.SheafCohomologyLongExactSequence
import Hartshorne.Scheme.ConstantSheaf
import Hartshorne.Topology.Subspace

/-!
# Vanishing for `ℤ_U`

Hartshorne, *Algebraic Geometry*, III.2, proof of Theorem 2.7, Step 5 (p. 211).

Let `X` be an irreducible Noetherian space of dimension `n` and assume Grothendieck vanishing
for all proper closed subsets of `X`. For an open `U ⊆ X` with inclusion `j`, the sheaf
`ℤ_U = j_!(ℤ|_U)` has `H^i(X, ℤ_U) = 0` for `i > n`
(`sheafCohomology_isZero_openExtensionByZero_constantSheaf`). The proof works for the constant
sheaf of any abelian group `A` in place of `ℤ`.

With `Y = X \ U`, the open–closed sequence `0 ⟶ j_!(A|_U) ⟶ A ⟶ i_*(A|_Y) ⟶ 0` gives
`H^{i-1}(X, i_*(A|_Y)) ⟶ H^i(X, j_!(A|_U)) ⟶ H^i(X, A)`. The right term vanishes because the
constant sheaf on an irreducible space is flasque. The left term is `H^{i-1}(Y, A|_Y)`, which
vanishes by the hypothesis on `Y` since `dim Y < n ≤ i - 1`. If `U` is empty, `j_!(A|_U)` is
zero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

universe u

variable {X : TopCat.{u}}

/-- **Vanishing for `ℤ_U`** (Hartshorne III.2, proof of Theorem 2.7, Step 5). Let `X` be an
irreducible Noetherian space of dimension `n`, and assume that for every proper closed subset
`Y ⊂ X`, every abelian sheaf `G` on `Y` and every `i > dim Y`, `H^i(Y, G) = 0`. Then for every
open `U ⊆ X`, every abelian group `A` and every `i > n`, `H^i(X, j_!(A|_U)) = 0`, where `A` is the
constant sheaf and `j : U ⟶ X` the inclusion. -/
theorem sheafCohomology_isZero_openExtensionByZero_constantSheaf [IrreducibleSpace X]
    [NoetherianSpace X] {n : ℕ} (hdim : topologicalKrullDim X = n)
    (hvan : ∀ Y : Set X, IsClosed Y → Y ⊂ Set.univ →
      ∀ (G : (TopCat.of Y).Sheaf AddCommGrpCat.{u}) (i : ℕ),
        topologicalKrullDim Y < (i : WithBot ℕ∞) → IsZero ((sheafCohomology (TopCat.of Y) i).obj G))
    (U : Opens X) (A : AddCommGrpCat.{u}) (i : ℕ) (hi : n < i) :
    IsZero ((sheafCohomology X i).obj (openExtensionByZero U
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj (constantSheaf X A)))) := by
  obtain ⟨Y, hY, rfl⟩ : ∃ (Y : Set X) (hY : IsClosed Y), closedComplementOpens Y hY = U :=
    ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl, Opens.ext (compl_compl _)⟩
  let F := constantSheaf X A
  set S := (openClosedExtensionSequence Y hY).map ((evaluation _ _).obj F) with hSdef
  have hS : S.ShortExact := openClosedExtensionSequence_shortExact Y hY F
  change IsZero ((sheafCohomology X i).obj S.X₁)
  by_cases hYu : Y = Set.univ
  · refine Functor.map_isZero _ ?_
    rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
    intro x
    exact openExtensionByZero_stalk_isZero_of_not_mem _ _ x
      (fun hx => hx (hYu ▸ Set.mem_univ x))
  · have hss : Y ⊂ Set.univ := Set.ssubset_univ_iff.mpr hYu
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have := isFlasque_constantSheaf_of_irreducibleSpace X A
    have h₂ : IsZero ((sheafCohomology X (m + 1)).obj S.X₂) :=
      sheafCohomology_isZero_of_isFlasque F m
    have hdimY : topologicalKrullDim Y < (m : WithBot ℕ∞) :=
      (topologicalKrullDim_lt_of_isClosed_ssubset hY hss hdim).trans_le
        (by exact_mod_cast (show n ≤ m by omega))
    have h₃ : IsZero ((sheafCohomology X m).obj S.X₃) :=
      (hvan Y hY hss _ m hdimY).of_iso
        (closedPushforwardCohomologyIso Y hY
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (closedSubspaceInclusion X Y)).obj F) m).symm
    exact (sheafCohomology_exact₁ hS m).isZero_X₂ (h₃.eq_of_src _ _) (h₂.eq_of_tgt _ _)

end Hartshorne
