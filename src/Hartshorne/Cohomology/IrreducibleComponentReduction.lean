/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.OpenClosedExtensionSequence
import Hartshorne.Cohomology.ClosedPushforwardCohomology
import Hartshorne.Cohomology.SheafCohomologyLongExactSequence
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.KrullDimension

/-!
# Reduction of Grothendieck vanishing to irreducible closed subsets

Hartshorne, *Algebraic Geometry*, III.2, proof of Theorem 2.7, Step 1 (p. 210).

Fix `n : ℕ`. If every irreducible closed subset `Z` of a Noetherian space `X` with `dim Z ≤ n`
has `H^i(Z, G) = 0` for all abelian sheaves `G` and all `i > n`, and `dim X ≤ n`, then
`H^i(X, F) = 0` for all abelian sheaves `F` on `X` and all `i > n`
(`sheafCohomology_isZero_of_forall_irreducible_closed`).

Instead of inducting on the number of irreducible components, the proof inducts on closed
subsets `W ⊆ X` (Noetherian induction), proving vanishing for every sheaf whose stalks vanish
outside `W` (`sheafCohomology_isZero_of_stalk_isZero_off`). For such a sheaf `F` and a closed
`A ⊆ X`, the open–closed sequence `0 ⟶ j_!(F|_U) ⟶ F ⟶ i_*(F|_A) ⟶ 0` (with `U = X \ A`)
has `i_*(F|_A)` supported in `A` and `j_!(F|_U)` supported in `W \ A`. If `W` is irreducible,
take `A = W`: then `j_!(F|_U) = 0` and `H^i(X, i_*(F|_W)) = H^i(W, F|_W) = 0`. If `W` is
reducible, write `W = A ∪ B` with `A, B` proper closed subsets and apply the induction
hypothesis to `A` and `B`. If `W` is empty, `F = 0`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

universe u

variable {X : TopCat.{u}}

/-- An abelian sheaf whose stalks all vanish has vanishing cohomology. -/
private theorem sheafCohomology_isZero_of_forall_stalk {F : X.Sheaf AddCommGrpCat.{u}}
    (hF : ∀ x : X, IsZero (F.presheaf.stalk x)) (i : ℕ) :
    IsZero ((sheafCohomology X i).obj F) :=
  Functor.map_isZero _ ((TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero F).2 hF)

/-- In the open–closed sequence for a closed `A`, the term `j_!(F|_U)` has zero stalks at the
points of `A` and at the points where `F` has zero stalk. -/
private theorem openClosedOpenPart_stalk_isZero (A : Set X) (hA : IsClosed A)
    (F : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ A ∨ IsZero (F.presheaf.stalk x)) :
    IsZero (((openClosedOpenPart A hA).obj F).presheaf.stalk x) := by
  rcases hx with hx | hx
  · exact openExtensionByZero_stalk_isZero_of_not_mem _ _ x (fun h => h hx)
  · have hS := openClosedExtensionSequence_shortExact A hA F
    have hmono := (TopCat.Presheaf.mono_iff_stalk_mono _).1 hS.mono_f x
    exact @IsZero.of_mono _ _ _ _ _ _ hmono hx

/-- In the open–closed sequence for a closed `A`, the term `i_*(F|_A)` has zero stalks off
`A`. -/
private theorem openClosedClosedPart_stalk_isZero (A : Set X) (hA : IsClosed A)
    (F : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∉ A) :
    IsZero (((openClosedClosedPart A).obj F).presheaf.stalk x) :=
  (isZero_zero _).of_iso (closedExtensionByZeroOffImageStalkIso A hA _ x hx)

/-- The long exact sequence for a closed `A`: if both outer terms of the open–closed sequence
have vanishing `H^i`, so does `F`. -/
private theorem sheafCohomology_isZero_of_openClosed (A : Set X) (hA : IsClosed A)
    (F : X.Sheaf AddCommGrpCat.{u}) (i : ℕ)
    (h₁ : IsZero ((sheafCohomology X i).obj ((openClosedOpenPart A hA).obj F)))
    (h₃ : IsZero ((sheafCohomology X i).obj ((openClosedClosedPart A).obj F))) :
    IsZero ((sheafCohomology X i).obj F) :=
  (sheafCohomology_exact₂ (openClosedExtensionSequence_shortExact A hA F) i).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- The irreducible case: a sheaf supported in an irreducible closed `W` with
`H^i(W, -) = 0`. -/
private theorem sheafCohomology_isZero_of_supported_irreducible (W : Set X) (hW : IsClosed W)
    (F : X.Sheaf AddCommGrpCat.{u}) (hF : ∀ x : X, x ∉ W → IsZero (F.presheaf.stalk x)) (i : ℕ)
    (hvan : IsZero ((sheafCohomology (TopCat.of W) i).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (closedSubspaceInclusion X W)).obj F))) :
    IsZero ((sheafCohomology X i).obj F) := by
  refine sheafCohomology_isZero_of_openClosed W hW F i ?_ ?_
  · refine sheafCohomology_isZero_of_forall_stalk (fun x => ?_) _
    by_cases hx : x ∈ W
    · exact openClosedOpenPart_stalk_isZero _ _ F x (Or.inl hx)
    · exact openClosedOpenPart_stalk_isZero _ _ F x (Or.inr (hF x hx))
  · exact hvan.of_iso (closedPushforwardCohomologyIso W hW
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (closedSubspaceInclusion X W)).obj F) i).symm

/-- The reducible case: a sheaf supported in `W ⊆ A ∪ B`, with vanishing for sheaves supported
in `A` and in `B`. -/
private theorem sheafCohomology_isZero_of_supported_union (W A B : Set X) (hA : IsClosed A)
    (hcov : W ⊆ A ∪ B) (F : X.Sheaf AddCommGrpCat.{u})
    (hF : ∀ x : X, x ∉ W → IsZero (F.presheaf.stalk x)) (i : ℕ)
    (hIA : ∀ G : X.Sheaf AddCommGrpCat.{u}, (∀ x : X, x ∉ A → IsZero (G.presheaf.stalk x)) →
      IsZero ((sheafCohomology X i).obj G))
    (hIB : ∀ G : X.Sheaf AddCommGrpCat.{u}, (∀ x : X, x ∉ B → IsZero (G.presheaf.stalk x)) →
      IsZero ((sheafCohomology X i).obj G)) :
    IsZero ((sheafCohomology X i).obj F) := by
  refine sheafCohomology_isZero_of_openClosed A hA F i ?_ ?_
  · refine hIB _ fun x hx => ?_
    by_cases hxA : x ∈ A
    · exact openClosedOpenPart_stalk_isZero _ _ F x (Or.inl hxA)
    · refine openClosedOpenPart_stalk_isZero _ _ F x (Or.inr (hF x fun hxW => ?_))
      rcases hcov hxW with h | h
      · exact hxA h
      · exact hx h
  · exact hIA _ fun x hx => openClosedClosedPart_stalk_isZero A hA F x hx

/-- **Noetherian induction for Grothendieck vanishing.** Under the hypotheses of
`sheafCohomology_isZero_of_forall_irreducible_closed`, every abelian sheaf on `X` whose stalks
vanish off a closed subset `W` has `H^i = 0` for `i > n`. -/
theorem sheafCohomology_isZero_of_stalk_isZero_off [NoetherianSpace X] {n : ℕ}
    (hX : topologicalKrullDim X ≤ n)
    (hirr : ∀ Z : Set X, IsClosed Z → IsIrreducible Z → topologicalKrullDim Z ≤ n →
      ∀ (G : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) (i : ℕ), n < i →
        IsZero ((sheafCohomology (TopCat.of Z) i).obj G))
    (W : Closeds X) (i : ℕ) (hi : n < i) :
    ∀ (F : X.Sheaf AddCommGrpCat.{u}), (∀ x : X, x ∉ W → IsZero (F.presheaf.stalk x)) →
      IsZero ((sheafCohomology X i).obj F) := by
  induction W using WellFoundedLT.induction with
  | ind W IH =>
  intro F hF
  by_cases hW : (W : Set X).Nonempty
  · by_cases hWirr : IsIrreducible (W : Set X)
    · exact sheafCohomology_isZero_of_supported_irreducible W W.isClosed F hF i
        (hirr W W.isClosed hWirr ((topologicalKrullDim_subspace_le X W).trans hX) _ i hi)
    · have hpre : ¬ IsPreirreducible (W : Set X) := fun h => hWirr ⟨hW, h⟩
      rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
      push Not at hpre
      obtain ⟨z₁, z₂, hz₁, hz₂, hcov, hn₁, hn₂⟩ := hpre
      let A : Closeds X := ⟨(W : Set X) ∩ z₁, W.isClosed.inter hz₁⟩
      let B : Closeds X := ⟨(W : Set X) ∩ z₂, W.isClosed.inter hz₂⟩
      have hAW : A < W := lt_of_le_of_ne (fun _ h => h.1) fun h =>
        hn₁ fun x hx => ((SetLike.ext_iff.1 h x).2 hx).2
      have hBW : B < W := lt_of_le_of_ne (fun _ h => h.1) fun h =>
        hn₂ fun x hx => ((SetLike.ext_iff.1 h x).2 hx).2
      refine sheafCohomology_isZero_of_supported_union W A B A.isClosed
        (fun x hx => (hcov hx).imp (fun h => (⟨hx, h⟩ : x ∈ (W : Set X) ∩ z₁))
          (fun h => (⟨hx, h⟩ : x ∈ (W : Set X) ∩ z₂))) F hF i
        (IH A hAW) (IH B hBW)
  · exact sheafCohomology_isZero_of_forall_stalk (fun x => hF x fun hx => hW ⟨x, hx⟩) _

/-- **Reduction to irreducible components** (Hartshorne III.2, proof of Theorem 2.7, Step 1).
Fix `n : ℕ` and a Noetherian space `X` with `dim X ≤ n`. If every irreducible closed subset
`Z ⊆ X` with `dim Z ≤ n` has `H^i(Z, G) = 0` for all abelian sheaves `G` on `Z` and all `i > n`,
then `H^i(X, F) = 0` for all abelian sheaves `F` on `X` and all `i > n`. -/
theorem sheafCohomology_isZero_of_forall_irreducible_closed [NoetherianSpace X] {n : ℕ}
    (hX : topologicalKrullDim X ≤ n)
    (hirr : ∀ Z : Set X, IsClosed Z → IsIrreducible Z → topologicalKrullDim Z ≤ n →
      ∀ (G : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) (i : ℕ), n < i →
        IsZero ((sheafCohomology (TopCat.of Z) i).obj G))
    (F : X.Sheaf AddCommGrpCat.{u}) (i : ℕ) (hi : n < i) :
    IsZero ((sheafCohomology X i).obj F) :=
  sheafCohomology_isZero_of_stalk_isZero_off hX hirr ⊤ i hi F (fun _ hx => absurd trivial hx)

end Hartshorne
