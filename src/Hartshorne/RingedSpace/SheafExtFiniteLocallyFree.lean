/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Hartshorne.RingedSpace.SheafExt

/-!
# `ℰxt` out of a finite locally free sheaf

Let `(X, 𝒪_X)` be a ringed space and `L` a locally free `𝒪_X`-module of finite rank. Then the
functor `ℋom(L, -)` is exact and hence `ℰxtⁱ(L, G) = 0` for every `G` and every `i > 0`
(`Hartshorne.Ringed.isZero_sheafExt_of_isFiniteLocallyFree`). This is the input used in the proof
of Hartshorne III.6, Proposition 6.5 (p. 234).

Proof. `ℋom(L, -)` is left exact (it preserves limits). It also preserves epimorphisms: by the
canonical isomorphism `L^∨ ⊗ G ≅ ℋom(L, G)`, natural in `G`, it is isomorphic to tensoring with
`L^∨`, which is a left adjoint by the tensor–Hom adjunction. A functor between abelian categories
preserving kernels and epimorphisms preserves homology, so applying `ℋom(L, -)` to an injective
resolution of `G` gives a complex that is exact in positive degrees.
-/

universe u

open CategoryTheory Limits

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

/-- For a finite locally free `L`, the functor `ℋom(L, -)` sends epimorphisms to epimorphisms. -/
lemma moduleSheafHomFunctor_map_epi {L : 𝓜} (hL : IsFiniteLocallyFree L) {A B : 𝓜} (g : A ⟶ B)
    [Epi g] : Epi ((moduleSheafHomFunctor L).map g) := by
  have hB : IsIso (moduleSheafDualTensorMap L B) := moduleSheafDualTensorMap_isIso L B hL
  have ht := modulesTensorMap_epi (moduleSheafDual L) g
  have hb : Epi (moduleSheafDualTensorMap L B) := @IsIso.epi_of_iso _ _ _ _ _ hB
  have hc : Epi (modulesTensorMap (𝟙 (moduleSheafDual L)) g ≫ moduleSheafDualTensorMap L B) :=
    @epi_comp _ _ _ _ _ _ ht _ hb
  rw [moduleSheafDualTensorMap_naturality_right (E := L) g] at hc
  rw [moduleSheafHomFunctor_map]
  exact @epi_of_epi _ _ _ _ _ (moduleSheafDualTensorMap L A) _ hc

/-- For a finite locally free `L`, the functor `ℋom(L, -)` preserves epimorphisms. -/
theorem moduleSheafHomFunctor_preservesEpimorphisms {L : 𝓜} (hL : IsFiniteLocallyFree L) :
    (moduleSheafHomFunctor L).PreservesEpimorphisms where
  preserves g _ := moduleSheafHomFunctor_map_epi hL g

/- As in `Hartshorne.RingedSpace.SheafExt`, use the preadditive structure coming from the abelian
structure, which is the one Mathlib's derived-functor API is stated with. -/
attribute [local instance 2000] Abelian.toPreadditive

/-- For a finite locally free `L`, the functor `ℋom(L, -)` is exact: it preserves homology. -/
theorem moduleSheafHomFunctor_preservesHomology {L : 𝓜} (hL : IsFiniteLocallyFree L) :
    (moduleSheafHomFunctor L).PreservesHomology := by
  have := moduleSheafHomFunctor_preservesEpimorphisms hL
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- **`ℰxtⁱ(L, G) = 0` for `i > 0` and `L` finite locally free.** Since `ℋom(L, -)` is exact, it
carries an injective resolution of `G` to a complex which is exact in positive degrees. -/
theorem isZero_sheafExt_of_isFiniteLocallyFree {L : 𝓜} (hL : IsFiniteLocallyFree L) (G : 𝓜)
    {i : ℕ} (hi : 0 < i) : IsZero ((sheafExt L i).obj G) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have := moduleSheafHomFunctor_preservesHomology hL
  let I := injectiveResolution G
  refine IsZero.of_iso ?_ (sheafExtIsoHomology L I (n + 1))
  have h : (((moduleSheafHomFunctor L).mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) :=
    (I.cocomplex_exactAt_succ n).map (moduleSheafHomFunctor L)
  exact h.isZero_homology

end Ringed

end Hartshorne
