/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeSegre
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Calculus of projective morphisms

Hartshorne, *Algebraic Geometry*, II.4, Exercise 4.8(e) and the composition assertion of
Exercise 4.9.

* Relative projective space commutes with base change: for `g : Y' ⟶ Y` the square formed by
  `ℙⁿ_{Y'} ⟶ ℙⁿ_Y` and the two structure projections is a pullback square
  (`projectiveSpaceOverSchemeMap_isPullback`).
* Projective morphisms compose (`Projective.comp`): given `X ↪ ℙʳ_Y` over `Y` and `Y ↪ ℙˢ_Z`
  over `Z`, the space `ℙʳ_Y` is the base change of `ℙʳ_Z ×_Z ℙˢ_Z ⟶ ℙˢ_Z` along `Y ↪ ℙˢ_Z`, so
  `ℙʳ_Y ⟶ ℙʳ_Z ×_Z ℙˢ_Z` is a closed immersion; the relative Segre embedding then lands in
  `ℙ^{rs+r+s}_Z`.
* Cancellation (`Projective.of_comp`): if `X ⟶ Y ⟶ Z` has projective composite, witnessed by
  `i : X ↪ ℙⁿ_Z`, and `Y ⟶ Z` is separated, then the induced `X ⟶ ℙⁿ_Y` composed with the
  separated map `ℙⁿ_Y ⟶ ℙⁿ_Z` (a base change of `Y ⟶ Z`) is `i`, hence is a closed immersion.

The packaged statement is `projectiveMorphismCalculus`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- Relative projective space commutes with base change: for `g : Y' ⟶ Y`, the square with
`ℙⁿ_{Y'} ⟶ ℙⁿ_Y` on top, the structure projections on the sides and `g` at the bottom is a
pullback square. -/
theorem projectiveSpaceOverSchemeMap_isPullback (n : ℕ) {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsPullback (projectiveSpaceOverSchemeMap n g) (projectiveSpaceOverSchemeProjection n Y')
      (projectiveSpaceOverSchemeProjection n Y) g := by
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _)
    (h₂₂ := schemeToSpecZ Y) (v₁₃ := projectiveSpaceOverIntegersMap n) ?_
    (projectiveSpaceOverSchemeMap_projection n g) (IsPullback.of_hasPullback _ _)
  rw [projectiveSpaceOverSchemeMap_fst]
  convert IsPullback.of_hasPullback (projectiveSpaceOverIntegersMap n) (schemeToSpecZ Y') using 1
  exact specULiftZIsTerminal.{u}.hom_ext _ _

namespace Projective

/-- **Projective morphisms compose** (Hartshorne II, Exercise 4.9). -/
theorem comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Projective f)
    (hg : Projective g) : Projective (f ≫ g) := by
  obtain ⟨r, i, hi, rfl⟩ := hf
  obtain ⟨s, j, hj, rfl⟩ := hg
  let πr := projectiveSpaceOverSchemeProjection r Z
  let πs := projectiveSpaceOverSchemeProjection s Z
  let πY := projectiveSpaceOverSchemeProjection r Y
  let k : projectiveSpaceOverScheme r Y ⟶ relativeSegreSource r s Z :=
    pullback.lift (projectiveSpaceOverSchemeMap r (j ≫ πs)) (πY ≫ j)
      (by rw [projectiveSpaceOverSchemeMap_projection, Category.assoc])
  have hk_fst : k ≫ pullback.fst πr πs = projectiveSpaceOverSchemeMap r (j ≫ πs) :=
    pullback.lift_fst _ _ _
  have hk_snd : k ≫ pullback.snd πr πs = πY ≫ j := pullback.lift_snd _ _ _
  have hsq : IsPullback k πY (pullback.snd πr πs) j := by
    refine IsPullback.of_right (h₁₂ := pullback.fst πr πs) (h₂₂ := πs) (v₁₃ := πr) ?_
      hk_snd (IsPullback.of_hasPullback πr πs)
    rw [hk_fst]
    exact projectiveSpaceOverSchemeMap_isPullback r (j ≫ πs)
  have : IsClosedImmersion k :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hj
  refine mk (r * s + r + s) (i ≫ k ≫ relativeSegre r s Z) ?_
  simp only [Category.assoc, relativeSegre_projection, relativeSegreSourceProjection]
  rw [reassoc_of% hk_fst, projectiveSpaceOverSchemeMap_projection]

/-- **Cancellation for projective morphisms** (Hartshorne II, Exercise 4.8(e)): if `f ≫ g` is
projective and `g` is separated, then `f` is projective. -/
theorem of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated g]
    (hfg : Projective (f ≫ g)) : Projective f := by
  obtain ⟨n, i, hi, hfac⟩ := hfg
  let j : X ⟶ projectiveSpaceOverScheme n Y :=
    pullback.lift (i ≫ pullback.fst _ _) f (specULiftZIsTerminal.{u}.hom_ext _ _)
  have hj : j ≫ projectiveSpaceOverSchemeMap n g = i := by
    apply pullback.hom_ext
    · rw [Category.assoc, projectiveSpaceOverSchemeMap_fst]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, projectiveSpaceOverSchemeMap_projection, hfac]
      exact pullback.lift_snd_assoc _ _ _ _
  have : IsSeparated (projectiveSpaceOverSchemeMap n g) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (projectiveSpaceOverSchemeMap_isPullback n g).flip inferInstance
  have : IsClosedImmersion (j ≫ projectiveSpaceOverSchemeMap n g) := by
    rw [hj]
    exact hi
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j (projectiveSpaceOverSchemeMap n g)
  exact mk n j (pullback.lift_snd _ _ _)

end Projective

/-- **Calculus of projective morphisms** (Hartshorne II, Exercises 4.8(e) and 4.9).
Projective morphisms compose, and if `X ⟶ Y ⟶ Z` has projective composite and `Y ⟶ Z` is
separated, then `X ⟶ Y` is projective. -/
theorem projectiveMorphismCalculus :
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        Projective f → Projective g → Projective (f ≫ g)) ∧
      ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        Projective (f ≫ g) → IsSeparated g → Projective f :=
  ⟨fun _ _ hf hg => Projective.comp hf hg,
    fun f g hfg hg => have := hg; Projective.of_comp f g hfg⟩

end Hartshorne
