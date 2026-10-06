/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BaseExtension
import Hartshorne.Scheme.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Limits

/-!
# Projective space over a scheme

Hartshorne, *Algebraic Geometry*, II.4, p. 103.

Relative projective `n`-space over `Y` is the base extension of projective
`n`-space over the integers along the unique morphism `Y ⟶ Spec ℤ`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- The structure morphism from scheme projective space over `ℤ` to
`Spec ℤ`. -/
def projectiveSpaceOverIntegersMap (n : ℕ) :
    projectiveSpaceScheme (ULift.{u} ℤ) n ⟶
      Spec (CommRingCat.of (ULift.{u} ℤ)) :=
  specULiftZIsTerminal.{u}.from _

/-- The unique structure morphism from a scheme to the universe-lifted
`Spec ℤ`. -/
def schemeToSpecZ (Y : Scheme.{u}) :
    Y ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
  specULiftZIsTerminal.{u}.from Y

/-- Relative projective `n`-space over `Y`. The homogeneous coordinates are
indexed by `Fin (n + 1)`. -/
abbrev projectiveSpaceOverScheme (n : ℕ) (Y : Scheme.{u}) : Scheme.{u} :=
  pullback (projectiveSpaceOverIntegersMap n) (schemeToSpecZ Y)

/-- The structure morphism `ℙⁿ_Y ⟶ Y`. -/
abbrev projectiveSpaceOverSchemeProjection (n : ℕ) (Y : Scheme.{u}) :
    projectiveSpaceOverScheme n Y ⟶ Y :=
  pullback.snd (projectiveSpaceOverIntegersMap n) (schemeToSpecZ Y)

/-- Projective space commutes canonically with base change. -/
def projectiveSpaceOverSchemeBaseChangeIso
    (n : ℕ) {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    pullback (projectiveSpaceOverSchemeProjection n Y) g ≅
      projectiveSpaceOverScheme n Y' := by
  let p := projectiveSpaceOverIntegersMap n
  let q := schemeToSpecZ Y
  let q' := schemeToSpecZ Y'
  let π := projectiveSpaceOverSchemeProjection n Y
  let toOld : pullback p q' ⟶ pullback p q :=
    pullback.lift (pullback.fst p q') (pullback.snd p q' ≫ g)
      (specULiftZIsTerminal.{u}.hom_ext _ _)
  have toOld_fst : toOld ≫ pullback.fst p q = pullback.fst p q' := by
    dsimp [toOld]
    exact pullback.lift_fst _ _ _
  have toOld_snd : toOld ≫ pullback.snd p q = pullback.snd p q' ≫ g := by
    dsimp [toOld]
    exact pullback.lift_snd _ _ _
  let forward : pullback π g ⟶ pullback p q' :=
    pullback.lift
      (pullback.fst π g ≫ pullback.fst p q)
      (pullback.snd π g)
      (specULiftZIsTerminal.{u}.hom_ext _ _)
  have forward_fst : forward ≫ pullback.fst p q' =
      pullback.fst π g ≫ pullback.fst p q := by
    dsimp [forward]
    exact pullback.lift_fst _ _ _
  have forward_snd : forward ≫ pullback.snd p q' = pullback.snd π g := by
    dsimp [forward]
    exact pullback.lift_snd _ _ _
  let backward : pullback p q' ⟶ pullback π g :=
    pullback.lift toOld (pullback.snd p q') toOld_snd
  have backward_fst : backward ≫ pullback.fst π g = toOld := by
    dsimp [backward]
    exact pullback.lift_fst _ _ _
  have backward_snd : backward ≫ pullback.snd π g = pullback.snd p q' := by
    dsimp [backward]
    exact pullback.lift_snd _ _ _
  refine
    { hom := forward
      inv := backward
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change forward ≫ backward = 𝟙 (pullback π g)
    apply pullback.hom_ext
    · rw [Category.assoc, backward_fst, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, toOld_fst, forward_fst]
      · rw [Category.assoc, toOld_snd, ← Category.assoc, forward_snd]
        change pullback.snd π g ≫ g = pullback.fst π g ≫ π
        exact pullback.condition.symm
    · rw [Category.assoc, backward_snd, forward_snd, Category.id_comp]
  · change backward ≫ forward = 𝟙 (pullback p q')
    apply pullback.hom_ext
    · rw [Category.assoc, forward_fst, ← Category.assoc, backward_fst,
        toOld_fst, Category.id_comp]
    · rw [Category.assoc, forward_snd, backward_snd, Category.id_comp]

/-- Compatibility of the base-change isomorphism with the projection to the
absolute projective-space factor. -/
@[reassoc]
theorem projectiveSpaceOverSchemeBaseChangeIso_hom_fst
    (n : ℕ) {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    (projectiveSpaceOverSchemeBaseChangeIso n g).hom ≫
        pullback.fst (projectiveSpaceOverIntegersMap n) (schemeToSpecZ Y') =
      pullback.fst (projectiveSpaceOverSchemeProjection n Y) g ≫
        pullback.fst (projectiveSpaceOverIntegersMap n) (schemeToSpecZ Y) := by
  change (pullback.lift _ _ _) ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- Compatibility of the base-change isomorphism with the structure
projection to the new base. -/
@[reassoc]
theorem projectiveSpaceOverSchemeBaseChangeIso_hom_projection
    (n : ℕ) {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    (projectiveSpaceOverSchemeBaseChangeIso n g).hom ≫
        projectiveSpaceOverSchemeProjection n Y' =
      pullback.snd (projectiveSpaceOverSchemeProjection n Y) g := by
  change (pullback.lift _ _ _) ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

end Hartshorne
