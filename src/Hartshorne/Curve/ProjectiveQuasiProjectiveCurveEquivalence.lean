/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.CurveProjectiveModel
import Hartshorne.Curve.ProjectiveRationalMapExtension

/-!
# Projective and quasi-projective curve categories are equivalent

Hartshorne, *Algebraic Geometry*, I.6, Corollary 6.12 (pp. 45--46).

The forward functor regards a nonsingular projective curve as a
quasi-projective curve and an everywhere-defined dominant morphism as a
dominant rational map.  Unique extension of rational maps makes this functor
fully faithful, while existence of nonsingular projective models makes it
essentially surjective.
-/

namespace Hartshorne

open CategoryTheory

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Regard projective nonsingular curves and their dominant morphisms as
quasi-projective curves and dominant rational maps. -/
private noncomputable def projectiveToQuasiProjectiveCurveFunctor :
    ProjectiveNonsingularCurveCat k ⥤ QuasiProjectiveCurveCat k where
  obj X :=
    { ι := X.ι
      carrier := X.carrier
      isQuasiProjective := X.isProjective.isQuasiProjVariety
      isCurve := X.isCurve }
  map f := DominantRatMap.ofHom f.1 f.2
  map_id X := by
    apply Quotient.sound
    intro x _ _
    rfl
  map_comp f g := by
    apply Quotient.sound
    intro x _ _
    rfl

private instance projectiveToQuasiProjectiveCurveFunctor_faithful :
    (projectiveToQuasiProjectiveCurveFunctor (k := k)).Faithful where
  map_injective {X Y} {f g} h := by
    obtain ⟨Φ, _, hUnique⟩ :=
      DominantRatMap.existsUnique_projectiveCurve_extension
        X Y.isProjective
        ((projectiveToQuasiProjectiveCurveFunctor (k := k)).map f)
    apply Subtype.ext
    have hf : f.1 = Φ := hUnique f.1 ⟨f.2, rfl⟩
    have hg : g.1 = Φ := hUnique g.1 ⟨g.2, ?_⟩
    · exact hf.trans hg.symm
    · change (projectiveToQuasiProjectiveCurveFunctor (k := k)).map g =
        (projectiveToQuasiProjectiveCurveFunctor (k := k)).map f
      exact h.symm

private instance projectiveToQuasiProjectiveCurveFunctor_full :
    (projectiveToQuasiProjectiveCurveFunctor (k := k)).Full where
  map_surjective {X Y} f := by
    obtain ⟨Φ, ⟨hΦ, hΦf⟩, _⟩ :=
      DominantRatMap.existsUnique_projectiveCurve_extension
        X Y.isProjective f
    exact ⟨⟨Φ, hΦ⟩, hΦf⟩

private instance projectiveToQuasiProjectiveCurveFunctor_essSurj :
    (projectiveToQuasiProjectiveCurveFunctor (k := k)).EssSurj where
  mem_essImage X := by
    classical
    obtain ⟨τ, hτ, hτne, Y, hY, hYcurve, hYnonsingular, hbirational⟩ :=
      X.isQuasiProjective.birational_nonsingular_projective X.isCurve
    let _ : Finite τ := hτ
    let _ : Nonempty τ := hτne
    let P : ProjectiveNonsingularCurveCat k :=
      { ι := τ
        carrier := Y
        isProjective := hY
        isCurve := hYcurve
        isNonsingular := hYnonsingular }
    obtain ⟨e⟩ := hbirational
    refine ⟨P, ⟨{
      hom := e.inv
      inv := e.hom
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩⟩
    · exact e.inv_hom_id
    · exact e.hom_inv_id

private instance projectiveToQuasiProjectiveCurveFunctor_isEquivalence :
    (projectiveToQuasiProjectiveCurveFunctor (k := k)).IsEquivalence where

/-- **Hartshorne I.6, Corollary 6.12, projective/quasi-projective step.**
Nonsingular projective curves with dominant morphisms are equivalent to
quasi-projective curves with dominant rational maps.  The forward functor is
the fixed inclusion above; its quasi-inverse is chosen only through full
faithfulness and essential surjectivity. -/
noncomputable def projectiveQuasiProjectiveCurveEquivalence :
    ProjectiveNonsingularCurveCat k ≌ QuasiProjectiveCurveCat k :=
  (projectiveToQuasiProjectiveCurveFunctor (k := k)).asEquivalence

end

end Hartshorne
