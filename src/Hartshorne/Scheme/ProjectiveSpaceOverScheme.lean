/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BaseExtension
import Hartshorne.Scheme.ProjectiveSpace
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Projective space and projective morphisms over a scheme

Hartshorne, *Algebraic Geometry*, II.4, p. 103.

Relative projective `n`-space over `Y` is the base extension of projective
`n`-space over the integers along the unique morphism `Y ⟶ Spec ℤ`.

A morphism is projective when it factors through a closed immersion into some
relative projective space. This file also supplies the canonical constructors
for closed immersions and projective-space projections and proves invariance
under isomorphism of arrows.
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

section ProjectiveMorphism

attribute [local instance] MvPolynomial.gradedAlgebra

private noncomputable def pzeroEvalOne
    (R : Type*) [CommRing R] : MvPolynomial (Fin 1) R →+* R :=
  (Polynomial.evalRingHom 1).comp (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom

@[simp]
private theorem pzeroEvalOne_X
    (R : Type*) [CommRing R] (i : Fin 1) :
    pzeroEvalOne R (MvPolynomial.X i) = 1 := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [pzeroEvalOne]

private theorem eq_zero_of_isHomogeneous_pzeroEvalOne_eq_zero
    {R : Type*} [CommRing R] {n : ℕ} {p : MvPolynomial (Fin 1) R}
    (hp : p.IsHomogeneous n) (h : pzeroEvalOne R p = 0) : p = 0 := by
  let P : Polynomial R := MvPolynomial.uniqueAlgEquiv R (Fin 1) p
  have hP : P = Polynomial.monomial n (P.coeff n) := by
    ext m
    by_cases hmn : m = n
    · subst m
      simp
    · have hcoeff : P.coeff m = 0 := by
        by_contra hm
        have hm' : MvPolynomial.coeff (Finsupp.single (0 : Fin 1) m) p ≠ 0 := by
          change ((MvPolynomial.uniqueAlgEquiv R (Fin 1)) p).coeff m ≠ 0 at hm
          rwa [MvPolynomial.coeff_uniqueAlgEquiv] at hm
        have hdeg := hp hm'
        have : m = n := by
          simpa [Finsupp.weight_apply] using hdeg
        exact hmn this
      simp [Polynomial.coeff_monomial, Ne.symm hmn, hcoeff]
  change Polynomial.eval 1 P = 0 at h
  rw [hP] at h
  simp only [Polynomial.eval_monomial, one_pow, mul_one] at h
  apply (MvPolynomial.uniqueAlgEquiv R (Fin 1)).injective
  change P = 0
  rw [hP, h]
  simp

private theorem pzero_X_mem_homogeneousSubmodule
    (R : Type*) [CommRing R] :
    (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin 1) R 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X R 0)

private noncomputable def pzeroAwayEval
    (R : Type*) [CommRing R] :
    Localization.Away (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R) →+* R :=
  IsLocalization.lift
    (M := Submonoid.powers (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R))
    (g := pzeroEvalOne R) (by
      rintro ⟨x, n, rfl⟩
      simp)

@[simp]
private theorem pzeroAwayEval_mk
    (R : Type*) [CommRing R] (a : MvPolynomial (Fin 1) R) (n : ℕ)
    (h : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R) ^ n ∈
      Submonoid.powers (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R)) :
    pzeroAwayEval R (Localization.mk a ⟨_, h⟩) = pzeroEvalOne R a := by
  rw [Localization.mk_eq_mk', pzeroAwayEval, IsLocalization.lift_mk'_spec]
  simp

private noncomputable def pzeroAwayToBase
    (R : Type*) [CommRing R] :
    HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin 1) R) (MvPolynomial.X 0) →+* R where
  toFun z := pzeroAwayEval R z.val
  map_one' := by simp [HomogeneousLocalization.val_one]
  map_mul' a b := by simp [HomogeneousLocalization.val_mul]
  map_zero' := by simp [HomogeneousLocalization.val_zero]
  map_add' a b := by simp [HomogeneousLocalization.val_add]

@[simp]
private theorem pzeroAwayToBase_mk
    (R : Type*) [CommRing R] (n : ℕ) (a : MvPolynomial (Fin 1) R)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 1) R (n • 1)) :
    pzeroAwayToBase R
      (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin 1) R)
        (pzero_X_mem_homogeneousSubmodule R) n a ha) = pzeroEvalOne R a := by
  show pzeroAwayEval R _ = _
  rw [HomogeneousLocalization.Away.val_mk, pzeroAwayEval_mk]

private noncomputable def pzeroAwayEquiv
    (R : Type*) [CommRing R] :
    HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin 1) R) (MvPolynomial.X 0) ≃+* R :=
  RingEquiv.ofBijective (pzeroAwayToBase R) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨n, a, ha, rfl⟩ :=
        HomogeneousLocalization.Away.mk_surjective _
          (pzero_X_mem_homogeneousSubmodule R) z
      rw [pzeroAwayToBase_mk] at hz
      have hzero : a = 0 := eq_zero_of_isHomogeneous_pzeroEvalOne_eq_zero
        ((MvPolynomial.mem_homogeneousSubmodule _ _).1 (by simpa using ha)) hz
      subst hzero
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
        Localization.mk_zero]
    · intro r
      refine ⟨HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin 1) R)
        (pzero_X_mem_homogeneousSubmodule R) 0 (MvPolynomial.C r) ?_, ?_⟩
      · simp
      · simp [pzeroAwayToBase_mk, pzeroEvalOne])

private theorem irrelevant_le_span_X
    (R : Type*) [CommRing R] (n : ℕ) :
    (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toIdeal ≤
      Ideal.span (Set.range
        (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd p hp
  change p ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R
  rw [← pow_one (MvPolynomial.idealOfVars (Fin (n + 1)) R),
    MvPolynomial.mem_pow_idealOfVars_iff]
  intro m hm
  have hhom : p.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d p).1 hp
  have hdeg : (Finsupp.weight 1) m = d := hhom (MvPolynomial.mem_support_iff.1 hm)
  have hdeg' : Finsupp.degree m = d := by
    rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
    exact hdeg
  rw [hdeg']
  exact hd

private noncomputable def projectiveSpaceZeroAbsoluteIso :
    projectiveSpaceScheme (ULift.{u} ℤ) 0 ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) := by
  let R := ULift.{u} ℤ
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 1) R
  have hcover : ⨆ i : Fin 1, Proj.basicOpen 𝒜 (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top 𝒜 MvPolynomial.X (irrelevant_le_span_X R 0)
  have htop : Proj.basicOpen 𝒜 (MvPolynomial.X (0 : Fin 1)) = ⊤ := by
    simpa only [Unique.eq_default, iSup_const] using hcover
  let eOpen : Proj 𝒜 ≅ (Proj.basicOpen 𝒜 (MvPolynomial.X (0 : Fin 1))).toScheme :=
    (Scheme.topIso _).symm ≪≫ (Scheme.isoOfEq _ htop).symm
  let eChart := Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X (0 : Fin 1))
    (pzero_X_mem_homogeneousSubmodule R) Nat.zero_lt_one
  let eRing := (pzeroAwayEquiv R).toCommRingCatIso
  change Proj 𝒜 ≅ Spec (CommRingCat.of R)
  exact eOpen ≪≫ eChart ≪≫ (Scheme.Spec.mapIso eRing.op).symm

private theorem projectiveSpaceZeroAbsoluteIso_hom :
    projectiveSpaceZeroAbsoluteIso.{u}.hom = projectiveSpaceOverIntegersMap.{u} 0 :=
  specULiftZIsTerminal.{u}.hom_ext _ _

private instance projectiveSpaceOverIntegersMap_zero_isIso :
    IsIso (projectiveSpaceOverIntegersMap.{u} 0) := by
  rw [← projectiveSpaceZeroAbsoluteIso_hom]
  infer_instance

private instance projectiveSpaceOverSchemeProjection_zero_isIso (Y : Scheme.{u}) :
    IsIso (projectiveSpaceOverSchemeProjection 0 Y) :=
  pullback_snd_iso_of_left_iso (projectiveSpaceOverIntegersMap 0) (schemeToSpecZ Y)

/-- A morphism is projective when it factors through a closed immersion into
relative projective space. -/
def Projective : MorphismProperty Scheme.{u} :=
  fun X Y f => ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOverScheme n Y),
    IsClosedImmersion i ∧ i ≫ projectiveSpaceOverSchemeProjection n Y = f

namespace Projective

/-- Construct a projective morphism from an explicit relative-projective-space
factorization. -/
theorem mk {X Y : Scheme.{u}} {f : X ⟶ Y} (n : ℕ)
    (i : X ⟶ projectiveSpaceOverScheme n Y) [IsClosedImmersion i]
    (h : i ≫ projectiveSpaceOverSchemeProjection n Y = f) : Projective f :=
  ⟨n, i, inferInstance, h⟩

/-- The projection from relative projective space is projective. -/
theorem projection (n : ℕ) (Y : Scheme.{u}) :
    Projective (projectiveSpaceOverSchemeProjection n Y) :=
  mk n (𝟙 _) (Category.id_comp _)

/-- Every closed immersion is projective. -/
theorem of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Projective f := by
  let e := asIso (projectiveSpaceOverSchemeProjection 0 Y)
  refine mk 0 (f ≫ e.inv) ?_
  simp [e]

private noncomputable def projectiveSpaceMapIso
    (n : ℕ) {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    projectiveSpaceOverScheme n Y ≅ projectiveSpaceOverScheme n Z :=
  asIso <| pullback.map
    (projectiveSpaceOverIntegersMap n) (schemeToSpecZ Y)
    (projectiveSpaceOverIntegersMap n) (schemeToSpecZ Z)
    (𝟙 _) e.hom (𝟙 _) (by simp) (specULiftZIsTerminal.{u}.hom_ext _ _)

@[reassoc]
private theorem projectiveSpaceMapIso_hom_projection
    (n : ℕ) {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (projectiveSpaceMapIso n e).hom ≫ projectiveSpaceOverSchemeProjection n Z =
      projectiveSpaceOverSchemeProjection n Y ≫ e.hom := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  rw [pullback.lift_snd]

instance : MorphismProperty.RespectsIso
    (Projective : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    obtain ⟨n, i, hi, hfac⟩ := hf
    let _ : IsClosedImmersion (e.hom ≫ i) := inferInstance
    exact mk n (e.hom ≫ i) (by rw [Category.assoc, hfac])
  · intro X Y Z e f hf
    obtain ⟨n, i, hi, hfac⟩ := hf
    let E := projectiveSpaceMapIso n e
    let _ : IsClosedImmersion (i ≫ E.hom) := inferInstance
    apply mk n (i ≫ E.hom)
    rw [Category.assoc, projectiveSpaceMapIso_hom_projection, ← Category.assoc, hfac]

end Projective

end ProjectiveMorphism

end Hartshorne
