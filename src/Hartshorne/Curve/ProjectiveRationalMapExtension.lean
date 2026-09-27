/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.Categories
import Hartshorne.Curve.CurveToValuationSpaceIso
import Hartshorne.Curve.ProjectiveExtension

/-!
# Extending dominant rational maps from projective nonsingular curves

Hartshorne, *Algebraic Geometry*, I.6, proof of Corollary 6.12
(pp. 45--46).

A rational map is represented on an arbitrary nonempty open subset. On an
abstract nonsingular curve that open has finite complement, so Proposition 6.8
extends the representative one missing point at a time. Proposition 6.7 then
transports the result back to the original nonsingular projective curve.

## Main result

* `Hartshorne.DominantRatMap.existsUnique_projectiveCurve_extension`
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u

namespace DominantRatMap

variable {k : Type u} [Field k]
variable {X Y : Variety k}

/-- The full-domain representative attached to a dominant morphism. -/
private noncomputable def ofHomRep
    (φ : VarietyHom X Y) (hφ : DenseRange φ.toFun) :
    DominantRatMapRep X Y where
  rep := {
    U := ⊤
    nonempty_U := Set.univ_nonempty
    hom := φ.comp (X.inclHom ⊤ Set.univ_nonempty)
  }
  isDominant := by
    change DenseRange (φ.toFun ∘ (X.inclHom ⊤ Set.univ_nonempty).toFun)
    apply DenseRange.comp hφ
      (Function.Surjective.denseRange (fun x => ⟨⟨x, trivial⟩, rfl⟩))
    exact φ.continuous_toFun

/-- Regard a dominant everywhere-defined morphism as a dominant rational map.

The representative has the full source as its domain. This is the canonical
map on hom-sets used when comparing the projective-curve and rational-map
categories. -/
noncomputable def ofHom {hY : Y.IsSeparated}
    (φ : VarietyHom X Y) (hφ : DenseRange φ.toFun) :
    DominantRatMap X Y hY :=
  Quotient.mk _ (ofHomRep φ hφ)

variable [IsAlgClosed k]

/-- **Hartshorne I.6, Corollary 6.12, extension step.**

A dominant rational map from a nonsingular projective curve to a projective
variety has a unique everywhere-defined extension. The extension is itself
dominant, recorded by the witness used to recover the original quotient-level
dominant rational map. In particular, when the target is a projective curve
this produces the required morphism in `ProjectiveNonsingularCurveCat`. -/
theorem existsUnique_projectiveCurve_extension
    {τ : Type u} [Finite τ] [Nonempty τ]
    (X : ProjectiveNonsingularCurveCat k)
    {Y : Set (ProjectiveSpace k τ)} (hY : IsProjVariety Y)
    (f : DominantRatMap X.toVariety (Variety.ofProjective hY)
      (isSeparated_ofQuasiProjective hY.isQuasiProjVariety)) :
    ∃! Φ : VarietyHom X.toVariety (Variety.ofProjective hY),
      ∃ hΦ : DenseRange Φ.toFun, ofHom Φ hΦ = f := by
  classical
  let hXq : IsQuasiProjVariety.{u, u} X.carrier :=
    X.isProjective.isQuasiProjVariety
  let hXaff : X.toVariety.HasAffineOpenBasis := by
    change (Variety.ofQuasiProjective hXq).HasAffineOpenBasis
    exact Variety.hasAffineOpenBasis_ofQuasiProjective hXq
  let _ : Algebra.EssFiniteType k X.toVariety.FunctionField :=
    RationalMapFunctionField.essFiniteType_functionField hXaff
  let htrdeg : Algebra.trdeg k X.toVariety.FunctionField = 1 :=
    hXaff.isCurve_iff_trdeg_eq_one.mp X.isCurve
  let A := hXq.localRingMapAbstractCurve X.isCurve X.isNonsingular
  let e : VarietyHom X.toVariety A :=
    hXq.localRingMapAbstractCurveHom X.isCurve X.isNonsingular
  obtain ⟨g, hge, _⟩ :=
    hXq.localRingMapAbstractCurveHom_isIso X.isCurve X.isNonsingular
  let U := hXq.localRingMapRangeOpen X.isCurve X.isNonsingular
  let hU := hXq.localRingMapRangeOpen_nonempty X.isCurve X.isNonsingular
  refine Quotient.inductionOn f ?_
  intro r
  let D : Opens A.carrier :=
    Opens.comap ⟨g.toFun, g.continuous_toFun⟩ r.rep.U
  have hD : (D : Set A.carrier).Nonempty := by
    obtain ⟨x, hx⟩ := r.rep.nonempty_U
    refine ⟨e x, ?_⟩
    change g (e x) ∈ r.rep.U
    have hxge := congrArg (fun q : VarietyHom X.toVariety X.toVariety => q x) hge
    change g (e x) = x at hxge
    exact hxge.symm ▸ hx
  let gD0 : VarietyHom (A.restrict D hD) X.toVariety :=
    g.comp (A.inclHom D hD)
  let gD : VarietyHom (A.restrict D hD)
      (X.toVariety.restrict r.rep.U r.rep.nonempty_U) :=
    VarietyHom.liftToRestrict gD0 r.rep.U r.rep.nonempty_U (fun x => x.2)
  let φA : VarietyHom (A.restrict D hD) (Variety.ofProjective hY) :=
    r.rep.hom.comp gD
  obtain ⟨ΦA, hΦA, _⟩ :=
    ValuationSpace.existsUnique_projective_extension_of_open
      htrdeg U hU D hD hY φA
  let Φ : VarietyHom X.toVariety (Variety.ofProjective hY) := ΦA.comp e
  have hΦagree (x : X.toVariety.carrier) (hx : x ∈ r.rep.U) :
      Φ x = r.rep.hom ⟨x, hx⟩ := by
    have hxge := congrArg (fun q : VarietyHom X.toVariety X.toVariety => q x) hge
    have hxD : e x ∈ D := by
      change g (e x) ∈ r.rep.U
      change g (e x) = x at hxge
      exact hxge.symm ▸ hx
    let xD : (A.restrict D hD).carrier := ⟨e x, hxD⟩
    have hxext := congrArg
      (fun q : VarietyHom (A.restrict D hD) (Variety.ofProjective hY) => q xD) hΦA
    change ΦA ((A.inclHom D hD) xD) = φA xD at hxext
    calc
      Φ x = ΦA (e x) := rfl
      _ = ΦA ((A.inclHom D hD) xD) := by
        apply congrArg ΦA
        rfl
      _ = φA xD := hxext
      _ = r.rep.hom ⟨x, hx⟩ := by
        apply congrArg r.rep.hom
        apply Subtype.ext
        exact hxge
  have hΦdense : DenseRange Φ.toFun := by
    apply Dense.mono _ r.isDominant
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1, hΦagree x.1 x.2⟩
  have hΦquot : ofHom Φ hΦdense =
      (⟦r⟧ : DominantRatMap X.toVariety (Variety.ofProjective hY)
        (isSeparated_ofQuasiProjective hY.isQuasiProjVariety)) := by
    apply Quotient.sound
    intro x _ hx
    change Φ x = r.rep.hom ⟨x, hx⟩
    exact hΦagree x hx
  refine ⟨Φ, ⟨hΦdense, hΦquot⟩, ?_⟩
  intro Ψ hΨ
  obtain ⟨hΨdense, hΨquot⟩ := hΨ
  have hrel : DominantRatMapRep.Rel (ofHomRep Ψ hΨdense) r := by
    exact Quotient.exact hΨquot
  apply isSeparated_ofQuasiProjective hY.isQuasiProjVariety
    X.toVariety Ψ Φ (r.rep.U : Set _) r.rep.U.isOpen r.rep.nonempty_U
  intro x hx
  have hΨagree := hrel x trivial hx
  change Ψ x = r.rep.hom ⟨x, hx⟩ at hΨagree
  exact hΨagree.trans (hΦagree x hx).symm

end DominantRatMap

end

end Hartshorne
