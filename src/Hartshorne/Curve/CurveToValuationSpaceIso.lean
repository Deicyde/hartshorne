/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.AbstractNonsingularCurve
import Hartshorne.Curve.LocalRingMapOpen
import Hartshorne.Morphism.GlobalLocalIntersection

/-!
# Nonsingular curves as open subcurves of their valuation spaces

Hartshorne, *Algebraic Geometry*, I.6, Proposition 6.7 (pp. 42--43).

The point-to-local-ring homeomorphism from a nonsingular quasi-projective
curve to its open image in the valuation space is an isomorphism of varieties.
The extra content beyond the homeomorphism is that residue evaluation of a
rational function in the local ring agrees with evaluation of its germ at the
corresponding point.
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u

variable {k : Type u} [Field k]

namespace Variety

/-- Evaluation at a point, regarded as a morphism of `k`-algebras. -/
private def evalAtPointAlgHom {X : Variety k} (P : X.carrier) :
    X.LocalRingAt P →ₐ[k] k where
  __ := X.evalAtPoint
  commutes' _ := rfl

end Variety

/-- Two `k`-algebra maps from a local `k`-algebra to `k` agree.  Both are
surjective, so their kernels are the unique maximal ideal. -/
private theorem algHom_to_baseField_unique
    {R : Type u} [CommRing R] [Algebra k R] [IsLocalRing R]
    (f g : R →ₐ[k] k) : f = g := by
  have hf : Function.Surjective f := fun c ↦
    ⟨algebraMap k R c, f.commutes c⟩
  have hg : Function.Surjective g := fun c ↦
    ⟨algebraMap k R c, g.commutes c⟩
  have hker : RingHom.ker f.toRingHom = RingHom.ker g.toRingHom :=
    (IsLocalRing.ker_eq_maximalIdeal f.toRingHom hf).trans
      (IsLocalRing.ker_eq_maximalIdeal g.toRingHom hg).symm
  ext x
  have hx : x - algebraMap k R (g x) ∈ RingHom.ker g.toRingHom := by
    rw [RingHom.mem_ker]
    simp
  rw [← hker, RingHom.mem_ker] at hx
  exact sub_eq_zero.mp (by simpa using hx)

variable [IsAlgClosed k] {X : Variety k}

/-- The canonical copy of the local ring inside the valuation subring attached
to a nonsingular curve point. -/
private noncomputable def localRingAlgEquivFunctionFieldDVRAt
    (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (hns : X.Nonsingular) (P : X.carrier) :
    X.LocalRingAt P ≃ₐ[k]
      (hX.functionFieldDVRAt hcurve hns P).toValuationSubring := by
  let f : X.LocalRingAt P →ₐ[k]
      (hX.functionFieldDVRAt hcurve hns P).toValuationSubring := {
    toFun z := ⟨X.localToFunctionFieldAlgHom P z, by
      have hm : X.localToFunctionFieldAlgHom P z ∈
          (hX.valuationSubringAt hcurve P (hns P)).toSubring := by
        rw [hX.valuationSubringAt_toSubring hcurve P (hns P)]
        exact ⟨z, rfl⟩
      change X.localToFunctionFieldAlgHom P z ∈
        hX.valuationSubringAt hcurve P (hns P)
      exact hm⟩
    map_one' := Subtype.ext (map_one (X.localToFunctionFieldAlgHom P))
    map_mul' a b := Subtype.ext (map_mul (X.localToFunctionFieldAlgHom P) a b)
    map_zero' := Subtype.ext (map_zero (X.localToFunctionFieldAlgHom P))
    map_add' a b := Subtype.ext (map_add (X.localToFunctionFieldAlgHom P) a b)
    commutes' c := Subtype.ext ((X.localToFunctionFieldAlgHom P).commutes c)
  }
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    apply X.localToFunctionFieldAlgHom_injective P
    exact congrArg Subtype.val hab
  · intro z
    have hz : z.1 ∈ (X.localRingRange P).toSubring := by
      rw [← hX.valuationSubringAt_toSubring hcurve P (hns P)]
      exact z.2
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, Subtype.ext ?_⟩
    exact ha

@[simp]
private theorem localRingAlgEquivFunctionFieldDVRAt_coe
    (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (hns : X.Nonsingular) (P : X.carrier) (a : X.LocalRingAt P) :
    (((localRingAlgEquivFunctionFieldDVRAt hX hcurve hns P) a :
        (hX.functionFieldDVRAt hcurve hns P).toValuationSubring) :
      X.FunctionField) = X.localToFunctionFieldAlgHom P a :=
  by
    unfold localRingAlgEquivFunctionFieldDVRAt
    rfl

/-- Residue evaluation at the DVR attached to `P` is evaluation of the
corresponding germ at `P`. -/
private theorem residueAt_localRingAlgEquivFunctionFieldDVRAt
    [Algebra.EssFiniteType k X.FunctionField]
    (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (hns : X.Nonsingular) (htrdeg : Algebra.trdeg k X.FunctionField = 1)
    (P : X.carrier) (a : X.LocalRingAt P) :
    FunctionFieldDVR.residueAt htrdeg
        (hX.functionFieldDVRAt hcurve hns P)
        (localRingAlgEquivFunctionFieldDVRAt hX hcurve hns P a) =
      X.evalAtPoint a := by
  let e := localRingAlgEquivFunctionFieldDVRAt hX hcurve hns P
  let f : X.LocalRingAt P →ₐ[k] k :=
    (FunctionFieldDVR.residueAt htrdeg
      (hX.functionFieldDVRAt hcurve hns P)).comp e.toAlgHom
  have hfg : f = X.evalAtPointAlgHom P :=
    algHom_to_baseField_unique f (X.evalAtPointAlgHom P)
  exact DFunLike.congr_fun hfg a

/-- Residue evaluation is insensitive to replacing a packaged function-field
DVR by an equal one. -/
private theorem residueAt_eq_of_dvr_eq
    {K : Type u} [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    {R S : FunctionFieldDVR k K} (hRS : R = S) (q : K)
    (hR : q ∈ R.toValuationSubring) (hS : q ∈ S.toValuationSubring) :
    FunctionFieldDVR.residueAt htrdeg R ⟨q, hR⟩ =
      FunctionFieldDVR.residueAt htrdeg S ⟨q, hS⟩ := by
  subst S
  rfl

variable { σ : Type u} [Finite σ] [DecidableEq σ] [Nonempty σ]
  {Y : Set (ProjectiveSpace k σ)}

/-- The open image of the point-to-local-ring map. -/
noncomputable def IsQuasiProjVariety.localRingMapRangeOpen
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    Opens (ValuationSpace k (Variety.ofQuasiProjective hY).FunctionField) :=
  ⟨Set.range
      ((Variety.hasAffineOpenBasis_ofQuasiProjective hY).localRingMap hcurve hns),
    hY.isOpen_range_localRingMap hcurve hns⟩

/-- The image of the local-ring map is nonempty. -/
theorem IsQuasiProjVariety.localRingMapRangeOpen_nonempty
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    ((hY.localRingMapRangeOpen hcurve hns :
      Opens (ValuationSpace k
        (Variety.ofQuasiProjective hY).FunctionField)) :
      Set (ValuationSpace k
        (Variety.ofQuasiProjective hY).FunctionField)).Nonempty := by
  let X := Variety.ofQuasiProjective hY
  let hX := Variety.hasAffineOpenBasis_ofQuasiProjective hY
  exact ⟨hX.localRingMap hcurve hns X.nonempty.some,
    ⟨X.nonempty.some, rfl⟩⟩

/-- The abstract nonsingular curve carried by the open image of the local-ring
map. -/
noncomputable def IsQuasiProjVariety.localRingMapAbstractCurve
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) : Variety k := by
  let X := Variety.ofQuasiProjective hY
  let hX := Variety.hasAffineOpenBasis_ofQuasiProjective hY
  letI : Algebra.EssFiniteType k X.FunctionField :=
    RationalMapFunctionField.essFiniteType_functionField hX
  exact ValuationSpace.abstractNonsingularCurve
    (hX.isCurve_iff_trdeg_eq_one.mp hcurve)
    (hY.localRingMapRangeOpen hcurve hns)
    (hY.localRingMapRangeOpen_nonempty hcurve hns)

/-- The point-to-local-ring homeomorphism, with its codomain expressed as the
carrier of the associated abstract nonsingular curve. -/
noncomputable def IsQuasiProjVariety.localRingMapAbstractCurveHomeomorph
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    (Variety.ofQuasiProjective hY).carrier ≃ₜ
      (hY.localRingMapAbstractCurve hcurve hns).carrier := by
  change (Variety.ofQuasiProjective hY).carrier ≃ₜ
    Set.range
      ((Variety.hasAffineOpenBasis_ofQuasiProjective hY).localRingMap hcurve hns)
  exact hY.localRingMapHomeomorph hcurve hns

@[simp]
theorem IsQuasiProjVariety.localRingMapAbstractCurveHomeomorph_apply_val
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular)
    (P : (Variety.ofQuasiProjective hY).carrier) :
    ((hY.localRingMapAbstractCurveHomeomorph hcurve hns P).1 :
      ValuationSpace k
        (Variety.ofQuasiProjective hY).FunctionField) =
      (Variety.hasAffineOpenBasis_ofQuasiProjective hY).localRingMap
        hcurve hns P :=
  rfl

@[simp]
theorem IsQuasiProjVariety.of_symm_localRingMapAbstractCurveHomeomorph
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular)
    (P : (Variety.ofQuasiProjective hY).carrier) :
    (ValuationSpace.of k
      (Variety.ofQuasiProjective hY).FunctionField).symm
        (hY.localRingMapAbstractCurveHomeomorph hcurve hns P).1 =
      (Variety.hasAffineOpenBasis_ofQuasiProjective hY).functionFieldDVRAt
        hcurve hns P := by
  rw [hY.localRingMapAbstractCurveHomeomorph_apply_val hcurve hns P]
  exact ValuationSpace.of_symm_apply_apply k _ _

/-- The point-to-local-ring homeomorphism as a morphism to the associated
abstract nonsingular curve. -/
noncomputable def IsQuasiProjVariety.localRingMapAbstractCurveHom
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    VarietyHom (Variety.ofQuasiProjective hY)
      (hY.localRingMapAbstractCurve hcurve hns) := by
  let X := Variety.ofQuasiProjective hY
  let hX := Variety.hasAffineOpenBasis_ofQuasiProjective hY
  let htrdeg : Algebra.trdeg k X.FunctionField = 1 :=
    hX.isCurve_iff_trdeg_eq_one.mp hcurve
  letI : Algebra.EssFiniteType k X.FunctionField :=
    RationalMapFunctionField.essFiniteType_functionField hX
  let U := hY.localRingMapRangeOpen hcurve hns
  let e := hY.localRingMapAbstractCurveHomeomorph hcurve hns
  refine {
    toFun := e
    continuous_toFun := e.continuous
    regular_comp := ?_
  }
  intro V g hg
  let W : Opens X.carrier := Opens.comap ⟨e, e.continuous⟩ V
  change (fun x : W ↦ g ⟨e x.1, x.2⟩) ∈ X.regular W
  change (fun w : pushOpens U V ↦ g (ofPush w)) ∈
    ValuationSpace.regularFunctions htrdeg
      (pushOpens U V : Set (ValuationSpace k X.FunctionField)) at hg
  rw [ValuationSpace.regularFunctions, AlgHom.mem_range] at hg
  obtain ⟨q, hq⟩ := hg
  apply X.regular_of_locally
  intro P
  let zP : V := ⟨e P.1, P.2⟩
  let wP : pushOpens U V := toPush zP
  have hqP : q.1 ∈
      (hX.functionFieldDVRAt hcurve hns P.1).toValuationSubring := by
    have hqP' := ValuationSpace.mem_regularRationalFunctions_iff.mp q.2 wP
    change q.1 ∈
      ((ValuationSpace.of k X.FunctionField).symm (e P.1).1).toValuationSubring at hqP'
    have hRP : (ValuationSpace.of k X.FunctionField).symm (e P.1).1 =
        hX.functionFieldDVRAt hcurve hns P.1 := by
      dsimp only [e, X, hX]
      exact hY.of_symm_localRingMapAbstractCurveHomeomorph hcurve hns P.1
    rw [hRP] at hqP'
    exact hqP'
  let eP := localRingAlgEquivFunctionFieldDVRAt hX hcurve hns P.1
  let a : X.LocalRingAt P.1 := eP.symm ⟨q.1, hqP⟩
  have haP : eP a = ⟨q.1, hqP⟩ := eP.apply_symm_apply _
  have haq : X.localToFunctionFieldAlgHom P.1 a = q.1 := by
    rw [← localRingAlgEquivFunctionFieldDVRAt_coe hX hcurve hns P.1 a]
    exact congrArg Subtype.val haP
  let r : X.GermRep P.1 := Quotient.out a
  let N : Opens X.carrier := r.U ⊓ W
  have hNW : N ≤ W := inf_le_right
  refine ⟨N, hNW, ⟨r.mem_U, P.2⟩, ?_⟩
  have hrN : (fun y : N ↦ r.toFun ⟨y.1, y.2.1⟩) ∈ X.regular N :=
    X.regular_restrict inf_le_left r.regular
  convert hrN using 1
  funext y
  let zY : V := ⟨e y.1, hNW y.2⟩
  let wY : pushOpens U V := toPush zY
  have hqY : q.1 ∈
      (hX.functionFieldDVRAt hcurve hns y.1).toValuationSubring := by
    have hqY' := ValuationSpace.mem_regularRationalFunctions_iff.mp q.2 wY
    change q.1 ∈
      ((ValuationSpace.of k X.FunctionField).symm (e y.1).1).toValuationSubring at hqY'
    have hRY : (ValuationSpace.of k X.FunctionField).symm (e y.1).1 =
        hX.functionFieldDVRAt hcurve hns y.1 := by
      dsimp only [e, X, hX]
      exact hY.of_symm_localRingMapAbstractCurveHomeomorph hcurve hns y.1
    rw [hRY] at hqY'
    exact hqY'
  let ry : X.GermRep y.1 := {
    U := r.U
    mem_U := y.2.1
    toFun := r.toFun
    regular := r.regular
  }
  let ay : X.LocalRingAt y.1 := Quotient.mk _ ry
  have hayq : X.localToFunctionFieldAlgHom y.1 ay = q.1 := by
    calc
      X.localToFunctionFieldAlgHom y.1 ay =
          X.localToFunctionFieldAlgHom P.1
            (Quotient.mk (Variety.germSetoid X P.1) r) := by
              exact Quotient.sound fun _ _ _ ↦ rfl
      _ = X.localToFunctionFieldAlgHom P.1 a :=
        congrArg (X.localToFunctionFieldAlgHom P.1) (Quotient.out_eq a)
      _ = q.1 := haq
  let eY := localRingAlgEquivFunctionFieldDVRAt hX hcurve hns y.1
  have heY : eY ay = ⟨q.1, hqY⟩ := by
    apply Subtype.ext
    rw [localRingAlgEquivFunctionFieldDVRAt_coe, hayq]
  calc
    g zY = ValuationSpace.residueEvaluation htrdeg
        (pushOpens U V : Set (ValuationSpace k X.FunctionField)) q wY := by
      have hw : ofPush wY = zY := by
        dsimp only [wY]
        exact ofPush_toPush zY
      rw [← hw]
      exact (congrFun hq wY).symm
    _ = FunctionFieldDVR.residueAt htrdeg
        ((ValuationSpace.of k X.FunctionField).symm wY.1)
        ⟨q.1, ValuationSpace.mem_regularRationalFunctions_iff.mp q.2 wY⟩ := rfl
    _ = FunctionFieldDVR.residueAt htrdeg
        (hX.functionFieldDVRAt hcurve hns y.1) ⟨q.1, hqY⟩ := by
      congr 2
    _ = FunctionFieldDVR.residueAt htrdeg
        (hX.functionFieldDVRAt hcurve hns y.1) (eY ay) := by rw [heY]
    _ = X.evalAtPoint ay :=
      residueAt_localRingAlgEquivFunctionFieldDVRAt
        hX hcurve hns htrdeg y.1 ay
    _ = r.toFun ⟨y.1, y.2.1⟩ := rfl

/-- The inverse homeomorphism is also a morphism: a regular function on the
original curve gives a rational representative belonging to every valuation
ring over its inverse image. -/
noncomputable def IsQuasiProjVariety.localRingMapAbstractCurveInvHom
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    VarietyHom (hY.localRingMapAbstractCurve hcurve hns)
      (Variety.ofQuasiProjective hY) := by
  let X := Variety.ofQuasiProjective hY
  let hX := Variety.hasAffineOpenBasis_ofQuasiProjective hY
  let htrdeg : Algebra.trdeg k X.FunctionField = 1 :=
    hX.isCurve_iff_trdeg_eq_one.mp hcurve
  letI : Algebra.EssFiniteType k X.FunctionField :=
    RationalMapFunctionField.essFiniteType_functionField hX
  let U := hY.localRingMapRangeOpen hcurve hns
  let e := hY.localRingMapAbstractCurveHomeomorph hcurve hns
  refine {
    toFun := e.symm
    continuous_toFun := e.symm.continuous
    regular_comp := ?_
  }
  intro V g hg
  let T : Opens (hY.localRingMapAbstractCurve hcurve hns).carrier :=
    Opens.comap ⟨e.symm, e.symm.continuous⟩ V
  change (fun z : T ↦ g ⟨e.symm z.1, z.2⟩) ∈
    (hY.localRingMapAbstractCurve hcurve hns).regular T
  change (fun w : pushOpens U T ↦
      g ⟨e.symm (ofPush w).1, (ofPush w).2⟩) ∈
    ValuationSpace.regularFunctions htrdeg
      (pushOpens U T : Set (ValuationSpace k X.FunctionField))
  by_cases hT : (pushOpens U T : Set
      (ValuationSpace k X.FunctionField)).Nonempty
  · have hV : (V : Set X.carrier).Nonempty := by
      obtain ⟨w, hw⟩ := hT
      let z : T := ofPush (⟨w, hw⟩ : pushOpens U T)
      exact ⟨e.symm z.1, z.2⟩
    let r : X.RationalRep := {
      U := V
      nonempty_U := hV
      toFun := g
      regular := hg
    }
    let q : X.FunctionField := Quotient.mk (Variety.rationalSetoid X) r
    have hqmem : ∀ w : pushOpens U T,
        q ∈ ((ValuationSpace.of k X.FunctionField).symm w.1).toValuationSubring := by
      intro w
      let z : T := ofPush w
      let P : X.carrier := e.symm z.1
      have hPV : P ∈ V := z.2
      let rP : X.GermRep P := {
        U := V
        mem_U := hPV
        toFun := g
        regular := hg
      }
      let aP : X.LocalRingAt P := Quotient.mk (Variety.germSetoid X P) rP
      have haPq : X.localToFunctionFieldAlgHom P aP = q := by
        exact Quotient.sound fun _ _ _ ↦ rfl
      have hqP : q ∈
          (hX.functionFieldDVRAt hcurve hns P).toValuationSubring := by
        change q ∈ (hX.valuationSubringAt hcurve P (hns P)).toSubring
        rw [hX.valuationSubringAt_toSubring hcurve P (hns P)]
        exact ⟨aP, haPq⟩
      have hRw : (ValuationSpace.of k X.FunctionField).symm w.1 =
          hX.functionFieldDVRAt hcurve hns P := by
        have heP : e P = z.1 := e.apply_symm_apply z.1
        calc
          (ValuationSpace.of k X.FunctionField).symm w.1 =
              (ValuationSpace.of k X.FunctionField).symm (e P).1 := by
                congr 1
                exact (congrArg Subtype.val heP).symm
          _ = hX.functionFieldDVRAt hcurve hns P := by
            dsimp only [e, X, hX]
            exact hY.of_symm_localRingMapAbstractCurveHomeomorph hcurve hns P
      rw [hRw]
      exact hqP
    let qreg : ValuationSpace.regularRationalFunctions
        (k := k) (K := X.FunctionField) (pushOpens U T) :=
      ⟨q, ValuationSpace.mem_regularRationalFunctions_iff.mpr hqmem⟩
    rw [ValuationSpace.regularFunctions, AlgHom.mem_range]
    refine ⟨qreg, ?_⟩
    funext w
    let z : T := ofPush w
    let P : X.carrier := e.symm z.1
    have hPV : P ∈ V := z.2
    let rP : X.GermRep P := {
      U := V
      mem_U := hPV
      toFun := g
      regular := hg
    }
    let aP : X.LocalRingAt P := Quotient.mk (Variety.germSetoid X P) rP
    have haPq : X.localToFunctionFieldAlgHom P aP = q := by
      exact Quotient.sound fun _ _ _ ↦ rfl
    have hqP : q ∈
        (hX.functionFieldDVRAt hcurve hns P).toValuationSubring := by
      change q ∈ (hX.valuationSubringAt hcurve P (hns P)).toSubring
      rw [hX.valuationSubringAt_toSubring hcurve P (hns P)]
      exact ⟨aP, haPq⟩
    have hRw : (ValuationSpace.of k X.FunctionField).symm w.1 =
        hX.functionFieldDVRAt hcurve hns P := by
      have heP : e P = z.1 := e.apply_symm_apply z.1
      calc
        (ValuationSpace.of k X.FunctionField).symm w.1 =
            (ValuationSpace.of k X.FunctionField).symm (e P).1 := by
              congr 1
              exact (congrArg Subtype.val heP).symm
        _ = hX.functionFieldDVRAt hcurve hns P := by
          dsimp only [e, X, hX]
          exact hY.of_symm_localRingMapAbstractCurveHomeomorph hcurve hns P
    let eP := localRingAlgEquivFunctionFieldDVRAt hX hcurve hns P
    have hePa : eP aP = ⟨q, hqP⟩ := by
      apply Subtype.ext
      rw [localRingAlgEquivFunctionFieldDVRAt_coe, haPq]
    change FunctionFieldDVR.residueAt htrdeg
        ((ValuationSpace.of k X.FunctionField).symm w.1)
          ⟨q, hqmem w⟩ = g ⟨e.symm z.1, z.2⟩
    calc
      FunctionFieldDVR.residueAt htrdeg
          ((ValuationSpace.of k X.FunctionField).symm w.1) ⟨q, hqmem w⟩ =
          FunctionFieldDVR.residueAt htrdeg
            (hX.functionFieldDVRAt hcurve hns P) ⟨q, hqP⟩ := by
              exact residueAt_eq_of_dvr_eq htrdeg hRw q (hqmem w) hqP
      _ = FunctionFieldDVR.residueAt htrdeg
          (hX.functionFieldDVRAt hcurve hns P) (eP aP) := by rw [hePa]
      _ = X.evalAtPoint aP :=
        residueAt_localRingAlgEquivFunctionFieldDVRAt
          hX hcurve hns htrdeg P aP
      _ = g ⟨P, hPV⟩ := rfl
  · rw [ValuationSpace.regularFunctions, AlgHom.mem_range]
    refine ⟨0, ?_⟩
    funext w
    exact (hT ⟨w.1, w.2⟩).elim

/-- **Hartshorne I.6, Proposition 6.7.** The point-to-local-ring map identifies
a nonsingular quasi-projective curve with the abstract nonsingular curve on
its open image, as an isomorphism of varieties. -/
theorem IsQuasiProjVariety.localRingMapAbstractCurveHom_isIso
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    (hY.localRingMapAbstractCurveHom hcurve hns).IsIso := by
  refine ⟨hY.localRingMapAbstractCurveInvHom hcurve hns, ?_, ?_⟩
  · apply VarietyHom.ext
    funext P
    change (hY.localRingMapAbstractCurveHomeomorph hcurve hns).symm
        (hY.localRingMapAbstractCurveHomeomorph hcurve hns P) = P
    exact (hY.localRingMapAbstractCurveHomeomorph hcurve hns).symm_apply_apply P
  · apply VarietyHom.ext
    funext R
    change hY.localRingMapAbstractCurveHomeomorph hcurve hns
        ((hY.localRingMapAbstractCurveHomeomorph hcurve hns).symm R) = R
    exact (hY.localRingMapAbstractCurveHomeomorph hcurve hns).apply_symm_apply R

end

end Hartshorne
