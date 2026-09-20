/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.RationalMapFunctionField
import Hartshorne.Morphism.AffineRationalCompare
import Hartshorne.Morphism.FunctionFieldFractions
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The rational-map/function-field equivalence

Hartshorne, *Algebraic Geometry*, I.4, Theorem 4.4.  The affine-target
correspondence is transported across an affine open chart of the target.  This
gives a bijection between dominant rational maps `X ⇢ Y` and `k`-algebra maps
`K(Y) → K(X)` whenever `Y` is separated and has an affine open basis.  The
correspondence is then packaged as an arrow-reversing categorical equivalence.

## Main definitions

* `Hartshorne.RationalMapFunctionField.dominantRatMapEquivFunctionFieldAlgHom`
* `Hartshorne.RationalMapFunctionField.RationalVarietyCat`
* `Hartshorne.RationalMapFunctionField.FgFieldCat`
* `Hartshorne.RationalMapFunctionField.functionFieldFunctor`
* `Hartshorne.RationalMapFunctionField.functionFieldEquivalence`
-/

namespace Hartshorne

open CategoryTheory MvPolynomial TopologicalSpace

universe u v

namespace RationalMapFunctionField

variable {k : Type u} [Field k]
variable {X Y : Variety k}

/-! ## Function fields and nonempty open subvarieties -/

noncomputable def pushRationalRep (X : Variety k) (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty)
    (r : Variety.RationalRep (X.restrict U hU)) : Variety.RationalRep X where
  U := pushOpens U r.U
  nonempty_U := by
    obtain ⟨x, hx⟩ := r.nonempty_U
    exact ⟨x.1, x.2, fun _ => hx⟩
  toFun := fun x => r.toFun (ofPush x)
  regular := r.regular

theorem pushRationalRep_congr (X : Variety k) (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty)
    {r s : Variety.RationalRep (X.restrict U hU)}
    (hrs : r.Rel s) :
    (pushRationalRep X U hU r).Rel (pushRationalRep X U hU s) := by
  intro x hxr hxs
  exact hrs ⟨x, hxr.1⟩ (hxr.2 hxr.1) (hxs.2 hxs.1)

noncomputable def pushFunctionField (X : Variety k) (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty) :
    (X.restrict U hU).FunctionField → X.FunctionField :=
  Quotient.map (pushRationalRep X U hU)
    (fun _ _ h => pushRationalRep_congr X U hU h)

theorem pushFunctionField_leftInverse (X : Variety k) (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty) :
    Function.LeftInverse (pushFunctionField X U hU)
      ((X.inclHom U hU).functionFieldHom
        (X.dense_range_inclHom_open U hU)) := by
  refine Quotient.ind fun r => ?_
  apply Quotient.sound
  intro x hx hs
  rfl

theorem pushFunctionField_rightInverse (X : Variety k) (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty) :
    Function.RightInverse (pushFunctionField X U hU)
      ((X.inclHom U hU).functionFieldHom
        (X.dense_range_inclHom_open U hU)) := by
  refine Quotient.ind fun r => ?_
  apply Quotient.sound
  intro x hx hs
  rfl

noncomputable def openFunctionFieldAlgEquiv (X : Variety k)
    (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty) :
    X.FunctionField ≃ₐ[k] (X.restrict U hU).FunctionField :=
  AlgEquiv.ofBijective
    ((X.inclHom U hU).functionFieldAlgHom
      (X.dense_range_inclHom_open U hU))
    ⟨(pushFunctionField_leftInverse X U hU).injective,
      (pushFunctionField_rightInverse X U hU).surjective⟩

noncomputable def functionFieldAlgEquivOfIsIso (f : VarietyHom X Y)
    (hf : f.IsIso) : Y.FunctionField ≃ₐ[k] X.FunctionField :=
  AlgEquiv.ofBijective
    (f.functionFieldAlgHom hf.bijective.2.denseRange)
    (f.bijective_functionFieldHom_of_isIso hf hf.bijective.2.denseRange)

variable {σ : Type u}

noncomputable def functionFieldAlgEquivAffine {τ : Type v} {Z : Set (τ → k)}
    (hZ : IsQuasiAffineVariety Z) :
    (Variety.ofQuasiAffine hZ).FunctionField ≃ₐ[k]
      FunctionField hZ.isIrreducible where
  __ := functionFieldEquivAffine hZ
  commutes' _ := rfl

noncomputable def affinePresentationFunctionFieldAlgEquiv
    {Z : Set (σ → k)} (hZ : IsAffineVariety Z)
    (f : VarietyHom X (Variety.ofQuasiAffine hZ.isQuasiAffineVariety))
    (hf : f.IsIso) :
    X.FunctionField ≃ₐ[k] FunctionField hZ.isIrreducible :=
  (functionFieldAlgEquivOfIsIso f hf).symm.trans
    (functionFieldAlgEquivAffine hZ.isQuasiAffineVariety)

/-! ## Affine charts as inverse dominant rational maps -/

theorem isSeparated_ofQuasiAffine {τ : Type v} {Z : Set (τ → k)}
    (hZ : IsQuasiAffineVariety Z) :
    (Variety.ofQuasiAffine hZ).IsSeparated := by
  intro A f g U hU hUne hfg
  apply VarietyHom.ext
  funext x
  apply Subtype.ext
  funext i
  have hf : A.IsGlobalRegular fun x => (f x).1 i :=
    (exists_varietyHom_iff_coords_regular hZ f.toFun).1 ⟨f, rfl⟩ i
  have hg : A.IsGlobalRegular fun x => (g x).1 i :=
    (exists_varietyHom_iff_coords_regular hZ g.toFun).1 ⟨g, rfl⟩ i
  let U' : Set (⊤ : Opens A.carrier) := {x | x.1 ∈ U}
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  have hUne' : U'.Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    exact ⟨⟨x, trivial⟩, hx⟩
  have heq : Set.EqOn
      (fun x : (⊤ : Opens A.carrier) => (f x.1).1 i)
      (fun x : (⊤ : Opens A.carrier) => (g x.1).1 i) U' :=
    fun x hx => congrArg (fun y : Z => y.1 i) (hfg x.1 hx)
  have hall := Variety.eq_of_eqOn hf hg hU' hUne' heq
  exact congrFun hall ⟨x, trivial⟩

noncomputable def affineChartRatMap {Y : Variety k} {Z : Set (σ → k)}
    (V : Opens Y.carrier) (hV : (V : Set Y.carrier).Nonempty)
    (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso) :
    DominantRatMap Y (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)
      (isSeparated_ofQuasiAffine hZ.isQuasiAffineVariety) :=
  Quotient.mk _
    { rep := { U := V, nonempty_U := hV, hom := f }
      isDominant := hf.bijective.2.denseRange }

noncomputable def affineChartRatMapInv {Y : Variety k} (hY : Y.IsSeparated)
    {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso) :
    DominantRatMap (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) Y hY := by
  let g : VarietyHom (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)
      (Y.restrict V hV) := Classical.choose hf
  have hgf : g.comp f = VarietyHom.id (Y.restrict V hV) :=
    (Classical.choose_spec hf).1
  have hg_surj : Function.Surjective g.toFun := by
    intro y
    refine ⟨f y, ?_⟩
    have he := congrArg
      (fun q : VarietyHom (Y.restrict V hV) (Y.restrict V hV) => q y) hgf
    simpa [g] using he
  let j := Y.inclHom V hV
  let A := Variety.ofQuasiAffine hZ.isQuasiAffineVariety
  let t := A.inclHom ⊤ Set.univ_nonempty
  have ht_surj : Function.Surjective t.toFun :=
    fun a => ⟨⟨a, trivial⟩, rfl⟩
  refine Quotient.mk _
    { rep := { U := ⊤, nonempty_U := Set.univ_nonempty, hom := j.comp (g.comp t) }
      isDominant := ?_ }
  have hgt : DenseRange (g.toFun ∘ t.toFun) :=
    DenseRange.comp hg_surj.denseRange ht_surj.denseRange g.continuous_toFun
  have hjgt : DenseRange (j.toFun ∘ (g.toFun ∘ t.toFun)) :=
    DenseRange.comp (Y.dense_range_inclHom_open V hV) hgt j.continuous_toFun
  exact hjgt

theorem affineChartRatMapInv_comp {Y : Variety k} (hY : Y.IsSeparated)
    {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso) :
    DominantRatMap.comp (affineChartRatMapInv hY V hV hZ f hf)
      (affineChartRatMap V hV hZ f hf) = DominantRatMap.id Y hY := by
  apply Quotient.sound
  intro y hy _
  change (((Classical.choose hf).comp f) ⟨y, hy.1⟩).1 = y
  have he := congrArg
    (fun q : VarietyHom (Y.restrict V hV) (Y.restrict V hV) =>
      q ⟨y, hy.1⟩) (Classical.choose_spec hf).1
  exact congrArg Subtype.val he

theorem affineChartRatMap_comp_inv {Y : Variety k} (hY : Y.IsSeparated)
    {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso) :
    DominantRatMap.comp (affineChartRatMap V hV hZ f hf)
      (affineChartRatMapInv hY V hV hZ f hf) =
        DominantRatMap.id (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)
          (isSeparated_ofQuasiAffine hZ.isQuasiAffineVariety) := by
  apply Quotient.sound
  intro z _ _
  change f (Classical.choose hf z) = z
  have he := congrArg
    (fun q : VarietyHom (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) => q z)
    (Classical.choose_spec hf).2
  simpa using he

noncomputable def postcomposeAffineChartEquiv {X Y : Variety k}
    (hY : Y.IsSeparated) {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso) :
    DominantRatMap X Y hY ≃
      DominantRatMap X (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)
        (isSeparated_ofQuasiAffine hZ.isQuasiAffineVariety) where
  toFun r := DominantRatMap.comp (affineChartRatMap V hV hZ f hf) r
  invFun r := DominantRatMap.comp (affineChartRatMapInv hY V hV hZ f hf) r
  left_inv r := by
    change DominantRatMap.comp (affineChartRatMapInv hY V hV hZ f hf)
      (DominantRatMap.comp (affineChartRatMap V hV hZ f hf) r) = r
    rw [← DominantRatMap.assoc,
      affineChartRatMapInv_comp hY V hV hZ f hf,
      DominantRatMap.id_comp]
  right_inv r := by
    change DominantRatMap.comp (affineChartRatMap V hV hZ f hf)
      (DominantRatMap.comp (affineChartRatMapInv hY V hV hZ f hf) r) = r
    rw [← DominantRatMap.assoc,
      affineChartRatMap_comp_inv hY V hV hZ f hf,
      DominantRatMap.id_comp]

noncomputable def affineChartFunctionFieldAlgEquiv {Y : Variety k}
    {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso) :
    Y.FunctionField ≃ₐ[k]
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField :=
  (openFunctionFieldAlgEquiv Y V hV).trans
    (functionFieldAlgEquivOfIsIso f hf).symm

noncomputable def precomposeAffineChartEquiv {X Y : Variety k}
    {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso) :
    (Y.FunctionField →ₐ[k] X.FunctionField) ≃
      ((Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField →ₐ[k]
        X.FunctionField) where
  toFun θ := θ.comp (affineChartFunctionFieldAlgEquiv V hV hZ f hf).symm.toAlgHom
  invFun θ := θ.comp (affineChartFunctionFieldAlgEquiv V hV hZ f hf).toAlgHom
  left_inv θ := by
    apply AlgHom.ext
    intro a
    simp
  right_inv θ := by
    apply AlgHom.ext
    intro a
    simp

theorem restrict_functionFieldAlgHom_affineChartRatMap {Y : Variety k}
    {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso) :
    (openFunctionFieldAlgEquiv Y V hV).toAlgHom.comp
        (DominantRatMap.functionFieldAlgHom (affineChartRatMap V hV hZ f hf)) =
      f.functionFieldAlgHom hf.bijective.2.denseRange := by
  ext q
  refine Quotient.inductionOn q ?_
  intro r
  apply Quotient.sound
  intro x hx hx'
  rfl

theorem functionFieldAlgHom_affineChartRatMap {Y : Variety k}
    {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso) :
    DominantRatMap.functionFieldAlgHom (affineChartRatMap V hV hZ f hf) =
      (affineChartFunctionFieldAlgEquiv V hV hZ f hf).symm.toAlgHom := by
  apply AlgHom.ext
  intro q
  let e := affineChartFunctionFieldAlgEquiv V hV hZ f hf
  apply e.injective
  calc
    e (DominantRatMap.functionFieldAlgHom
        (affineChartRatMap V hV hZ f hf) q) = q := by
      change (functionFieldAlgEquivOfIsIso f hf).symm
        (openFunctionFieldAlgEquiv Y V hV
          (DominantRatMap.functionFieldAlgHom
            (affineChartRatMap V hV hZ f hf) q)) = q
      rw [show openFunctionFieldAlgEquiv Y V hV
          (DominantRatMap.functionFieldAlgHom
            (affineChartRatMap V hV hZ f hf) q) =
          f.functionFieldAlgHom hf.bijective.2.denseRange q by
            exact AlgHom.congr_fun
              (restrict_functionFieldAlgHom_affineChartRatMap V hV hZ f hf) q]
      exact (functionFieldAlgEquivOfIsIso f hf).symm_apply_apply q
    _ = e (e.symm q) := (e.apply_symm_apply q).symm

theorem functionFieldAlgHom_postcomposeAffineChart {X Y : Variety k}
    (hY : Y.IsSeparated) {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso)
    (q : DominantRatMap X Y hY) :
    precomposeAffineChartEquiv (X := X) V hV hZ f hf
        (DominantRatMap.functionFieldAlgHom q) =
      DominantRatMap.functionFieldAlgHom
        (postcomposeAffineChartEquiv hY V hV hZ f hf q) := by
  change (DominantRatMap.functionFieldAlgHom q).comp
      (affineChartFunctionFieldAlgEquiv V hV hZ f hf).symm.toAlgHom =
    DominantRatMap.functionFieldAlgHom
      (DominantRatMap.comp (affineChartRatMap V hV hZ f hf) q)
  rw [← functionFieldAlgHom_affineChartRatMap V hV hZ f hf]
  exact (DominantRatMap.functionFieldAlgHom_comp
    (affineChartRatMap V hV hZ f hf) q).symm

theorem bijective_functionFieldAlgHom_of_affineChart {X Y : Variety k}
    (hY : Y.IsSeparated) {Z : Set (σ → k)} (V : Opens Y.carrier)
    (hV : (V : Set Y.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (f : VarietyHom (Y.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hf : f.IsIso)
    (hAffine : Function.Bijective
      (@DominantRatMap.functionFieldAlgHom k _ X
        (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)
        (isSeparated_ofQuasiAffine hZ.isQuasiAffineVariety))) :
    Function.Bijective (@DominantRatMap.functionFieldAlgHom k _ X Y hY) := by
  let eMap := postcomposeAffineChartEquiv (X := X) hY V hV hZ f hf
  let eHom := precomposeAffineChartEquiv (X := X) V hV hZ f hf
  constructor
  · intro q₁ q₂ hq
    apply eMap.injective
    apply hAffine.1
    rw [← functionFieldAlgHom_postcomposeAffineChart hY V hV hZ f hf q₁,
      ← functionFieldAlgHom_postcomposeAffineChart hY V hV hZ f hf q₂,
      hq]
  · intro θ
    obtain ⟨qA, hqA⟩ := hAffine.2 (eHom θ)
    refine ⟨eMap.symm qA, ?_⟩
    apply eHom.injective
    rw [functionFieldAlgHom_postcomposeAffineChart, eMap.apply_symm_apply, hqA]

theorem bijective_functionFieldAlgHom_of_hasAffineOpenBasis [IsAlgClosed k]
    {X Y : Variety k} (hY : Y.IsSeparated) (hYaff : Y.HasAffineOpenBasis) :
    Function.Bijective (@DominantRatMap.functionFieldAlgHom k _ X Y hY) := by
  let y : Y.carrier := Y.nonempty.some
  obtain ⟨V, hV, -, -, τ, hτ, Z, hZ, f, hf⟩ := hYaff ⊤ y trivial
  let _ : Finite τ := hτ
  apply bijective_functionFieldAlgHom_of_affineChart hY V hV hZ f hf
  exact ⟨DominantRatMap.functionFieldAlgHom_injective_affine hZ
      (isSeparated_ofQuasiAffine hZ.isQuasiAffineVariety),
    DominantRatMap.functionFieldAlgHom_surjective_affine hZ
      (isSeparated_ofQuasiAffine hZ.isQuasiAffineVariety)⟩

/-- Hartshorne I.4.4 for a separated target admitting an affine open basis. -/
noncomputable def dominantRatMapEquivFunctionFieldAlgHom [IsAlgClosed k]
    {X Y : Variety k} (hY : Y.IsSeparated) (hYaff : Y.HasAffineOpenBasis) :
    DominantRatMap X Y hY ≃ (Y.FunctionField →ₐ[k] X.FunctionField) :=
  Equiv.ofBijective DominantRatMap.functionFieldAlgHom
    (bijective_functionFieldAlgHom_of_hasAffineOpenBasis hY hYaff)

/-! ## Essential finite generation and realization -/

theorem essFiniteType_affineFunctionField [IsAlgClosed k] [Finite σ]
    {Z : Set (σ → k)} (hZ : IsAffineVariety Z) :
    Algebra.EssFiniteType k (FunctionField hZ.isIrreducible) := by
  let _ : IsDomain (coordinateRing Z) := isDomain_coordinateRing hZ
  let _ : IsFractionRing (coordinateRing Z)
      (FunctionField hZ.isIrreducible) :=
    isFractionRing_functionField hZ.isIrreducible
  have _ : Algebra.EssFiniteType k (coordinateRing Z) := inferInstance
  let _ : Algebra.EssFiniteType (coordinateRing Z)
      (FunctionField hZ.isIrreducible) :=
    Algebra.EssFiniteType.of_isLocalization _
      (nonZeroDivisors (coordinateRing Z))
  exact Algebra.EssFiniteType.comp k (coordinateRing Z)
    (FunctionField hZ.isIrreducible)

theorem essFiniteType_functionField [IsAlgClosed k]
    (hX : X.HasAffineOpenBasis) :
    Algebra.EssFiniteType k X.FunctionField := by
  let x : X.carrier := X.nonempty.some
  obtain ⟨U, hU, -, -, τ, hτ, Z, hZ, f, hf⟩ := hX ⊤ x trivial
  let _ : Finite τ := hτ
  let e := (openFunctionFieldAlgEquiv X U hU).trans
    (affinePresentationFunctionFieldAlgEquiv hZ f hf)
  exact (Algebra.EssFiniteType.iff_of_algEquiv e).mpr
    (essFiniteType_affineFunctionField hZ)

theorem exists_affine_functionField_algEquiv [IsAlgClosed k]
    (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    ∃ (n : ℕ) (Z : Set (Fin n → k)) (hZ : IsAffineVariety Z),
      Nonempty
        ((Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField ≃ₐ[k] K) := by
  let B := Algebra.EssFiniteType.subalgebra k K
  have _ : Algebra.FiniteType k B := inferInstance
  have _ : IsDomain B := inferInstance
  obtain ⟨n, Z, hZ, ⟨e⟩⟩ :=
    exists_isAffineVariety_coordinateRing_equiv (k := k) (B := B)
  let _ : IsDomain (coordinateRing Z) := isDomain_coordinateRing hZ
  let _ : IsFractionRing (coordinateRing Z)
      (FunctionField hZ.isIrreducible) :=
    isFractionRing_functionField hZ.isIrreducible
  have hM : Algebra.EssFiniteType.submonoid k K = nonZeroDivisors B := by
    ext x
    simp only [Algebra.EssFiniteType.submonoid, Submonoid.mem_comap,
      IsUnit.mem_submonoid_iff]
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rw [show IsUnit (algebraMap B K x) ↔ algebraMap B K x ≠ 0 from
      isUnit_iff_ne_zero]
    exact map_ne_zero_iff _ Subtype.val_injective
  have hfrac : IsFractionRing B K := by
    change IsLocalization (nonZeroDivisors B) K
    rw [← hM]
    infer_instance
  let _ : IsFractionRing B K := hfrac
  let efrac : FunctionField hZ.isIrreducible ≃ₐ[k] K :=
    IsFractionRing.algEquivOfAlgEquiv e
  let eaff : (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField ≃ₐ[k]
      FunctionField hZ.isIrreducible :=
    { __ := functionFieldEquivAffine hZ.isQuasiAffineVariety
      commutes' := fun _ => rfl }
  exact ⟨n, Z, hZ, ⟨eaff.trans efrac⟩⟩

/-- Same-universe affine realization, needed because `Variety.IsAffine` and
`Variety.HasAffineOpenBasis` presently use ambient coordinate types in the
same universe as the base field. -/
theorem exists_isAffineVariety_coordinateRing_equiv_sameUniverse
    {B : Type u} [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsAlgClosed k] :
    ∃ (τ : Type u) (_ : Finite τ) (Z : Set (τ → k)),
      IsAffineVariety Z ∧ Nonempty (coordinateRing Z ≃ₐ[k] B) := by
  obtain ⟨τ, hτ, f, hf⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial'.1
      (inferInstance : Algebra.FiniteType k B)
  let _ : Fintype τ := hτ
  have hker : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  refine ⟨τ, inferInstance, zeroLocus k (RingHom.ker f),
    isAffineVariety_zeroLocus_of_isPrime hker, ⟨?_⟩⟩
  exact (Ideal.quotientEquivAlgOfEq k
      (vanishingIdeal_zeroLocus_of_isPrime hker)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)

/-! ## Categorical formulation -/

/-- Fields essentially of finite type over `k`. -/
def IsFgField (k : Type u) [Field k] : ObjectProperty (CommAlgCat.{u} k) :=
  fun K => IsField K ∧ Algebra.EssFiniteType k K

/-- The full subcategory of `k`-algebras that are fields essentially of finite type. -/
abbrev FgFieldCat (k : Type u) [Field k] :=
  (IsFgField k).FullSubcategory

/-- Separated varieties with an affine open basis, with dominant rational maps. -/
structure RationalVarietyCat (k : Type u) [Field k] where
  toVariety : Variety k
  isSeparated : toVariety.IsSeparated
  hasAffineOpenBasis : toVariety.HasAffineOpenBasis

/-- Every essentially finite type field extension is the function field of
an affine object, with the affine presentation kept in the base-field universe. -/
theorem exists_rationalVariety_functionField_algEquiv [IsAlgClosed k]
    (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    ∃ A : RationalVarietyCat k,
      Nonempty (A.toVariety.FunctionField ≃ₐ[k] K) := by
  let B := Algebra.EssFiniteType.subalgebra k K
  let _ : Algebra.FiniteType k B := inferInstance
  let _ : IsDomain B := inferInstance
  obtain ⟨τ, hτ, Z, hZ, ⟨e⟩⟩ :=
    exists_isAffineVariety_coordinateRing_equiv_sameUniverse
      (k := k) (B := B)
  let _ : Finite τ := hτ
  let _ : IsDomain (coordinateRing Z) := isDomain_coordinateRing hZ
  let _ : IsFractionRing (coordinateRing Z)
      (FunctionField hZ.isIrreducible) :=
    isFractionRing_functionField hZ.isIrreducible
  have hM : Algebra.EssFiniteType.submonoid k K = nonZeroDivisors B := by
    ext x
    simp only [Algebra.EssFiniteType.submonoid, Submonoid.mem_comap,
      IsUnit.mem_submonoid_iff]
    rw [mem_nonZeroDivisors_iff_ne_zero]
    rw [show IsUnit (algebraMap B K x) ↔ algebraMap B K x ≠ 0 from
      isUnit_iff_ne_zero]
    exact map_ne_zero_iff _ Subtype.val_injective
  have hfrac : IsFractionRing B K := by
    change IsLocalization (nonZeroDivisors B) K
    rw [← hM]
    infer_instance
  let _ : IsFractionRing B K := hfrac
  let efrac : FunctionField hZ.isIrreducible ≃ₐ[k] K :=
    IsFractionRing.algEquivOfAlgEquiv e
  let A : RationalVarietyCat k :=
    { toVariety := Variety.ofQuasiAffine hZ.isQuasiAffineVariety
      isSeparated := isSeparated_ofQuasiAffine hZ.isQuasiAffineVariety
      hasAffineOpenBasis := Variety.hasAffineOpenBasis_ofAffine hZ }
  exact ⟨A,
    ⟨(functionFieldAlgEquivAffine hZ.isQuasiAffineVariety).trans efrac⟩⟩

namespace RationalVarietyCat

noncomputable instance : Category (RationalVarietyCat k) where
  Hom X Y := DominantRatMap X.toVariety Y.toVariety Y.isSeparated
  id X := DominantRatMap.id X.toVariety X.isSeparated
  comp f g := DominantRatMap.comp g f
  id_comp := fun {X _} f => DominantRatMap.comp_id (hX := X.isSeparated) f
  comp_id := fun {_ _} f => DominantRatMap.id_comp f
  assoc := fun {_ _ _ _} f g h => (DominantRatMap.assoc f g h).symm

@[simp]
theorem id_def (X : RationalVarietyCat k) :
    (𝟙 X : X ⟶ X) = DominantRatMap.id X.toVariety X.isSeparated :=
  rfl

@[simp]
theorem comp_def {X Y Z : RationalVarietyCat k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = DominantRatMap.comp g f :=
  rfl

end RationalVarietyCat

noncomputable def functionFieldObj [IsAlgClosed k]
    (X : RationalVarietyCat k) : FgFieldCat k where
  obj := CommAlgCat.of k X.toVariety.FunctionField
  property := ⟨Variety.isField_functionField,
    essFiniteType_functionField X.hasAffineOpenBasis⟩

/-- The contravariant function-field functor. -/
noncomputable def functionFieldFunctor [IsAlgClosed k] :
    (RationalVarietyCat k)ᵒᵖ ⥤ FgFieldCat k where
  obj X := functionFieldObj X.unop
  map f := ObjectProperty.homMk
    (CommAlgCat.ofHom (DominantRatMap.functionFieldAlgHom f.unop))
  map_id X := by
    apply ObjectProperty.hom_ext
    show CommAlgCat.ofHom
      (DominantRatMap.functionFieldAlgHom (DominantRatMap.id
        X.unop.toVariety X.unop.isSeparated)) = _
    rw [DominantRatMap.functionFieldAlgHom_id]
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    show CommAlgCat.ofHom
      (DominantRatMap.functionFieldAlgHom
        (DominantRatMap.comp f.unop g.unop)) = _
    rw [DominantRatMap.functionFieldAlgHom_comp]
    rfl

instance faithful_functionFieldFunctor [IsAlgClosed k] :
    (functionFieldFunctor (k := k)).Faithful where
  map_injective {X Y} {f g} h := by
    apply Quiver.Hom.unop_inj
    apply (dominantRatMapEquivFunctionFieldAlgHom
      X.unop.isSeparated X.unop.hasAffineOpenBasis).injective
    exact congrArg
      (fun m => CommAlgCat.Hom.hom (InducedCategory.Hom.hom m)) h

instance full_functionFieldFunctor [IsAlgClosed k] :
    (functionFieldFunctor (k := k)).Full where
  map_surjective {X Y} ψ := by
    let e := dominantRatMapEquivFunctionFieldAlgHom
      (X := Y.unop.toVariety) (Y := X.unop.toVariety)
      X.unop.isSeparated X.unop.hasAffineOpenBasis
    let θ := CommAlgCat.Hom.hom (InducedCategory.Hom.hom ψ)
    let q : Y.unop ⟶ X.unop := e.symm θ
    refine ⟨q.op, ?_⟩
    apply ObjectProperty.hom_ext
    show CommAlgCat.ofHom (DominantRatMap.functionFieldAlgHom q) = _
    have hq : DominantRatMap.functionFieldAlgHom q = θ := e.apply_symm_apply θ
    rw [hq]
    rfl

instance essSurj_functionFieldFunctor [IsAlgClosed k] :
    (functionFieldFunctor (k := k)).EssSurj where
  mem_essImage K := by
    let _ : Field K.obj := K.property.1.toField
    let _ : Algebra.EssFiniteType k K.obj := K.property.2
    obtain ⟨A, ⟨e⟩⟩ :=
      exists_rationalVariety_functionField_algEquiv (k := k) K.obj
    exact ⟨Opposite.op A,
      ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk e)⟩⟩

instance isEquivalence_functionFieldFunctor [IsAlgClosed k] :
    (functionFieldFunctor (k := k)).IsEquivalence where

/-- The function-field functor is an equivalence of categories. -/
theorem functionFieldFunctor_isEquivalence [IsAlgClosed k] :
    (functionFieldFunctor (k := k)).IsEquivalence :=
  inferInstance

/-- The arrow-reversing categorical form of Hartshorne I.4.4. -/
noncomputable def functionFieldEquivalence [IsAlgClosed k] :
    (RationalVarietyCat k)ᵒᵖ ≌ FgFieldCat k :=
  (functionFieldFunctor (k := k)).asEquivalence

end RationalMapFunctionField

end Hartshorne
