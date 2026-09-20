/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.BirationalMap
import Hartshorne.Rational.RationalMapFunctionFieldEquivalence

/-!
# The birational criterion

Hartshorne, *Algebraic Geometry*, I.4, Corollary 4.5.

Two varieties are birational exactly when they contain isomorphic nonempty
open subvarieties. For separated varieties with affine-open bases, this is also
equivalent to their function fields being isomorphic over the ground field.

## Main results

* `Hartshorne.Variety.HasIsomorphicOpenSubsets`
* `Hartshorne.birational_iff_hasIsomorphicOpenSubsets`
* `Hartshorne.birational_iff_nonempty_functionField_algEquiv`
* `Hartshorne.hasIsomorphicOpenSubsets_iff_nonempty_functionField_algEquiv`
* `Hartshorne.birational_criterion`
-/

namespace Hartshorne

open TopologicalSpace
open CategoryTheory

universe u v

variable {k : Type u} [Field k]

/-- Two varieties have isomorphic nonempty open subvarieties when there are
nonempty opens in each and a variety isomorphism between their restrictions. -/
def Variety.HasIsomorphicOpenSubsets (X Y : Variety.{u, v} k) : Prop :=
  ∃ (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty)
    (V : Opens Y.carrier) (hV : (V : Set Y.carrier).Nonempty)
    (f : VarietyHom (X.restrict U hU) (Y.restrict V hV)), f.IsIso

/-- **The open-subvariety form of the birational criterion.**

Two separated varieties are birational exactly when they contain isomorphic
nonempty open subvarieties. -/
theorem birational_iff_hasIsomorphicOpenSubsets
    (X Y : SeparatedVariety.{u, v} k) :
    Birational X Y ↔
      X.toVariety.HasIsomorphicOpenSubsets Y.toVariety := by
  constructor
  · rintro ⟨e⟩
    let ehom : DominantRatMap X.toVariety Y.toVariety Y.isSeparated := e.hom
    let einv : DominantRatMap Y.toVariety X.toVariety X.isSeparated := e.inv
    let r : DominantRatMapRep X.toVariety Y.toVariety := Quotient.out ehom
    let s : DominantRatMapRep Y.toVariety X.toVariety := Quotient.out einv
    let qr : DominantRatMap X.toVariety Y.toVariety Y.isSeparated :=
      Quotient.mk _ r
    let qs : DominantRatMap Y.toVariety X.toVariety X.isSeparated :=
      Quotient.mk _ s
    have hqr : qr = ehom := by
      dsimp [qr, r]
      exact Quotient.out_eq ehom
    have hqs : qs = einv := by
      dsimp [qs, s]
      exact Quotient.out_eq einv
    have heX : DominantRatMap.comp einv ehom =
        DominantRatMap.id X.toVariety X.isSeparated := by
      exact e.hom_inv_id
    have heY : DominantRatMap.comp ehom einv =
        DominantRatMap.id Y.toVariety Y.isSeparated := by
      exact e.inv_hom_id
    have hsr : DominantRatMapRep.Rel (s.comp r)
        (DominantRatMapRep.id X.toVariety) := by
      have hq : (⟦s.comp r⟧ : DominantRatMap X.toVariety X.toVariety
          X.isSeparated) = ⟦DominantRatMapRep.id X.toVariety⟧ := by
        change DominantRatMap.comp qs qr =
          DominantRatMap.id X.toVariety X.isSeparated
        rw [hqs, hqr]
        exact heX
      exact Quotient.exact hq
    have hrs : DominantRatMapRep.Rel (r.comp s)
        (DominantRatMapRep.id Y.toVariety) := by
      have hq : (⟦r.comp s⟧ : DominantRatMap Y.toVariety Y.toVariety
          Y.isSeparated) = ⟦DominantRatMapRep.id Y.toVariety⟧ := by
        change DominantRatMap.comp qr qs =
          DominantRatMap.id Y.toVariety Y.isSeparated
        rw [hqr, hqs]
        exact heY
      exact Quotient.exact hq
    let U : Opens X.toVariety.carrier :=
      Variety.preimageOpens r.rep.nonempty_U r.rep.hom s.rep.U
    let hU : (U : Set X.toVariety.carrier).Nonempty :=
      RatMapRep.compDomain_nonempty s.rep r.rep r.isDominant
    let V : Opens Y.toVariety.carrier :=
      Variety.preimageOpens s.rep.nonempty_U s.rep.hom r.rep.U
    let hV : (V : Set Y.toVariety.carrier).Nonempty :=
      RatMapRep.compDomain_nonempty r.rep s.rep s.isDominant
    let rU : VarietyHom (X.toVariety.restrict U hU) Y.toVariety :=
      r.rep.hom.comp (X.toVariety.inclHomOfLE
        (fun _ hx => (Variety.mem_preimageOpens.1 hx).1) hU r.rep.nonempty_U)
    let sV : VarietyHom (Y.toVariety.restrict V hV) X.toVariety :=
      s.rep.hom.comp (Y.toVariety.inclHomOfLE
        (fun _ hx => (Variety.mem_preimageOpens.1 hx).1) hV s.rep.nonempty_U)
    have hrU (x : (X.toVariety.restrict U hU).carrier) : rU x ∈ V := by
      have hx := Variety.mem_preimageOpens.1 x.2
      apply Variety.mem_preimageOpens.2
      refine ⟨hx.2 hx.1, fun hy => ?_⟩
      have he := hsr x.1 x.2 trivial
      change s.rep.hom ⟨r.rep.hom ⟨x.1, hx.1⟩, hy⟩ = x.1 at he
      have hz : (⟨rU x, hy⟩ : s.rep.U) =
          ⟨r.rep.hom ⟨x.1, hx.1⟩, hx.2 hx.1⟩ := by
        apply Subtype.ext
        rfl
      have he' : s.rep.hom ⟨rU x, hy⟩ = x.1 := by
        rw [hz]
        exact he
      rw [he']
      exact hx.1
    have hsV (y : (Y.toVariety.restrict V hV).carrier) : sV y ∈ U := by
      have hy := Variety.mem_preimageOpens.1 y.2
      apply Variety.mem_preimageOpens.2
      refine ⟨hy.2 hy.1, fun hx => ?_⟩
      have he := hrs y.1 y.2 trivial
      change r.rep.hom ⟨s.rep.hom ⟨y.1, hy.1⟩, hx⟩ = y.1 at he
      have hz : (⟨sV y, hx⟩ : r.rep.U) =
          ⟨s.rep.hom ⟨y.1, hy.1⟩, hy.2 hy.1⟩ := by
        apply Subtype.ext
        rfl
      have he' : r.rep.hom ⟨sV y, hx⟩ = y.1 := by
        rw [hz]
        exact he
      rw [he']
      exact hy.1
    let f : VarietyHom (X.toVariety.restrict U hU)
        (Y.toVariety.restrict V hV) :=
      VarietyHom.liftToRestrict rU V hV hrU
    let g : VarietyHom (Y.toVariety.restrict V hV)
        (X.toVariety.restrict U hU) :=
      VarietyHom.liftToRestrict sV U hU hsV
    refine ⟨U, hU, V, hV, f, g, ?_, ?_⟩
    · apply VarietyHom.ext
      funext x
      apply Subtype.ext
      exact hsr x.1 x.2 trivial
    · apply VarietyHom.ext
      funext y
      apply Subtype.ext
      exact hrs y.1 y.2 trivial
  · rintro ⟨U, hU, V, hV, f, hf⟩
    have hf0 := hf
    obtain ⟨g, hgf, hfg⟩ := hf
    let rHom : VarietyHom (X.toVariety.restrict U hU) Y.toVariety :=
      (Y.toVariety.inclHom V hV).comp f
    let sHom : VarietyHom (Y.toVariety.restrict V hV) X.toVariety :=
      (X.toVariety.inclHom U hU).comp g
    have hrDense : DenseRange rHom.toFun := by
      change DenseRange ((Y.toVariety.inclHom V hV).toFun ∘ f.toFun)
      exact DenseRange.comp
        (Y.toVariety.dense_range_inclHom_open V hV)
        (VarietyHom.IsIso.bijective hf0).2.denseRange
        (Y.toVariety.inclHom V hV).continuous_toFun
    have hgIso : g.IsIso := ⟨f, hfg, hgf⟩
    have hsDense : DenseRange sHom.toFun := by
      change DenseRange ((X.toVariety.inclHom U hU).toFun ∘ g.toFun)
      exact DenseRange.comp
        (X.toVariety.dense_range_inclHom_open U hU)
        hgIso.bijective.2.denseRange
        (X.toVariety.inclHom U hU).continuous_toFun
    let r : DominantRatMap X.toVariety Y.toVariety Y.isSeparated :=
      Quotient.mk _
        { rep := { U := U, nonempty_U := hU, hom := rHom }
          isDominant := hrDense }
    let s : DominantRatMap Y.toVariety X.toVariety X.isSeparated :=
      Quotient.mk _
        { rep := { U := V, nonempty_U := hV, hom := sHom }
          isDominant := hsDense }
    refine ⟨{ hom := r, inv := s, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
    · apply Quotient.sound
      intro x hx _
      change ((g.comp f) ⟨x, hx.1⟩).1 = x
      have he := congrArg
        (fun q : VarietyHom (X.toVariety.restrict U hU)
          (X.toVariety.restrict U hU) => q ⟨x, hx.1⟩) hgf
      exact congrArg Subtype.val he
    · apply Quotient.sound
      intro y hy _
      change ((f.comp g) ⟨y, hy.1⟩).1 = y
      have he := congrArg
        (fun q : VarietyHom (Y.toVariety.restrict V hV)
          (Y.toVariety.restrict V hV) => q ⟨y, hy.1⟩) hfg
      exact congrArg Subtype.val he

/-- **The function-field form of the birational criterion.**

Separated varieties with affine-open bases are birational exactly when their
function fields are isomorphic as algebras over the ground field. -/
theorem birational_iff_nonempty_functionField_algEquiv [IsAlgClosed k]
    (X Y : SeparatedVariety.{u, u} k)
    (hXaff : X.toVariety.HasAffineOpenBasis)
    (hYaff : Y.toVariety.HasAffineOpenBasis) :
    Birational X Y ↔
      Nonempty (X.toVariety.FunctionField ≃ₐ[k] Y.toVariety.FunctionField) := by
  constructor
  · rintro ⟨e⟩
    let f : X.toVariety.FunctionField →ₐ[k] Y.toVariety.FunctionField :=
      DominantRatMap.functionFieldAlgHom e.inv
    let g : Y.toVariety.FunctionField →ₐ[k] X.toVariety.FunctionField :=
      DominantRatMap.functionFieldAlgHom e.hom
    have hgf : g.comp f = AlgHom.id k X.toVariety.FunctionField := by
      rw [← DominantRatMap.functionFieldAlgHom_comp]
      change DominantRatMap.functionFieldAlgHom (e.hom ≫ e.inv) = _
      rw [e.hom_inv_id]
      exact DominantRatMap.functionFieldAlgHom_id _ _
    have hfg : f.comp g = AlgHom.id k Y.toVariety.FunctionField := by
      rw [← DominantRatMap.functionFieldAlgHom_comp]
      change DominantRatMap.functionFieldAlgHom (e.inv ≫ e.hom) = _
      rw [e.inv_hom_id]
      exact DominantRatMap.functionFieldAlgHom_id _ _
    refine ⟨AlgEquiv.ofBijective f ⟨?_, ?_⟩⟩
    · intro a b hab
      have h := congrArg g hab
      calc
        a = g (f a) := (AlgHom.congr_fun hgf a).symm
        _ = g (f b) := h
        _ = b := AlgHom.congr_fun hgf b
    · intro b
      refine ⟨g b, ?_⟩
      exact AlgHom.congr_fun hfg b
  · rintro ⟨e⟩
    let toY :=
      RationalMapFunctionField.dominantRatMapEquivFunctionFieldAlgHom
        (X := X.toVariety) (Y := Y.toVariety) Y.isSeparated hYaff
    let toX :=
      RationalMapFunctionField.dominantRatMapEquivFunctionFieldAlgHom
        (X := Y.toVariety) (Y := X.toVariety) X.isSeparated hXaff
    let endX :=
      RationalMapFunctionField.dominantRatMapEquivFunctionFieldAlgHom
        (X := X.toVariety) (Y := X.toVariety) X.isSeparated hXaff
    let endY :=
      RationalMapFunctionField.dominantRatMapEquivFunctionFieldAlgHom
        (X := Y.toVariety) (Y := Y.toVariety) Y.isSeparated hYaff
    let f : X ⟶ Y := toY.symm e.symm.toAlgHom
    let g : Y ⟶ X := toX.symm e.toAlgHom
    have hf : DominantRatMap.functionFieldAlgHom f = e.symm.toAlgHom :=
      toY.apply_symm_apply e.symm.toAlgHom
    have hg : DominantRatMap.functionFieldAlgHom g = e.toAlgHom :=
      toX.apply_symm_apply e.toAlgHom
    refine ⟨⟨f, g, ?_, ?_⟩⟩
    · change DominantRatMap.comp g f =
        DominantRatMap.id X.toVariety X.isSeparated
      apply endX.injective
      change DominantRatMap.functionFieldAlgHom
        (DominantRatMap.comp g f) =
          DominantRatMap.functionFieldAlgHom
            (DominantRatMap.id X.toVariety X.isSeparated)
      rw [DominantRatMap.functionFieldAlgHom_comp, hf, hg,
        DominantRatMap.functionFieldAlgHom_id]
      ext a
      exact e.symm_apply_apply a
    · change DominantRatMap.comp f g =
        DominantRatMap.id Y.toVariety Y.isSeparated
      apply endY.injective
      change DominantRatMap.functionFieldAlgHom
        (DominantRatMap.comp f g) =
          DominantRatMap.functionFieldAlgHom
            (DominantRatMap.id Y.toVariety Y.isSeparated)
      rw [DominantRatMap.functionFieldAlgHom_comp, hg, hf,
        DominantRatMap.functionFieldAlgHom_id]
      ext a
      exact e.apply_symm_apply a

/-- Nonempty open subvarieties are isomorphic exactly when the corresponding
function fields are isomorphic over the ground field. -/
theorem hasIsomorphicOpenSubsets_iff_nonempty_functionField_algEquiv
    [IsAlgClosed k] (X Y : SeparatedVariety.{u, u} k)
    (hXaff : X.toVariety.HasAffineOpenBasis)
    (hYaff : Y.toVariety.HasAffineOpenBasis) :
    X.toVariety.HasIsomorphicOpenSubsets Y.toVariety ↔
      Nonempty (X.toVariety.FunctionField ≃ₐ[k] Y.toVariety.FunctionField) :=
  (birational_iff_hasIsomorphicOpenSubsets X Y).symm.trans
    (birational_iff_nonempty_functionField_algEquiv X Y hXaff hYaff)

/-- **Hartshorne I.4, Corollary 4.5.**

Birationality, the existence of isomorphic nonempty open subvarieties, and
isomorphism of function fields are equivalent. -/
theorem birational_criterion [IsAlgClosed k]
    (X Y : SeparatedVariety.{u, u} k)
    (hXaff : X.toVariety.HasAffineOpenBasis)
    (hYaff : Y.toVariety.HasAffineOpenBasis) :
    (Birational X Y ↔
      X.toVariety.HasIsomorphicOpenSubsets Y.toVariety) ∧
    (X.toVariety.HasIsomorphicOpenSubsets Y.toVariety ↔
      Nonempty (X.toVariety.FunctionField ≃ₐ[k] Y.toVariety.FunctionField)) :=
  ⟨birational_iff_hasIsomorphicOpenSubsets X Y,
    hasIsomorphicOpenSubsets_iff_nonempty_functionField_algEquiv
      X Y hXaff hYaff⟩

end Hartshorne
