/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.TangentVectorsDualNumbers
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Infinitesimal deformations over the dual numbers

Hartshorne, *Algebraic Geometry*, III.9, Example 9.13.1 (p. 265).
-/

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

private lemma localAlgHom_ext
    {B : Type u} [CommRing B] [IsLocalRing B] [Algebra k B]
    (φ ψ : B →ₐ[k] k) [IsLocalHom φ] [IsLocalHom ψ] : φ = ψ := by
  apply AlgHom.ext
  intro b
  let b₀ := b - algebraMap k B (ψ b)
  have hψsurj : Function.Surjective ψ := fun r ↦ ⟨algebraMap k B r, by simp⟩
  have hφsurj : Function.Surjective φ := fun r ↦ ⟨algebraMap k B r, by simp⟩
  have hb₀ψ : b₀ ∈ RingHom.ker ψ.toRingHom := by
    rw [RingHom.mem_ker]
    simp [b₀]
  have hb₀φmem : b₀ ∈ RingHom.ker φ.toRingHom := by
    rw [IsLocalRing.ker_eq_maximalIdeal φ.toRingHom hφsurj,
      ← IsLocalRing.ker_eq_maximalIdeal ψ.toRingHom hψsurj]
    exact hb₀ψ
  have hb₀φ : φ b₀ = 0 := by rwa [← RingHom.mem_ker]
  have : φ b - ψ b = 0 := by simpa [b₀] using hb₀φ
  exact sub_eq_zero.mp this

set_option backward.isDefEq.respectTransparency false in
private lemma rationalPointResidueAlgHom_congr
    {T : Over (Spec (CommRingCat.of k))} (g h : basePointOver k ⟶ T)
    (e : rationalPointHom g (baseClosedPoint k) =
      rationalPointHom h (baseClosedPoint k)) :
    letI : Algebra k (RationalPointStalk T g) := rationalPointStalkAlgebra T g
    (rationalPointResidueAlgHom T g).toRingHom =
      ((T.left.presheaf.stalkCongr (.of_eq e)).hom ≫
        Scheme.stalkClosedPointTo (rationalPointHom h)).hom := by
  let _ : Algebra k (RationalPointStalk T g) := rationalPointStalkAlgebra T g
  let ψ : RationalPointStalk T g →ₐ[k] k :=
    { toRingHom := ((T.left.presheaf.stalkCongr (.of_eq e)).hom ≫
        Scheme.stalkClosedPointTo (rationalPointHom h)).hom
      commutes' := fun r ↦ by
        let α : CommRingCat.of k ⟶ RationalPointStalk T g :=
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ T.hom.appTop ≫
            T.left.presheaf.germ ⊤ _ trivial
        change (α ≫ (T.left.presheaf.stalkCongr (.of_eq e)).hom ≫
          Scheme.stalkClosedPointTo (rationalPointHom h)) r = r
        change (α ≫ (T.left.presheaf.stalkCongr (.of_eq e)).hom ≫
          Scheme.stalkClosedPointTo (rationalPointHom h)) r =
            (𝟙 (CommRingCat.of k)) r
        apply ConcreteCategory.congr_hom
        dsimp only [α]
        simp only [Category.assoc, TopCat.Presheaf.stalkCongr_hom,
          TopCat.Presheaf.germ_stalkSpecializes_assoc]
        rw [Scheme.germ_stalkClosedPointTo]
        have hh : rationalPointHom h ≫ T.hom = 𝟙 (Spec (CommRingCat.of k)) := h.w
        simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]
        rw [← Scheme.Hom.comp_appTop_assoc, hh]
        simp }
  have hleft : IsLocalHom (rationalPointResidueAlgHom T g) := by
    let hr : IsLocalHom (Scheme.stalkClosedPointTo (rationalPointHom g)).hom :=
      Scheme.isLocalHom_stalkClosedPointTo _
    exact ⟨fun a ha ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _
      (Scheme.stalkClosedPointTo (rationalPointHom g)).hom hr a ha⟩
  let _ : IsLocalHom (rationalPointResidueAlgHom T g) := hleft
  have hright : IsLocalHom ψ := by
    let es := T.left.presheaf.stalkCongr (.of_eq e)
    let he : IsLocalHom es.hom.hom := IsLocalHom.of_surjective es.hom.hom
      (ConcreteCategory.bijective_of_isIso es.hom).2
    let hr : IsLocalHom (Scheme.stalkClosedPointTo (rationalPointHom h)).hom :=
      Scheme.isLocalHom_stalkClosedPointTo _
    refine ⟨fun a ha ↦ ?_⟩
    exact @IsLocalHom.map_nonunit _ _ _ _ _ _ es.hom.hom he a
      (@IsLocalHom.map_nonunit _ _ _ _ _ _
        (Scheme.stalkClosedPointTo (rationalPointHom h)).hom hr (es.hom a) ha)
  let _ : IsLocalHom ψ := hright
  exact congr_arg AlgHom.toRingHom (localAlgHom_ext (rationalPointResidueAlgHom T g) ψ)

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a dual-number-valued point to the closed point recovers its marked rational
point. -/
theorem dualNumberClosedPoint_comp
    {T : Over (Spec (CommRingCat.of k))} {t : basePointOver k ⟶ T}
    (v : DualNumberLift T t) :
    dualNumberClosedPoint k ≫ v.1 = t := by
  let _ : IsLocalHom (TrivSqZeroExt.fstHom k k k).toRingHom :=
    (TrivSqZeroExt.fst_surjective (R := k) (M := k)).isLocalHom
  ext
  apply (AlgebraicGeometry.SpecToEquivOfLocalRing T.left (CommRingCat.of k)).injective
  rw [AlgebraicGeometry.SpecToEquivOfLocalRing_eq_iff]
  let e :
      ((AlgebraicGeometry.SpecToEquivOfLocalRing T.left (CommRingCat.of k))
          (dualNumberClosedPoint k ≫ v.1).left).1 =
        ((AlgebraicGeometry.SpecToEquivOfLocalRing T.left (CommRingCat.of k)) t.left).1 := by
    change (dualNumberClosedPoint k ≫ v.1).left
      (IsLocalRing.closedPoint (CommRingCat.of k)) =
        t.left (IsLocalRing.closedPoint (CommRingCat.of k))
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    change dualNumberPointHom v.1
      ((dualNumberClosedPoint k).left (baseClosedPoint k)) =
        rationalPointHom t (baseClosedPoint k)
    rw [show (dualNumberClosedPoint k).left (baseClosedPoint k) =
      dualNumberClosedPointCarrier k by
        change (Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.fstHom k k k).toRingHom)) (baseClosedPoint k) =
            dualNumberClosedPointCarrier k
        rw [Spec_closedPoint]]
    exact v.2
  refine ⟨e, ?_⟩
  apply CommRingCat.hom_ext
  exact rationalPointResidueAlgHom_congr (dualNumberClosedPoint k ≫ v.1) t e

/-- An infinitesimal deformation of `X` over the dual numbers: a flat `k[ε]`-scheme together
with a chosen identification of its closed fibre with `X`. -/
structure InfinitesimalDeformation (X : Over (Spec (CommRingCat.of k))) where
  total : Over (dualNumberOver k).left
  flat : Flat total.hom
  closedFiberIso :
    Over.mk (pullback.snd total.hom (dualNumberClosedPoint k).left) ≅ X

attribute [instance] InfinitesimalDeformation.flat

/-- Pulling a family first to the dual numbers and then to their closed point gives the original
fibre over the marked rational point. -/
noncomputable def closedFiberBaseChangeIso
    {T : Over (Spec (CommRingCat.of k))} (W : Over T.left)
    (t : basePointOver k ⟶ T) (v : DualNumberLift T t) :
    Over.mk (pullback.snd
      (pullback.snd W.hom (dualNumberPointHom v.1))
      (dualNumberClosedPoint k).left) ≅
      Over.mk (pullback.snd W.hom (rationalPointHom t)) := by
  have h : (dualNumberClosedPoint k).left ≫ dualNumberPointHom v.1 =
      rationalPointHom t := by
    simpa only [Over.comp_left] using congr_arg Over.Hom.left (dualNumberClosedPoint_comp v)
  let e : pullback (pullback.snd W.hom (dualNumberPointHom v.1))
        (dualNumberClosedPoint k).left ≅
      pullback W.hom (rationalPointHom t) :=
    pullbackLeftPullbackSndIso W.hom (dualNumberPointHom v.1)
        (dualNumberClosedPoint k).left ≪≫
      pullback.congrHom rfl h
  exact Over.isoMk e (by
    change e.hom ≫ pullback.snd W.hom (rationalPointHom t) =
      pullback.snd (pullback.snd W.hom (dualNumberPointHom v.1))
        (dualNumberClosedPoint k).left
    dsimp only [e, Iso.trans_hom, pullback.congrHom, asIso_hom, pullback.map]
    rw [Category.assoc, pullback.lift_snd, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_snd])

namespace InfinitesimalDeformation

/-- A literal dual-number lift of a marked point in a flat family induces an infinitesimal
deformation of the marked fibre. -/
noncomputable def ofFamilyLift
    {X T : Over (Spec (CommRingCat.of k))} (W : Over T.left) [Flat W.hom]
    (t : basePointOver k ⟶ T) (v : DualNumberLift T t)
    (mark : Over.mk (pullback.snd W.hom (rationalPointHom t)) ≅ X) :
    InfinitesimalDeformation X where
  total := Over.mk (pullback.snd W.hom (dualNumberPointHom v.1))
  flat := by
    change Flat (pullback.snd W.hom (dualNumberPointHom v.1))
    infer_instance
  closedFiberIso := closedFiberBaseChangeIso W t v ≪≫ mark

/-- A tangent vector to the base of a marked flat family induces an infinitesimal deformation of
the marked fibre. -/
noncomputable def ofFamilyTangent
    {X T : Over (Spec (CommRingCat.of k))} (W : Over T.left) [Flat W.hom]
    (t : basePointOver k ⟶ T) (τ : RationalPointTangentSpace T t)
    (mark : Over.mk (pullback.snd W.hom (rationalPointHom t)) ≅ X) :
    InfinitesimalDeformation X :=
  ofFamilyLift W t ((dualNumberLiftEquivTangentSpace T t).symm τ) mark

end InfinitesimalDeformation

end Hartshorne
