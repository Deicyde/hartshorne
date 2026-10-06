/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.TangentDualNumbersAlgebra
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Tangent vectors and the dual numbers

Hartshorne, *Algebraic Geometry*, II, Exercise 2.8 (p. 80).
-/

open CategoryTheory

namespace Hartshorne

open AlgebraicGeometry IsLocalRing TrivSqZeroExt

universe u

variable (k : Type u) [Field k]

/-- The base point `Spec k` as a `k`-scheme. -/
noncomputable abbrev basePointOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (𝟙 (Spec (CommRingCat.of k)))

/-- The spectrum of the dual numbers as a `k`-scheme. -/
noncomputable abbrev dualNumberOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- The unique point of `Spec k`. -/
noncomputable abbrev baseClosedPoint : (Spec (CommRingCat.of k) : Type u) :=
  closedPoint (CommRingCat.of k)

/-- The closed point of the spectrum of the dual numbers. -/
noncomputable abbrev dualNumberClosedPointCarrier :
    (Spec (CommRingCat.of (DualNumber k)) : Type u) :=
  closedPoint (CommRingCat.of (DualNumber k))

private instance dualNumberFst_isLocalHom :
    IsLocalHom (fstHom k k k).toRingHom :=
  (TrivSqZeroExt.fst_surjective (R := k) (M := k)).isLocalHom

/-- The closed-point inclusion `Spec k → Spec k[ε]`, as a morphism of `k`-schemes. -/
noncomputable def dualNumberClosedPoint : basePointOver k ⟶ dualNumberOver k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (fstHom k k k).toRingHom)) (by
    dsimp [basePointOver, dualNumberOver]
    rw [← Spec.map_comp, ← Spec.map_id]
    rw [Spec.map_inj]
    ext r
    rfl)

variable {k}

/-- The underlying scheme morphism of a rational point. -/
noncomputable abbrev rationalPointHom
    {X : Over (Spec (CommRingCat.of k))} (x : basePointOver k ⟶ X) :
    Spec (CommRingCat.of k) ⟶ X.left :=
  x.left

/-- The underlying scheme morphism of a dual-number-valued point. -/
noncomputable abbrev dualNumberPointHom
    {X : Over (Spec (CommRingCat.of k))} (f : dualNumberOver k ⟶ X) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ X.left :=
  f.left

/-- Dual-number-valued `k`-points whose closed point is the chosen rational point. -/
def DualNumberLift (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :=
  { f : dualNumberOver k ⟶ X //
    dualNumberPointHom f (dualNumberClosedPointCarrier k) =
      rationalPointHom x (baseClosedPoint k) }

/-- The local ring at the point underlying a chosen `k`-rational point. -/
noncomputable abbrev RationalPointStalk
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :=
  X.left.presheaf.stalk (rationalPointHom x (baseClosedPoint k))

private lemma rationalPoint_mapsToClosedPoint
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    X.hom (rationalPointHom x (baseClosedPoint k)) = baseClosedPoint k := by
  have hx : rationalPointHom x ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)) := x.w
  rw [← Scheme.Hom.comp_apply, hx]
  rfl

/-- The `k`-algebra structure on the stalk induced by the structure morphism of `X`. -/
@[instance_reducible]
noncomputable def rationalPointStalkAlgebra
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    Algebra k (RationalPointStalk X x) := by
  let y := rationalPointHom x (baseClosedPoint k)
  let α : CommRingCat.of k ⟶ X.left.presheaf.stalk y :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.germ ⊤ y trivial
  exact α.hom.toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The local residue map associated to a rational point, bundled as a `k`-algebra map. -/
noncomputable def rationalPointResidueAlgHom
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
    RationalPointStalk X x →ₐ[k] k := by
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  refine
    { toRingHom := (Scheme.stalkClosedPointTo (rationalPointHom x)).hom
      commutes' := fun r ↦ ?_ }
  let y := rationalPointHom x (baseClosedPoint k)
  let α : CommRingCat.of k ⟶ X.left.presheaf.stalk y :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.germ ⊤ y trivial
  change (α ≫ Scheme.stalkClosedPointTo (rationalPointHom x)) r = r
  change (α ≫ Scheme.stalkClosedPointTo (rationalPointHom x)) r =
    (𝟙 (CommRingCat.of k)) r
  apply ConcreteCategory.congr_hom
  dsimp only [α, y, baseClosedPoint]
  rw [Category.assoc, Category.assoc, Scheme.germ_stalkClosedPointTo]
  have hx : rationalPointHom x ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)) := x.w
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc]
  rw [← Scheme.Hom.comp_appTop_assoc, hx]
  simp

/-- The Zariski tangent space `Hom_k(𝔪_x / 𝔪_x², k)` at a rational point. -/
noncomputable def RationalPointTangentSpace
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) : Type u :=
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  CotangentSpace (RationalPointStalk X x) →ₗ[k] k

private lemma localAlgHom_ext
    {B : Type u} [CommRing B] [IsLocalRing B] [Algebra k B]
    (φ ψ : B →ₐ[k] k) [IsLocalHom φ] [IsLocalHom ψ] : φ = ψ := by
  apply AlgHom.ext
  intro b
  let b₀ := b - algebraMap k B (ψ b)
  have hψsurj : Function.Surjective ψ := fun r ↦
    ⟨algebraMap k B r, by simp⟩
  have hφsurj : Function.Surjective φ := fun r ↦
    ⟨algebraMap k B r, by simp⟩
  have hb₀ψ : b₀ ∈ RingHom.ker ψ.toRingHom := by
    rw [RingHom.mem_ker]
    simp [b₀]
  have hkerψ : RingHom.ker ψ.toRingHom = maximalIdeal B :=
    IsLocalRing.ker_eq_maximalIdeal ψ.toRingHom hψsurj
  have hkerφ : RingHom.ker φ.toRingHom = maximalIdeal B :=
    IsLocalRing.ker_eq_maximalIdeal φ.toRingHom hφsurj
  have hb₀φmem : b₀ ∈ RingHom.ker φ.toRingHom := by
    rw [hkerφ, ← hkerψ]
    exact hb₀ψ
  have hb₀φ : φ b₀ = 0 := by
    rw [← RingHom.mem_ker]
    exact hb₀φmem
  have : φ b - ψ b = 0 := by simpa [b₀] using hb₀φ
  exact sub_eq_zero.mp this

set_option backward.isDefEq.respectTransparency false in
private noncomputable def localLiftOfDualNumberLift
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X)
    (f : DualNumberLift X x) :
    letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
    DualNumberLocalLift (rationalPointResidueAlgHom X x) := by
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  let y₀ := rationalPointHom x (baseClosedPoint k)
  let yε := dualNumberPointHom f.1 (dualNumberClosedPointCarrier k)
  let e : yε = y₀ := f.2
  let ψ : X.left.presheaf.stalk y₀ ⟶ CommRingCat.of (DualNumber k) :=
    (X.left.presheaf.stalkCongr (.of_eq e.symm)).hom ≫
      Scheme.stalkClosedPointTo (dualNumberPointHom f.1)
  let φ : RationalPointStalk X x →ₐ[k] DualNumber k :=
    { toRingHom := ψ.hom
      commutes' := fun r ↦ by
        let α : CommRingCat.of k ⟶ X.left.presheaf.stalk y₀ :=
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫
            X.left.presheaf.germ ⊤ y₀ trivial
        change (α ≫ ψ) r = (CommRingCat.ofHom (algebraMap k (DualNumber k))) r
        apply ConcreteCategory.congr_hom
        dsimp only [α, ψ, y₀, yε, e, baseClosedPoint, dualNumberClosedPointCarrier]
        simp only [Category.assoc, TopCat.Presheaf.stalkCongr_hom,
          TopCat.Presheaf.germ_stalkSpecializes_assoc]
        rw [Scheme.germ_stalkClosedPointTo]
        simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc]
        rw [← Scheme.Hom.comp_appTop_assoc, f.1.w]
        simp [dualNumberOver, Scheme.ΓSpecIso_naturality] }
  have hψ : IsLocalHom ψ.hom := by
    let eStalk := X.left.presheaf.stalkCongr (.of_eq e.symm)
    let he : IsLocalHom eStalk.hom.hom :=
      IsLocalHom.of_surjective eStalk.hom.hom
        (ConcreteCategory.bijective_of_isIso eStalk.hom).2
    let hr : IsLocalHom (Scheme.stalkClosedPointTo (dualNumberPointHom f.1)).hom :=
      Scheme.isLocalHom_stalkClosedPointTo _
    refine ⟨fun a ha ↦ ?_⟩
    exact @IsLocalHom.map_nonunit _ _ _ _ _ _ eStalk.hom.hom he a
      (@IsLocalHom.map_nonunit _ _ _ _ _ _
        (Scheme.stalkClosedPointTo (dualNumberPointHom f.1)).hom hr (eStalk.hom a) ha)
  let _ : IsLocalHom ψ.hom := hψ
  have hφ : IsLocalHom φ := by
    exact ⟨fun a ha ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _ ψ.hom hψ a ha⟩
  let _ : IsLocalHom φ := hφ
  refine ⟨φ, ?_⟩
  let χ : RationalPointStalk X x →ₐ[k] k := (fstHom k k k).comp φ
  have hχ : IsLocalHom χ := by
    let hfst : IsLocalHom (fstHom k k k) :=
      ⟨fun a ha ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _
        (fstHom k k k).toRingHom (dualNumberFst_isLocalHom k) a ha⟩
    exact ⟨fun a ha ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _ φ hφ a
      (@IsLocalHom.map_nonunit _ _ _ _ _ _ (fstHom k k k) hfst
        (φ a) ha)⟩
  let _ : IsLocalHom χ := hχ
  have hρ : IsLocalHom (rationalPointResidueAlgHom X x) := by
    let hr : IsLocalHom (Scheme.stalkClosedPointTo (rationalPointHom x)).hom :=
      Scheme.isLocalHom_stalkClosedPointTo _
    exact ⟨fun a ha ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _
      (Scheme.stalkClosedPointTo (rationalPointHom x)).hom hr a ha⟩
  let _ : IsLocalHom (rationalPointResidueAlgHom X x) := hρ
  exact localAlgHom_ext χ (rationalPointResidueAlgHom X x)

set_option backward.isDefEq.respectTransparency false in
private lemma localLiftToScheme_isOver
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X)
    (φ : letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
      DualNumberLocalLift (rationalPointResidueAlgHom X x)) :
    letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
    Spec.map (CommRingCat.ofHom φ.1.toRingHom) ≫
        X.left.fromSpecStalk (rationalPointHom x (baseClosedPoint k)) ≫ X.hom =
      (dualNumberOver k).hom := by
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  let y := rationalPointHom x (baseClosedPoint k)
  let φCat : X.left.presheaf.stalk y ⟶ CommRingCat.of (DualNumber k) :=
    ConcreteCategory.ofHom φ.1.toRingHom
  let α : CommRingCat.of k ⟶ X.left.presheaf.stalk y :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.germ ⊤ y trivial
  let β : CommRingCat.of k ⟶ CommRingCat.of (DualNumber k) :=
    CommRingCat.ofHom (algebraMap k (DualNumber k))
  change Spec.map φCat ≫ X.left.fromSpecStalk y ≫ X.hom = Spec.map β
  apply AlgebraicGeometry.ext_to_Spec
  rw [Scheme.Γ_map_op, Scheme.Γ_map_op]
  simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.fromSpecStalk_appTop]
  rw [show (Spec (X.left.presheaf.stalk y)).presheaf.map (homOfLE le_top).op = 𝟙 _ by
    rw [show (homOfLE le_top : (⊤ : (Spec (X.left.presheaf.stalk y)).Opens) ⟶ ⊤).op =
      𝟙 _ from Subsingleton.elim _ _]
    simpa]
  simp only [Category.id_comp, Category.comp_id]
  slice_lhs 4 5 =>
    rw [← Scheme.ΓSpecIso_inv_naturality φCat]
  slice_rhs 1 2 =>
    rw [← Scheme.ΓSpecIso_inv_naturality β]
  change (α ≫ φCat) ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv =
    β ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv
  rw [cancel_mono]
  change α ≫ φCat = β
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change φ.1 (algebraMap k (RationalPointStalk X x) r) =
    algebraMap k (DualNumber k) r
  exact φ.1.commutes r

set_option backward.isDefEq.respectTransparency false in
private noncomputable def dualNumberLiftOfLocalLift
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X)
    (φ : letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
      DualNumberLocalLift (rationalPointResidueAlgHom X x)) : DualNumberLift X x := by
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  let ρ := rationalPointResidueAlgHom X x
  have hρ : IsLocalHom ρ := by
    let hr : IsLocalHom (Scheme.stalkClosedPointTo (rationalPointHom x)).hom :=
      Scheme.isLocalHom_stalkClosedPointTo _
    exact ⟨fun a ha ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _
      (Scheme.stalkClosedPointTo (rationalPointHom x)).hom hr a ha⟩
  let _ : IsLocalHom ρ := hρ
  have hφ : IsLocalHom φ.1 := by
    refine ⟨fun a ha ↦ ?_⟩
    apply @IsLocalHom.map_nonunit _ _ _ _ _ _ ρ hρ a
    have hu : IsUnit ((fstHom k k k) (φ.1 a)) :=
      IsUnit.map (fstHom k k k) ha
    have hred := DFunLike.congr_fun φ.2 a
    change fst (φ.1 a) = ρ a at hred
    rw [← hred]
    exact hu
  let _ : IsLocalHom φ.1 := hφ
  let y := rationalPointHom x (baseClosedPoint k)
  let φCat : X.left.presheaf.stalk y ⟶ CommRingCat.of (DualNumber k) :=
    ConcreteCategory.ofHom φ.1.toRingHom
  have hφring : IsLocalHom φCat.hom :=
    ⟨fun a ha ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _ φ.1 hφ a ha⟩
  let _ : IsLocalHom φCat.hom := hφring
  let g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left :=
    Spec.map φCat ≫ X.left.fromSpecStalk y
  let F : dualNumberOver k ⟶ X :=
    Over.homMk g (localLiftToScheme_isOver X x φ)
  refine ⟨F, ?_⟩
  change g (dualNumberClosedPointCarrier k) = rationalPointHom x (baseClosedPoint k)
  change X.left.fromSpecStalk y
      (Spec.map φCat (dualNumberClosedPointCarrier k)) = y
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

set_option backward.isDefEq.respectTransparency false in
private lemma localLiftOfDualNumberLift_dualNumberLiftOfLocalLift
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X)
    (φ : letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
      DualNumberLocalLift (rationalPointResidueAlgHom X x)) :
    localLiftOfDualNumberLift X x (dualNumberLiftOfLocalLift X x φ) = φ := by
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  apply Subtype.ext
  apply AlgHom.ext
  intro a
  dsimp only [localLiftOfDualNumberLift, dualNumberLiftOfLocalLift]
  let y := rationalPointHom x (baseClosedPoint k)
  let φCat : X.left.presheaf.stalk y ⟶ CommRingCat.of (DualNumber k) :=
    ConcreteCategory.ofHom φ.1.toRingHom
  let ρ := rationalPointResidueAlgHom X x
  have hρ : IsLocalHom ρ := by
    let hr : IsLocalHom (Scheme.stalkClosedPointTo (rationalPointHom x)).hom :=
      Scheme.isLocalHom_stalkClosedPointTo _
    exact ⟨fun b hb ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _
      (Scheme.stalkClosedPointTo (rationalPointHom x)).hom hr b hb⟩
  let _ : IsLocalHom ρ := hρ
  have hφ : IsLocalHom φ.1 := by
    refine ⟨fun b hb ↦ ?_⟩
    apply @IsLocalHom.map_nonunit _ _ _ _ _ _ ρ hρ b
    have hu : IsUnit ((fstHom k k k) (φ.1 b)) :=
      IsUnit.map (fstHom k k k) hb
    have hred := DFunLike.congr_fun φ.2 b
    change fst (φ.1 b) = ρ b at hred
    rw [← hred]
    exact hu
  let _ : IsLocalHom φCat.hom :=
    ⟨fun b hb ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _ φ.1 hφ b hb⟩
  let g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left :=
    Spec.map φCat ≫ X.left.fromSpecStalk y
  let e : g (dualNumberClosedPointCarrier k) = y := by
    change X.left.fromSpecStalk y
        (Spec.map φCat (dualNumberClosedPointCarrier k)) = y
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  change Scheme.stalkClosedPointTo g
      ((X.left.presheaf.stalkCongr (.of_eq e.symm)).hom a) = φ.1 a
  have hmap :
      (X.left.presheaf.stalkCongr (.of_eq e.symm)).hom ≫
          Scheme.stalkClosedPointTo g = φCat := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
    simp only [g, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.germ_stalkSpecializes_assoc,
      Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk]
  exact ConcreteCategory.congr_hom hmap a

set_option backward.isDefEq.respectTransparency false in
private lemma dualNumberLiftOfLocalLift_localLiftOfDualNumberLift
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X)
    (f : DualNumberLift X x) :
    dualNumberLiftOfLocalLift X x (localLiftOfDualNumberLift X x f) = f := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  let y₀ := rationalPointHom x (baseClosedPoint k)
  let yε := dualNumberPointHom f.1 (dualNumberClosedPointCarrier k)
  let e : yε = y₀ := f.2
  let ψ : X.left.presheaf.stalk y₀ ⟶ CommRingCat.of (DualNumber k) :=
    (X.left.presheaf.stalkCongr (.of_eq e.symm)).hom ≫
      Scheme.stalkClosedPointTo (dualNumberPointHom f.1)
  have hψ : IsLocalHom ψ.hom := by
    let eStalk := X.left.presheaf.stalkCongr (.of_eq e.symm)
    let he : IsLocalHom eStalk.hom.hom :=
      IsLocalHom.of_surjective eStalk.hom.hom
        (ConcreteCategory.bijective_of_isIso eStalk.hom).2
    let hr : IsLocalHom (Scheme.stalkClosedPointTo (dualNumberPointHom f.1)).hom :=
      Scheme.isLocalHom_stalkClosedPointTo _
    refine ⟨fun a ha ↦ ?_⟩
    exact @IsLocalHom.map_nonunit _ _ _ _ _ _ eStalk.hom.hom he a
      (@IsLocalHom.map_nonunit _ _ _ _ _ _
        (Scheme.stalkClosedPointTo (dualNumberPointHom f.1)).hom hr (eStalk.hom a) ha)
  let E := AlgebraicGeometry.SpecToEquivOfLocalRing X.left
    (CommRingCat.of (DualNumber k))
  let P : Σ z, { η : X.left.presheaf.stalk z ⟶ CommRingCat.of (DualNumber k) //
      IsLocalHom η.hom } := ⟨y₀, ψ, hψ⟩
  have hP : P = E (dualNumberPointHom f.1) := by
    apply AlgebraicGeometry.SpecToEquivOfLocalRing_eq_iff.mpr
    refine ⟨e.symm, ?_⟩
    dsimp only [P, E, ψ, y₀, yε, e]
    congr
  change Spec.map ψ ≫ X.left.fromSpecStalk y₀ = dualNumberPointHom f.1
  change E.symm P = dualNumberPointHom f.1
  rw [hP, E.symm_apply_apply]

/-- Dual-number-valued points through `x` are equivalent to local lifts of the residue map. -/
noncomputable def dualNumberLiftEquivLocalLift
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
    DualNumberLift X x ≃ DualNumberLocalLift (rationalPointResidueAlgHom X x) := by
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  exact
    { toFun := localLiftOfDualNumberLift X x
      invFun := dualNumberLiftOfLocalLift X x
      left_inv := dualNumberLiftOfLocalLift_localLiftOfDualNumberLift X x
      right_inv := localLiftOfDualNumberLift_dualNumberLiftOfLocalLift X x }

/-- The canonical equivalence between dual-number-valued points through `x` and the Zariski
tangent space at `x`. -/
noncomputable def dualNumberLiftEquivTangentSpace
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    DualNumberLift X x ≃ RationalPointTangentSpace X x := by
  letI : Algebra k (RationalPointStalk X x) := rationalPointStalkAlgebra X x
  let ρ := rationalPointResidueAlgHom X x
  have hρ : IsLocalHom ρ := by
    let hr : IsLocalHom (Scheme.stalkClosedPointTo (rationalPointHom x)).hom :=
      Scheme.isLocalHom_stalkClosedPointTo _
    exact ⟨fun a ha ↦ @IsLocalHom.map_nonunit _ _ _ _ _ _
      (Scheme.stalkClosedPointTo (rationalPointHom x)).hom hr a ha⟩
  let _ : IsLocalHom ρ := hρ
  exact (dualNumberLiftEquivLocalLift X x).trans
    (dualNumberLocalLiftEquivCotangentDual ρ)

/-- The canonical map sending a dual-number-valued point through `x` to its tangent vector. -/
noncomputable def dualNumberLiftToTangent
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    DualNumberLift X x → RationalPointTangentSpace X x :=
  dualNumberLiftEquivTangentSpace X x

/-- Dual-number-valued points through a rational point are in bijection with its Zariski tangent
space. -/
theorem dualNumberLiftToTangent_bijective
    (X : Over (Spec (CommRingCat.of k))) (x : basePointOver k ⟶ X) :
    Function.Bijective (dualNumberLiftToTangent X x) :=
  (dualNumberLiftEquivTangentSpace X x).bijective

end Hartshorne
