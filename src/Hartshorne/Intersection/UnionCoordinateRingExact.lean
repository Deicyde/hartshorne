/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.GradedSubquotient
import Hartshorne.Projective.Correspondence
import Hartshorne.Projective.QuotientGrading

/-!
# The coordinate-ring exact sequence for a union

Hartshorne, *Algebraic Geometry*, I.7, proof of Proposition 7.6(b)
(p. 52).

For two homogeneous ideals `I₁` and `I₂`, the canonical sequence

`0 → S/(I₁ ∩ I₂) → S/I₁ × S/I₂ → S/(I₁ + I₂) → 0`

is exact degree by degree.  The first map is the pair of quotient-factor maps
and the second sends `(x, y)` to `x - y`.

## Main result

* `Hartshorne.unionCoordinateRing_exact`
-/

namespace Hartshorne

open DirectSum MvPolynomial

noncomputable section

universe u

variable {k : Type u} [Field k] {σ : Type*}

private abbrev Poly := MvPolynomial σ k

private abbrev intGrading : ℤ → Submodule k (Poly (k := k) (σ := σ)) :=
  integerHomogeneousSubmodule k σ

private theorem toIdeal_inf_le_left
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) :
    (I₁ ⊓ I₂).toIdeal ≤ I₁.toIdeal := by
  rw [HomogeneousIdeal.toIdeal_inf]
  exact inf_le_left

private theorem toIdeal_inf_le_right
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) :
    (I₁ ⊓ I₂).toIdeal ≤ I₂.toIdeal := by
  rw [HomogeneousIdeal.toIdeal_inf]
  exact inf_le_right

private theorem toIdeal_le_sup_left
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) :
    I₁.toIdeal ≤ (I₁ ⊔ I₂).toIdeal := by
  rw [HomogeneousIdeal.toIdeal_sup]
  exact le_sup_left

private theorem toIdeal_le_sup_right
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) :
    I₂.toIdeal ≤ (I₁ ⊔ I₂).toIdeal := by
  rw [HomogeneousIdeal.toIdeal_sup]
  exact le_sup_right

/-- The canonical map from the quotient by an intersection to the product of
the two quotients. -/
def unionCoordinateToPieces
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) :
    (Poly (k := k) (σ := σ) ⧸ (I₁ ⊓ I₂).toIdeal) →ₗ[Poly (k := k) (σ := σ)]
      (Poly (k := k) (σ := σ) ⧸ I₁.toIdeal) ×
        (Poly (k := k) (σ := σ) ⧸ I₂.toIdeal) :=
  LinearMap.prod
    (Ideal.Quotient.factorₐ (Poly (k := k) (σ := σ))
      (toIdeal_inf_le_left I₁ I₂)).toLinearMap
    (Ideal.Quotient.factorₐ (Poly (k := k) (σ := σ))
      (toIdeal_inf_le_right I₁ I₂)).toLinearMap

/-- The difference map from the product of the two quotients to the quotient
by their sum. -/
def unionPiecesToIntersection
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) :
    ((Poly (k := k) (σ := σ) ⧸ I₁.toIdeal) ×
        (Poly (k := k) (σ := σ) ⧸ I₂.toIdeal)) →ₗ[Poly (k := k) (σ := σ)]
      Poly (k := k) (σ := σ) ⧸ (I₁ ⊔ I₂).toIdeal :=
  (Ideal.Quotient.factorₐ (Poly (k := k) (σ := σ))
      (toIdeal_le_sup_left I₁ I₂)).toLinearMap.comp
      (LinearMap.fst (Poly (k := k) (σ := σ)) _ _) -
    (Ideal.Quotient.factorₐ (Poly (k := k) (σ := σ))
      (toIdeal_le_sup_right I₁ I₂)).toLinearMap.comp
      (LinearMap.snd (Poly (k := k) (σ := σ)) _ _)

/-- The degree-`d` piece of the middle term `S/I₁ × S/I₂`. -/
def unionCoordinateMiddleGrading
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) (d : ℤ) :
    Submodule k
      ((Poly (k := k) (σ := σ) ⧸ I₁.toIdeal) ×
        (Poly (k := k) (σ := σ) ⧸ I₂.toIdeal)) :=
  (quotGrading (intGrading (k := k) (σ := σ)) I₁ d).prod
    (quotGrading (intGrading (k := k) (σ := σ)) I₂ d)

private def unionCoordinateMiddleFst
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) (d : ℤ) :
    unionCoordinateMiddleGrading I₁ I₂ d →+
      quotGrading (intGrading (k := k) (σ := σ)) I₁ d where
  toFun x := ⟨x.1.1, x.2.1⟩
  map_zero' := by ext; rfl
  map_add' x y := by ext; rfl

private def unionCoordinateMiddleSnd
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) (d : ℤ) :
    unionCoordinateMiddleGrading I₁ I₂ d →+
      quotGrading (intGrading (k := k) (σ := σ)) I₂ d where
  toFun x := ⟨x.1.2, x.2.2⟩
  map_zero' := by ext; rfl
  map_add' x y := by ext; rfl

private theorem coe_map_unionCoordinateMiddleFst
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ)))
    (z : ⨁ d, unionCoordinateMiddleGrading I₁ I₂ d) :
    DirectSum.coeAddMonoidHom
        (quotGrading (intGrading (k := k) (σ := σ)) I₁)
        (DirectSum.map (unionCoordinateMiddleFst I₁ I₂) z) =
      (DirectSum.coeAddMonoidHom (unionCoordinateMiddleGrading I₁ I₂) z).1 := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | of d x => simp [DirectSum.coeAddMonoidHom_of, unionCoordinateMiddleFst]

private theorem coe_map_unionCoordinateMiddleSnd
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ)))
    (z : ⨁ d, unionCoordinateMiddleGrading I₁ I₂ d) :
    DirectSum.coeAddMonoidHom
        (quotGrading (intGrading (k := k) (σ := σ)) I₂)
        (DirectSum.map (unionCoordinateMiddleSnd I₁ I₂) z) =
      (DirectSum.coeAddMonoidHom (unionCoordinateMiddleGrading I₁ I₂) z).2 := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | of d x => simp [DirectSum.coeAddMonoidHom_of, unionCoordinateMiddleSnd]

private theorem unionCoordinateMiddleGrading_isInternal
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) :
    DirectSum.IsInternal (unionCoordinateMiddleGrading I₁ I₂) := by
  classical
  constructor
  · intro x y hxy
    have hfst :
        DirectSum.map (unionCoordinateMiddleFst I₁ I₂) x =
          DirectSum.map (unionCoordinateMiddleFst I₁ I₂) y := by
      apply (DirectSum.Decomposition.isInternal
        (ℳ := quotGrading (intGrading (k := k) (σ := σ)) I₁)).injective
      rw [coe_map_unionCoordinateMiddleFst,
        coe_map_unionCoordinateMiddleFst, hxy]
    have hsnd :
        DirectSum.map (unionCoordinateMiddleSnd I₁ I₂) x =
          DirectSum.map (unionCoordinateMiddleSnd I₁ I₂) y := by
      apply (DirectSum.Decomposition.isInternal
        (ℳ := quotGrading (intGrading (k := k) (σ := σ)) I₂)).injective
      rw [coe_map_unionCoordinateMiddleSnd,
        coe_map_unionCoordinateMiddleSnd, hxy]
    apply DFinsupp.ext
    intro d
    have hfd := DFunLike.congr_fun hfst d
    have hsd := DFunLike.congr_fun hsnd d
    rw [DirectSum.map_apply, DirectSum.map_apply] at hfd hsd
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val hfd
    · exact congrArg Subtype.val hsd
  · rintro ⟨x, y⟩
    let vx := DirectSum.decompose
      (quotGrading (intGrading (k := k) (σ := σ)) I₁) x
    let vy := DirectSum.decompose
      (quotGrading (intGrading (k := k) (σ := σ)) I₂) y
    let z : ⨁ d, unionCoordinateMiddleGrading I₁ I₂ d :=
      DFinsupp.mk (vx.support ∪ vy.support) fun d =>
        ⟨((vx d : _) , (vy d : _)), ⟨(vx d).property, (vy d).property⟩⟩
    have hzx : DirectSum.map (unionCoordinateMiddleFst I₁ I₂) z = vx := by
      apply DFinsupp.ext
      intro d
      rw [DirectSum.map_apply, DFinsupp.mk_apply]
      split_ifs with hd
      · rfl
      · have hdx : d ∉ vx.support := fun h => hd (Finset.mem_union_left _ h)
        have hzero : vx d = 0 := DFinsupp.notMem_support_iff.1 hdx
        rw [hzero]
        rfl
    have hzy : DirectSum.map (unionCoordinateMiddleSnd I₁ I₂) z = vy := by
      apply DFinsupp.ext
      intro d
      rw [DirectSum.map_apply, DFinsupp.mk_apply]
      split_ifs with hd
      · rfl
      · have hdy : d ∉ vy.support := fun h => hd (Finset.mem_union_right _ h)
        have hzero : vy d = 0 := DFinsupp.notMem_support_iff.1 hdy
        rw [hzero]
        rfl
    refine ⟨z, ?_⟩
    apply Prod.ext
    · rw [← coe_map_unionCoordinateMiddleFst I₁ I₂ z, hzx]
      exact (DirectSum.decompose
        (quotGrading (intGrading (k := k) (σ := σ)) I₁)).symm_apply_apply x
    · rw [← coe_map_unionCoordinateMiddleSnd I₁ I₂ z, hzy]
      exact (DirectSum.decompose
        (quotGrading (intGrading (k := k) (σ := σ)) I₂)).symm_apply_apply y

/-- The product pieces give the direct-sum grading on the middle term. -/
noncomputable instance unionCoordinateMiddleGradingDecomposition
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) :
    DirectSum.Decomposition (unionCoordinateMiddleGrading I₁ I₂) :=
  DirectSum.IsInternal.chooseDecomposition
    (unionCoordinateMiddleGrading I₁ I₂)
    (unionCoordinateMiddleGrading_isInternal I₁ I₂)

/-- The diagonal `S`-action on the middle term respects its product grading. -/
instance unionCoordinateMiddleGradingGradedSMul
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) :
    SetLike.GradedSMul (intGrading (k := k) (σ := σ))
      (unionCoordinateMiddleGrading I₁ I₂) where
  smul_mem {i j a m} ha hm := by
    obtain ⟨b, hb, hbm⟩ := hm.1
    obtain ⟨c, hc, hcm⟩ := hm.2
    constructor
    · refine ⟨a * b, SetLike.mul_mem_graded ha hb, ?_⟩
      change Ideal.Quotient.mk I₁.toIdeal (a * b) = a • m.1
      rw [← hbm]
      exact Submodule.Quotient.mk_smul I₁.toIdeal a b
    · refine ⟨a * c, SetLike.mul_mem_graded ha hc, ?_⟩
      change Ideal.Quotient.mk I₂.toIdeal (a * c) = a • m.2
      rw [← hcm]
      exact Submodule.Quotient.mk_smul I₂.toIdeal a c

/-- The first canonical map restricted to degree `d`. -/
def unionCoordinateToPieces_degree
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) (d : ℤ) :
    quotGrading (intGrading (k := k) (σ := σ)) (I₁ ⊓ I₂) d →ₗ[k]
      unionCoordinateMiddleGrading I₁ I₂ d where
  toFun x := ⟨unionCoordinateToPieces I₁ I₂ x, by
    obtain ⟨a, ha, hax⟩ := x.property
    constructor
    · exact ⟨a, ha, by rw [← hax]; rfl⟩
    · exact ⟨a, ha, by rw [← hax]; rfl⟩⟩
  map_add' x y := by ext <;> simp [unionCoordinateToPieces]
  map_smul' r x := by ext <;> simp [unionCoordinateToPieces]

/-- The difference map restricted to degree `d`. -/
def unionPiecesToIntersection_degree
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) (d : ℤ) :
    unionCoordinateMiddleGrading I₁ I₂ d →ₗ[k]
      quotGrading (intGrading (k := k) (σ := σ)) (I₁ ⊔ I₂) d := by
  let f : unionCoordinateMiddleGrading I₁ I₂ d →ₗ[k]
      Poly (k := k) (σ := σ) ⧸ (I₁ ⊔ I₂).toIdeal :=
    (unionPiecesToIntersection I₁ I₂).restrictScalars k |>.comp
      (unionCoordinateMiddleGrading I₁ I₂ d).subtype
  exact f.codRestrict _ (fun x => by
    obtain ⟨a, ha, hax⟩ := x.property.1
    obtain ⟨b, hb, hbx⟩ := x.property.2
    refine ⟨a - b, (intGrading (k := k) (σ := σ) d).sub_mem ha hb, ?_⟩
    change Ideal.Quotient.mk (I₁ ⊔ I₂).toIdeal (a - b) =
      Ideal.Quotient.factor (toIdeal_le_sup_left I₁ I₂) x.1.1 -
        Ideal.Quotient.factor (toIdeal_le_sup_right I₁ I₂) x.1.2
    rw [← hax, ← hbx]
    rfl)

/-- The coordinate-ring sequence for two homogeneous ideals is short exact in
every degree, with all three terms carrying their induced integer gradings. -/
theorem unionCoordinateRing_exact
    (I₁ I₂ : HomogeneousIdeal (intGrading (k := k) (σ := σ))) (d : ℤ) :
    Function.Injective (unionCoordinateToPieces_degree I₁ I₂ d) ∧
      LinearMap.range (unionCoordinateToPieces_degree I₁ I₂ d) =
        LinearMap.ker (unionPiecesToIntersection_degree I₁ I₂ d) ∧
      Function.Surjective (unionPiecesToIntersection_degree I₁ I₂ d) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨a, ha, hax⟩ := x.property
    obtain ⟨b, hb, hby⟩ := y.property
    have hpair := congrArg Subtype.val hxy
    have hfst := congrArg Prod.fst hpair
    have hsnd := congrArg Prod.snd hpair
    change (unionCoordinateToPieces I₁ I₂ (x : _)).1 =
      (unionCoordinateToPieces I₁ I₂ (y : _)).1 at hfst
    change (unionCoordinateToPieces I₁ I₂ (x : _)).2 =
      (unionCoordinateToPieces I₁ I₂ (y : _)).2 at hsnd
    rw [← hax, ← hby] at hfst hsnd
    change Ideal.Quotient.mk I₁.toIdeal a =
      Ideal.Quotient.mk I₁.toIdeal b at hfst
    change Ideal.Quotient.mk I₂.toIdeal a =
      Ideal.Quotient.mk I₂.toIdeal b at hsnd
    apply Subtype.ext
    rw [← hax, ← hby]
    change Ideal.Quotient.mk (I₁ ⊓ I₂).toIdeal a =
      Ideal.Quotient.mk (I₁ ⊓ I₂).toIdeal b
    rw [Ideal.Quotient.eq, HomogeneousIdeal.toIdeal_inf]
    exact ⟨Ideal.Quotient.eq.1 hfst, Ideal.Quotient.eq.1 hsnd⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      change unionPiecesToIntersection_degree I₁ I₂ d
          (unionCoordinateToPieces_degree I₁ I₂ d y) = 0
      obtain ⟨a, ha, hay⟩ := y.property
      apply Subtype.ext
      change unionPiecesToIntersection I₁ I₂
          (unionCoordinateToPieces I₁ I₂ (y : _)) = 0
      rw [← hay]
      simp [unionCoordinateToPieces, unionPiecesToIntersection]
    · intro hx
      change unionPiecesToIntersection_degree I₁ I₂ d x = 0 at hx
      obtain ⟨a, ha, hax⟩ := x.property.1
      obtain ⟨b, hb, hbx⟩ := x.property.2
      have hxzero := congrArg Subtype.val hx
      change unionPiecesToIntersection I₁ I₂ (x : _) = 0 at hxzero
      change Ideal.Quotient.factor (toIdeal_le_sup_left I₁ I₂) x.1.1 -
        Ideal.Quotient.factor (toIdeal_le_sup_right I₁ I₂) x.1.2 = 0 at hxzero
      rw [← hax, ← hbx] at hxzero
      have hab : a - b ∈ (I₁ ⊔ I₂).toIdeal := by
        apply Ideal.Quotient.eq_zero_iff_mem.1
        simpa using hxzero
      rw [HomogeneousIdeal.toIdeal_sup] at hab
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hab
      let ud : Poly (k := k) (σ := σ) :=
        DirectSum.decompose (intGrading (k := k) (σ := σ)) u d
      let vd : Poly (k := k) (σ := σ) :=
        DirectSum.decompose (intGrading (k := k) (σ := σ)) v d
      have hudG : ud ∈ intGrading (k := k) (σ := σ) d :=
        (DirectSum.decompose (intGrading (k := k) (σ := σ)) u d).property
      have hvdG : vd ∈ intGrading (k := k) (σ := σ) d :=
        (DirectSum.decompose (intGrading (k := k) (σ := σ)) v d).property
      have hudI : ud ∈ I₁.toIdeal := I₁.isHomogeneous d hu
      have hvdI : vd ∈ I₂.toIdeal := I₂.isHomogeneous d hv
      have huv_d : ud + vd = a - b := by
        calc
          ud + vd =
              (DirectSum.decompose (intGrading (k := k) (σ := σ))
                (u + v) d : Poly (k := k) (σ := σ)) := by
                rw [DirectSum.decompose_add]
                rfl
          _ = (DirectSum.decompose (intGrading (k := k) (σ := σ))
                (a - b) d : Poly (k := k) (σ := σ)) := by rw [huv]
          _ = a - b := DirectSum.decompose_of_mem_same _
            ((intGrading (k := k) (σ := σ) d).sub_mem ha hb)
      let z := a - ud
      have hzG : z ∈ intGrading (k := k) (σ := σ) d :=
        (intGrading (k := k) (σ := σ) d).sub_mem ha hudG
      let q : quotGrading (intGrading (k := k) (σ := σ)) (I₁ ⊓ I₂) d :=
        ⟨Ideal.Quotient.mk (I₁ ⊓ I₂).toIdeal z, ⟨z, hzG, rfl⟩⟩
      refine ⟨q, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rw [← hax]
        apply Ideal.Quotient.eq.2
        have : z - a = -ud := by dsimp [z]; abel
        rw [this]
        exact I₁.toIdeal.neg_mem hudI
      · rw [← hbx]
        apply Ideal.Quotient.eq.2
        have : z - b = vd := by
          dsimp [z]
          calc
            a - ud - b = (a - b) - ud := by abel
            _ = (ud + vd) - ud := by rw [huv_d]
            _ = vd := by abel
        rw [this]
        exact hvdI
  · intro y
    obtain ⟨c, hc, hcy⟩ := y.property
    let x : unionCoordinateMiddleGrading I₁ I₂ d :=
      ⟨(Ideal.Quotient.mk I₁.toIdeal c, 0),
        ⟨⟨c, hc, rfl⟩,
          (quotGrading (intGrading (k := k) (σ := σ)) I₂ d).zero_mem⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rw [← hcy]
    simp [x, unionPiecesToIntersection_degree,
      unionPiecesToIntersection]

end

end Hartshorne
