/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjTwistCompatibility

/-!
# The graded global-sections module `Γ_*(F)`

Hartshorne, *Algebraic Geometry*, II.5, the definition before Proposition 5.13 (p. 118).

Let `S` be an `ℕ`-graded ring, `X = Proj S`, and `F` an `𝒪_X`-module. Hartshorne defines
`Γ_*(F) = ⨁_{n ∈ ℤ} Γ(X, F(n))`, a graded `S`-module, where
`F(n) = F ⊗ 𝒪_X(n)`: a homogeneous `s ∈ S_d` determines a global section of `𝒪_X(d)`, and
multiplication by it is `F(n) ⊗ 𝒪_X(d) → F(n + d)`.

## Main definitions and results

* `GradedGlobalSections.twistSection`, `twistHom`: the section `s / 1` of `𝒪_X(d)` for `s ∈ S_d`,
  and the morphism `𝒪_X ⟶ 𝒪_X(d)`, `1 ↦ s / 1`.
* `GradedGlobalSections.twistMulHom_tmul_twistSection_apply`: under the multiplication
  `𝒪_X(n) ⊗ 𝒪_X(e) → 𝒪_X(n + e)` (`twistMulHom`), multiplying by `t / 1` multiplies values by
  `t`; in particular `s / 1 · t / 1 = st / 1`.
* `GradedGlobalSections.mulMap`: multiplication by `s ∈ S_d` as a morphism `F(n) ⟶ F(n + d)`, with
  `mulMap_add`, `mulMap_mul` (`μ_s ≫ μ_t = μ_{st}` up to `n + d + e = n + (d + e)`) and
  `mulMap_one`.
* `GradedGlobalSections.GammaStar`: `Γ_*(F) = ⨁_{n ∈ ℤ} Γ(X, F(n))`.
* `GradedGlobalSections.gammaStarModule`: the `S`-module structure, and `smul_of`: `s ∈ S_d` maps
  `Γ(X, F(n))` to `Γ(X, F(n + d))` by `mulMap`.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory MonoidalCategory HomogeneousLocalization TopologicalSpace
  Opposite

namespace GradedGlobalSections

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

open ProjGradedModuleSheaf

omit [GradedRing 𝒜] in
theorem mem_gradedTwist_zero {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    s ∈ gradedTwist 𝒜 (d : ℤ) ((0 : ℕ) : ℤ) :=
  (mem_gradedTwist_of_eq (k := d) (by omega)).2 hs

/-- The fraction `s / 1` in `S(d)_(x)` of an element `s ∈ S_d = S(d)_0`. -/
def twistFraction (d : ℕ) (x : ProjectiveSpectrum 𝒜) {s : A} (hs : s ∈ 𝒜 d) :
    HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 d) x.asHomogeneousIdeal.toIdeal.primeCompl :=
  HomogeneousLocalizedModule.mk 0 s (mem_gradedTwist_zero hs) 1 SetLike.GradedOne.one_mem
    x.asHomogeneousIdeal.toIdeal.primeCompl.one_mem

theorem twistFraction_val (d : ℕ) (x : ProjectiveSpectrum 𝒜) {s : A} (hs : s ∈ 𝒜 d) :
    (twistFraction d x hs).val = LocalizedModule.mk s 1 := rfl

/-- The section `x ↦ s / 1` of `𝒪_X(d)` over an open `U`, for `s ∈ S_d`. -/
def twistSection (d : ℕ) (s : 𝒜 d) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (projTwistingSheaf 𝒜 d).val.obj U :=
  (⟨fun y => twistFraction d y.1 s.2, fun y =>
    ⟨U.unop, y.2, 𝟙 _, 0, s, mem_gradedTwist_zero s.2, 1, SetLike.GradedOne.one_mem,
      fun z => z.1.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, fun _ => rfl⟩⟩ :
    (sheafInType 𝒜 (gradedTwist 𝒜 d)).1.obj U)

@[simp]
theorem twistSection_apply (d : ℕ) (s : 𝒜 d) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (x : U.unop) :
    ((twistSection d s U : (sheafInType 𝒜 (gradedTwist 𝒜 d)).1.obj U).1 x) =
      twistFraction d x.1 s.2 := rfl

/-- The sections `s / 1` of `𝒪_X(d)` form a compatible family. -/
def twistSections (d : ℕ) (s : 𝒜 d) : (projTwistingSheaf 𝒜 d).sections :=
  ⟨fun U => twistSection d s U, fun _ => rfl⟩

/-- The morphism `𝒪_X ⟶ 𝒪_X(d)`, `1 ↦ s / 1`, of a degree-`d` element `s`. -/
def twistHom (d : ℕ) (s : 𝒜 d) : 𝟙_ (Proj 𝒜).Modules ⟶ projTwistingSheaf 𝒜 d :=
  (projTwistingSheaf 𝒜 d).unitHomEquiv.symm (twistSections d s)

/-- The section `1` of the unit `𝒪_X`. -/
def oneSec (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : (𝟙_ (Proj 𝒜).Modules).val.obj U :=
  (1 : (Proj 𝒜).ringCatSheaf.obj.obj U)

theorem twistHom_app_one (d : ℕ) (s : 𝒜 d) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (twistHom d s).val.app U (oneSec U) = twistSection d s U := by
  have := SheafOfModules.unitHomEquiv_apply_coe (projTwistingSheaf 𝒜 d) (twistHom d s) U
  rw [twistHom, Equiv.apply_symm_apply] at this
  exact this.symm


section Mul

open Ringed

/-- Multiplying a section of `𝒪_X(n)` by `s / 1`, `s ∈ S_e`: on values, multiplication by `s`. -/
theorem twistMulHom_tmul_twistSection_apply (n : ℤ) (e : ℕ) (t : 𝒜 e)
    {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (g : (projTwistingSheaf 𝒜 n).val.obj U)
    (x : U.unop) :
    ((((twistMulHom 𝒜 n e).val.app U (tmulSection _ _ g (twistSection e t U)) :
        (projTwistingSheaf 𝒜 (n + e)).val.obj U) :
      (sheafInType 𝒜 (gradedTwist 𝒜 (n + e))).1.obj U).1 x).val =
      (t : A) • ((g : (sheafInType 𝒜 (gradedTwist 𝒜 n)).1.obj U).1 x).val := by
  rw [twistMulHom_tmulSection, twistSection_apply, twistFraction_val]
  change (Localization.mk (t : A) 1 : Localization _) • _ = _
  rw [Localization.mk_one_eq_algebraMap, algebraMap_smul]

end Mul

section MulMap

open Ringed

variable (F : (Proj 𝒜).Modules)

/-- `(ρ_ G).inv` sends `x` to `x ⊗ 1`. -/
theorem rightUnitor_inv_app (G : (Proj 𝒜).Modules) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (x : G.val.obj U) :
    (ρ_ G).inv.val.app U x = tmulSection G (𝟙_ (Proj 𝒜).Modules) x (oneSec U) := by
  have h : (ρ_ G).hom.val.app U (tmulSection G (𝟙_ (Proj 𝒜).Modules) x (oneSec U)) = x := by
    refine (rightUnitor_hom_tmulSection G (U := U) _ x).trans ?_
    exact one_smul ((Proj 𝒜).ringCatSheaf.obj.obj U) x
  conv_lhs => rw [← h]
  change ((ρ_ G).hom ≫ (ρ_ G).inv).val.app U _ = _
  rw [Iso.hom_inv_id]
  rfl

/-- **Multiplication by `s ∈ S_d`** on the twists of `F`: the composite
`F(n) ≅ F(n) ⊗ 𝒪_X ⟶ F(n) ⊗ 𝒪_X(d) ≅ F ⊗ (𝒪_X(n) ⊗ 𝒪_X(d)) ⟶ F(n + d)`, where
`F(n) = F ⊗ 𝒪_X(n)` and the middle map is `1 ↦ s / 1`. -/
def mulMap (n : ℤ) (d : ℕ) (s : 𝒜 d) :
    F ⊗ projTwistingSheaf 𝒜 n ⟶ F ⊗ projTwistingSheaf 𝒜 (n + d) :=
  (ρ_ _).inv ≫ ((F ⊗ projTwistingSheaf 𝒜 n) ◁ twistHom d s) ≫ (α_ _ _ _).hom ≫
    (F ◁ twistMulHom 𝒜 n d)

theorem mulMap_tmulSection (n : ℤ) (d : ℕ) (s : 𝒜 d)
    {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (f : F.val.obj U)
    (g : (projTwistingSheaf 𝒜 n).val.obj U) :
    (mulMap F n d s).val.app U (tmulSection _ _ f g) =
      tmulSection _ _ f ((twistMulHom 𝒜 n d).val.app U
        (tmulSection _ _ g (twistSection d s U))) := by
  change (F ◁ twistMulHom 𝒜 n d).val.app U
    ((α_ F (projTwistingSheaf 𝒜 n) (projTwistingSheaf 𝒜 d)).hom.val.app U
    (((F ⊗ projTwistingSheaf 𝒜 n) ◁ twistHom d s).val.app U
      ((ρ_ (F ⊗ projTwistingSheaf 𝒜 n)).inv.val.app U (tmulSection _ _ f g)))) = _
  rw [rightUnitor_inv_app, scheme_whiskerLeft_tmulSection, twistHom_app_one,
    scheme_associator_hom_tmulSection, scheme_whiskerLeft_tmulSection]

/-- `eqToHom` between twists of `F` acts on `f ⊗ g` through the second factor. -/
theorem eqToHom_tmulSection {a b : ℤ} (h : a = b) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (f : F.val.obj U) (g : (projTwistingSheaf 𝒜 a).val.obj U) :
    (eqToHom (congrArg (fun m => F ⊗ projTwistingSheaf 𝒜 m) h)).val.app U
        (tmulSection _ _ f g) =
      tmulSection _ _ f ((eqToHom (congrArg (projTwistingSheaf 𝒜) h)).val.app U g) := by
  subst h
  simp only [eqToHom_refl]
  rfl

/-- `eqToHom` between twisting sheaves does not change values. -/
theorem eqToHom_apply_val {a b : ℤ} (h : a = b) {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (g : (projTwistingSheaf 𝒜 a).val.obj U) (x : U.unop) :
    ((((eqToHom (congrArg (projTwistingSheaf 𝒜) h)).val.app U g :
        (projTwistingSheaf 𝒜 b).val.obj U) :
      (sheafInType 𝒜 (gradedTwist 𝒜 b)).1.obj U).1 x).val =
      ((g : (sheafInType 𝒜 (gradedTwist 𝒜 a)).1.obj U).1 x).val := by
  subst h
  simp only [eqToHom_refl]
  rfl

theorem mulMap_add (n : ℤ) (d : ℕ) (s s' : 𝒜 d) :
    mulMap F n d (s + s') = mulMap F n d s + mulMap F n d s' := by
  apply tensor_hom_ext
  intro U f g
  have hs : twistSection d (s + s') U = twistSection d s U + twistSection d s' U := by
    apply section_ext
    intro x
    apply HomogeneousLocalizedModule.ext
    change LocalizedModule.mk ((s : A) + s') 1 =
      LocalizedModule.mk (s : A) 1 + LocalizedModule.mk (s' : A) 1
    rw [LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]
  have key := fun t => mulMap_tmulSection F n d t f g
  calc _ = tmulSection _ _ f ((twistMulHom 𝒜 n d).val.app U
        (tmulSection _ _ g (twistSection d (s + s') U))) := key _
    _ = tmulSection _ _ f ((twistMulHom 𝒜 n d).val.app U
          (tmulSection _ _ g (twistSection d s U))) +
        tmulSection _ _ f ((twistMulHom 𝒜 n d).val.app U
          (tmulSection _ _ g (twistSection d s' U))) := by
      rw [hs, tmulSection_add_right, map_add, tmulSection_add_right]
    _ = (mulMap F n d s).val.app U (tmulSection _ _ f g) +
        (mulMap F n d s').val.app U (tmulSection _ _ f g) := by
      rw [key, key]
    _ = _ := rfl

-- The kernel check unfolds the generic and scheme monoidal instances against each other.
set_option maxHeartbeats 1000000 in
theorem mulMap_mul (n : ℤ) (d e : ℕ) (s : 𝒜 d) (t : 𝒜 e) :
    mulMap F n d s ≫ mulMap F (n + d) e t =
      mulMap F n (d + e) ⟨s * t, SetLike.GradedMul.mul_mem s.2 t.2⟩ ≫
        eqToHom (congrArg (fun m => F ⊗ projTwistingSheaf 𝒜 m)
          (show n + ((d + e : ℕ) : ℤ) = n + d + e by push_cast; ring)) := by
  have h : n + ((d + e : ℕ) : ℤ) = n + d + e := by push_cast; ring
  apply tensor_hom_ext
  intro U f g
  calc _ = (mulMap F (n + d) e t).val.app U ((mulMap F n d s).val.app U
        (tmulSection _ _ f g)) := rfl
    _ = (mulMap F (n + d) e t).val.app U (tmulSection _ _ f
          ((twistMulHom 𝒜 n d).val.app U (tmulSection _ _ g (twistSection d s U)))) :=
        congrArg _ (mulMap_tmulSection F n d s f g)
    _ = tmulSection _ _ f ((twistMulHom 𝒜 (n + d) e).val.app U (tmulSection _ _
          ((twistMulHom 𝒜 n d).val.app U (tmulSection _ _ g (twistSection d s U)))
          (twistSection e t U))) := mulMap_tmulSection F (n + d) e t f _
    _ = tmulSection _ _ f ((eqToHom (congrArg (projTwistingSheaf 𝒜) h)).val.app U
          ((twistMulHom 𝒜 n (d + e : ℕ)).val.app U (tmulSection _ _ g
            (twistSection (d + e) ⟨(s : A) * t, SetLike.GradedMul.mul_mem s.2 t.2⟩ U)))) := by
      refine congrArg (tmulSection _ _ f) ?_
      apply section_ext
      intro x
      apply HomogeneousLocalizedModule.ext
      rw [twistMulHom_tmul_twistSection_apply, eqToHom_apply_val h,
        twistMulHom_tmul_twistSection_apply, twistMulHom_tmul_twistSection_apply]
      change _ = ((s : A) * t) • _
      rw [mul_comm, mul_smul]
    _ = (eqToHom (congrArg (fun m => F ⊗ projTwistingSheaf 𝒜 m) h)).val.app U
          (tmulSection _ _ f ((twistMulHom 𝒜 n (d + e : ℕ)).val.app U (tmulSection _ _ g
            (twistSection (d + e) ⟨(s : A) * t, SetLike.GradedMul.mul_mem s.2 t.2⟩ U)))) :=
        (eqToHom_tmulSection F h f _).symm
    _ = (eqToHom (congrArg (fun m => F ⊗ projTwistingSheaf 𝒜 m) h)).val.app U
          ((mulMap F n (d + e) ⟨(s : A) * t, SetLike.GradedMul.mul_mem s.2 t.2⟩).val.app U
            (tmulSection _ _ f g)) :=
        congrArg _ (mulMap_tmulSection F n (d + e) _ f g).symm
    _ = _ := rfl

-- The kernel check unfolds the generic and scheme monoidal instances against each other.
set_option maxHeartbeats 1000000 in
theorem mulMap_one (n : ℤ) :
    mulMap F n 0 ⟨1, SetLike.GradedOne.one_mem⟩ =
      eqToHom (congrArg (fun m => F ⊗ projTwistingSheaf 𝒜 m)
        (show n = n + ((0 : ℕ) : ℤ) by push_cast; ring)) := by
  have h : n = n + ((0 : ℕ) : ℤ) := by push_cast; ring
  apply tensor_hom_ext
  intro U f g
  calc _ = tmulSection _ _ f ((twistMulHom 𝒜 n (0 : ℕ)).val.app U
        (tmulSection _ _ g (twistSection 0 ⟨1, SetLike.GradedOne.one_mem⟩ U))) :=
      mulMap_tmulSection F n 0 _ f g
    _ = tmulSection _ _ f ((eqToHom (congrArg (projTwistingSheaf 𝒜) h)).val.app U g) := by
      refine congrArg (tmulSection _ _ f) ?_
      apply section_ext
      intro x
      apply HomogeneousLocalizedModule.ext
      rw [twistMulHom_tmul_twistSection_apply, eqToHom_apply_val h]
      exact one_smul _ _
    _ = _ := (eqToHom_tmulSection F h f g).symm

end MulMap

section Graded

variable (F : (Proj 𝒜).Modules)

/-- The global sections `Γ(X, F(n))` of the `n`-th twist `F(n) = F ⊗ 𝒪_X(n)`. -/
abbrev twistGlobal (n : ℤ) : Type u := (F ⊗ projTwistingSheaf 𝒜 n).val.obj (op ⊤)

/-- **Hartshorne's `Γ_*(F) = ⨁_{n ∈ ℤ} Γ(X, F(n))`.** -/
abbrev GammaStar : Type u := DirectSum ℤ fun n => twistGlobal F n

/-- Multiplication by `s ∈ S_d` on global sections, `Γ(X, F(n)) → Γ(X, F(n + d))`. -/
def mulGlobal (n : ℤ) (d : ℕ) (s : 𝒜 d) : twistGlobal F n →+ twistGlobal F (n + d) :=
  ((mulMap F n d s).val.app (op ⊤)).hom.toAddMonoidHom

theorem mulMap_zero (n : ℤ) (d : ℕ) : mulMap F n d 0 = 0 := by
  have h := mulMap_add F n d 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

/-- Multiplication by `s ∈ S_d` on `Γ_*(F)`, shifting degrees by `d`. -/
def mulStar (d : ℕ) (s : 𝒜 d) : GammaStar F →+ GammaStar F :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun m => twistGlobal F m) (n + d)).comp (mulGlobal F n d s)

theorem mulStar_of (d : ℕ) (s : 𝒜 d) (n : ℤ) (x : twistGlobal F n) :
    mulStar F d s (DirectSum.of (fun m => twistGlobal F m) n x) =
      DirectSum.of (fun m => twistGlobal F m) (n + d) (mulGlobal F n d s x) :=
  DirectSum.toAddMonoid_of _ _ _

theorem of_eqToHom {a b : ℤ} (h : a = b) (x : twistGlobal F a) :
    DirectSum.of (fun m => twistGlobal F m) b
        ((eqToHom (congrArg (fun m => F ⊗ projTwistingSheaf 𝒜 m) h)).val.app (op ⊤) x) =
      DirectSum.of (fun m => twistGlobal F m) a x := by
  subst h
  rfl

theorem of_mulGlobal_congr (n : ℤ) {d d' : ℕ} (h : d = d') (s : 𝒜 d) (s' : 𝒜 d')
    (hs : (s : A) = s') (x : twistGlobal F n) :
    DirectSum.of (fun m => twistGlobal F m) (n + d) (mulGlobal F n d s x) =
      DirectSum.of (fun m => twistGlobal F m) (n + d') (mulGlobal F n d' s' x) := by
  subst h
  obtain rfl : s = s' := Subtype.ext hs
  rfl

/-- `s ↦` multiplication by `s`, for `s ∈ S_d`. -/
def mulStarHom (d : ℕ) : 𝒜 d →+ AddMonoid.End (GammaStar F) where
  toFun s := mulStar F d s
  map_zero' := DirectSum.addHom_ext fun n x => by
    change mulStar F d 0 (DirectSum.of (fun m => twistGlobal F m) n x) = 0
    rw [mulStar_of]
    change DirectSum.of (fun m => twistGlobal F m) _ ((mulMap F n d 0).val.app (op ⊤) x) = 0
    rw [mulMap_zero]
    exact map_zero _
  map_add' s s' := DirectSum.addHom_ext fun n x => by
    change mulStar F d (s + s') (DirectSum.of (fun m => twistGlobal F m) n x) =
      mulStar F d s (DirectSum.of (fun m => twistGlobal F m) n x) +
        mulStar F d s' (DirectSum.of (fun m => twistGlobal F m) n x)
    rw [mulStar_of, mulStar_of, mulStar_of, ← map_add]
    congr 1
    change (mulMap F n d (s + s')).val.app (op ⊤) x = _
    rw [mulMap_add]
    rfl

/-- The action of `S` on `Γ_*(F)`, additive in the ring element. -/
def actHom : A →+ AddMonoid.End (GammaStar F) :=
  (DirectSum.toAddMonoid fun d => mulStarHom F d).comp
    (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

theorem actHom_of_mem {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    actHom F s = mulStar F d ⟨s, hs⟩ := by
  change DirectSum.toAddMonoid (fun d => mulStarHom F d) (DirectSum.decompose 𝒜 s) = _
  rw [DirectSum.decompose_of_mem 𝒜 hs, DirectSum.toAddMonoid_of]
  rfl

theorem actHom_one : actHom F 1 = 1 := by
  rw [actHom_of_mem F SetLike.GradedOne.one_mem]
  refine DirectSum.addHom_ext fun n x => ?_
  have h : n = n + ((0 : ℕ) : ℤ) := by push_cast; ring
  calc mulStar F 0 ⟨1, SetLike.GradedOne.one_mem⟩ (DirectSum.of (fun m => twistGlobal F m) n x)
      = DirectSum.of (fun m => twistGlobal F m) (n + ((0 : ℕ) : ℤ))
          ((mulMap F n 0 ⟨1, SetLike.GradedOne.one_mem⟩).val.app (op ⊤) x) :=
        mulStar_of F 0 _ n x
    _ = DirectSum.of (fun m => twistGlobal F m) (n + ((0 : ℕ) : ℤ))
          ((eqToHom (congrArg (fun m => F ⊗ projTwistingSheaf 𝒜 m) h)).val.app (op ⊤) x) := by
        rw [mulMap_one]
    _ = DirectSum.of (fun m => twistGlobal F m) n x := of_eqToHom F h x
    _ = _ := rfl

-- The kernel check unfolds the generic and scheme monoidal instances against each other.
set_option maxHeartbeats 1000000 in
-- Elaborating the `calc` steps up to defeq needs deep unfolding.
set_option maxRecDepth 10000 in
theorem actHom_mul_of_mem {i j : ℕ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    actHom F (a * b) = actHom F a * actHom F b := by
  rw [actHom_of_mem F (SetLike.GradedMul.mul_mem ha hb), actHom_of_mem F ha,
    actHom_of_mem F hb]
  refine DirectSum.addHom_ext fun n x => ?_
  have h2 : DirectSum.of (fun m => twistGlobal F m) (n + j + i)
      ((mulMap F (n + j) i ⟨a, ha⟩).val.app (op ⊤)
        ((mulMap F n j ⟨b, hb⟩).val.app (op ⊤) x)) =
      DirectSum.of (fun m => twistGlobal F m) (n + ((j + i : ℕ) : ℤ))
        ((mulMap F n (j + i) ⟨b * a, SetLike.GradedMul.mul_mem hb ha⟩).val.app (op ⊤) x) :=
    (congrArg (fun φ => DirectSum.of (fun m => twistGlobal F m) (n + j + i) (φ.val.app (op ⊤) x))
      (mulMap_mul F n j i ⟨b, hb⟩ ⟨a, ha⟩)).trans
      (of_eqToHom F (show n + ((j + i : ℕ) : ℤ) = n + j + i by push_cast; ring) _)
  calc mulStar F (i + j) ⟨a * b, SetLike.GradedMul.mul_mem ha hb⟩
        (DirectSum.of (fun m => twistGlobal F m) n x)
      = DirectSum.of (fun m => twistGlobal F m) (n + ((i + j : ℕ) : ℤ))
          (mulGlobal F n (i + j) ⟨a * b, SetLike.GradedMul.mul_mem ha hb⟩ x) :=
        mulStar_of F _ _ n x
    _ = DirectSum.of (fun m => twistGlobal F m) (n + ((j + i : ℕ) : ℤ))
          (mulGlobal F n (j + i) ⟨b * a, SetLike.GradedMul.mul_mem hb ha⟩ x) :=
        of_mulGlobal_congr F n (add_comm i j) _ _ (mul_comm a b) x
    _ = DirectSum.of (fun m => twistGlobal F m) (n + j + i)
          ((mulMap F (n + j) i ⟨a, ha⟩).val.app (op ⊤)
            ((mulMap F n j ⟨b, hb⟩).val.app (op ⊤) x)) := h2.symm
    _ = mulStar F i ⟨a, ha⟩ (DirectSum.of (fun m => twistGlobal F m) (n + j)
          (mulGlobal F n j ⟨b, hb⟩ x)) := (mulStar_of F i _ (n + j) _).symm
    _ = mulStar F i ⟨a, ha⟩ (mulStar F j ⟨b, hb⟩
          (DirectSum.of (fun m => twistGlobal F m) n x)) :=
        congrArg _ (mulStar_of F j _ n x).symm
    _ = _ := rfl

/-- The action of `S` on `Γ_*(F)`, as a ring homomorphism to additive endomorphisms. -/
def actRingHom : A →+* AddMonoid.End (GammaStar F) where
  toFun := actHom F
  map_one' := actHom_one F
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' a b := by
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add a a' ha ha' => rw [add_mul, map_add, map_add, ha, ha', add_mul]
    | homogeneous a =>
      induction b using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | add b b' hb hb' => rw [mul_add, map_add, map_add, hb, hb', mul_add]
      | homogeneous b => exact actHom_mul_of_mem F a.2 b.2

/-- **`Γ_*(F)` as an `S`-module** (Hartshorne II.5, p.118): `s ∈ S_d` acts on `Γ(X, F(n))` through
the section `s / 1` of `𝒪_X(d)` and `F(n) ⊗ 𝒪_X(d) → F(n + d)`. -/
abbrev gammaStarModule : Module A (GammaStar F) :=
  Module.compHom (GammaStar F) (actRingHom F)

/-- The grading: `s ∈ S_d` sends `Γ(X, F(n))` to `Γ(X, F(n + d))`. -/
theorem smul_of {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (n : ℤ) (x : twistGlobal F n) :
    letI := gammaStarModule F
    s • DirectSum.of (fun m => twistGlobal F m) n x =
      DirectSum.of (fun m => twistGlobal F m) (n + d) (mulGlobal F n d ⟨s, hs⟩ x) := by
  change actHom F s (DirectSum.of (fun m => twistGlobal F m) n x) = _
  rw [actHom_of_mem F hs]
  exact mulStar_of F d _ n x

end Graded

end GradedGlobalSections

end Hartshorne
