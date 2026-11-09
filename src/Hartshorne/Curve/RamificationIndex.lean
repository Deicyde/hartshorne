/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteCurveDivisorPullback
import Hartshorne.Cohomology.SmoothMorphisms.EtaleCriteria
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# The ramification index of a finite morphism of curves

Hartshorne, *Algebraic Geometry*, IV.2, p. 299.

Let `f : X ⟶ Y` be a finite morphism of nonsingular curves over `k`, let `P ∈ X` and `Q = f(P)`.
For a uniformizer `t` of the discrete valuation ring `𝒪_{Y,Q}`, the ramification index is
`e_P = v_P(f^# t)` (`AlgebraicGeometry.Scheme.IsNonsingularCurve.ramificationIndex`).

* `ramificationIndex_eq`: `e_P` does not depend on `t`.
* `finiteCurvePointPullback_apply_self`: `e_P` is the coefficient of `P` in `f^* Q`.
* `ramificationIndex_eq_ramificationIdx'`: `e_P` is the ideal-theoretic ramification index of
  the local homomorphism `𝒪_{Y,Q} → 𝒪_{X,P}` of discrete valuation rings.
* `ramificationIndex_eq_one_iff`: for a closed point `P` and `k` algebraically closed, `e_P = 1`
  if and only if `f` is unramified at `P` (`Hartshorne.HartshorneUnramifiedAt`).
* `IsTamelyRamifiedAt`, `IsWildlyRamifiedAt`: tame and wild ramification.
-/

open CategoryTheory Limits Order TopologicalSpace IsLocalRing

universe u

namespace Hartshorne

/-- Hartshorne's pointwise unramifiedness at `x`, for `f(x) = y`: `m_y 𝒪_{X,x} = m_x` and
`k(x)/k(y)` is separable algebraic. `Hartshorne.HartshorneUnramified f` is this condition at every
point. -/
def HartshorneUnramifiedAt {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) ∧
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) ∧
      Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)

theorem hartshorneUnramified_iff_forall {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    HartshorneUnramified f ↔ ∀ x, HartshorneUnramifiedAt f x :=
  Iff.rfl

end Hartshorne

namespace AlgebraicGeometry

namespace Scheme.IsNonsingularCurve

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [IsIntegral X] [IsIntegral Y]

/-- The **ramification index** `e_P = v_P(f^# t)` of a finite (more generally, locally
quasi-finite) morphism of curves at `P`, for a uniformizer `t` of `𝒪_{Y, f(P)}`
(Hartshorne IV.2, p. 299). It is `0` at the generic point. -/
noncomputable def ramificationIndex (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [LocallyQuasiFinite f] (P : X) : ℤ :=
  hX.finiteCurvePullbackMultiplicity hY f P

/-- **Independence of the uniformizer.** `e_P = v_P(f^# t)` for every uniformizer `t` of
`𝒪_{Y, f(P)}`. -/
theorem ramificationIndex_eq (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [LocallyQuasiFinite f] {P : X} (hP : coheight P = 1)
    {t : Y.presheaf.stalk (f P)} (ht : Irreducible t) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    hX.ramificationIndex hY f P =
      X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ t)) P :=
  hX.finiteCurvePullbackMultiplicity_eq hY f hP ht

/-- `e_P` is the coefficient of `P` in `f^* f(P)`. -/
theorem finiteCurvePointPullback_apply_self (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] (P : X) :
    (hX.finiteCurvePointPullback hY f (f P)).1 P = hX.ramificationIndex hY f P := by
  classical
  change (if f P = f P then hX.finiteCurvePullbackMultiplicity hY f P else 0) = _
  rw [if_pos rfl]
  rfl

/-- In the stalk at a codimension-one point, `u π^n` has order `n` for a uniformizer `π`. -/
theorem ord_algebraMap_unit_mul_pow (hX : X.IsNonsingularCurve k) {x : X} (hx : coheight x = 1)
    {π : X.presheaf.stalk x} (hπ : Irreducible π) (v : (X.presheaf.stalk x)ˣ) (n : ℕ) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    X.ord (algebraMap _ X.functionField (v * π ^ n)) x = n := by
  intro _
  have hne : algebraMap (X.presheaf.stalk x) X.functionField (v * π ^ n) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]
    exact mul_ne_zero v.ne_zero (pow_ne_zero _ hπ.ne_zero)
  rw [X.ord_eq_iff hx hne, map_mul, map_mul, map_pow, map_pow,
    ordHom_algebraMap_of_isUnit hX hx v.isUnit, ordHom_algebraMap_of_irreducible hX hx hπ, one_mul,
    WithZero.exp, ← WithZero.coe_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]

/-- At a codimension-one point `P`, `m_Q 𝒪_{X,P} = m_P ^ {e_P}`. -/
theorem exists_map_maximalIdeal_eq_pow (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] {P : X}
    (hP : coheight P = 1) :
    ∃ n : ℕ, (n : ℤ) = hX.ramificationIndex hY f P ∧
      (maximalIdeal (Y.presheaf.stalk (f P))).map (f.stalkMap P).hom =
        maximalIdeal (X.presheaf.stalk P) ^ n := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  have hQ := hX.coheight_apply_eq_one hY f hP
  have := X.codimensionOneStalk_isDiscreteValuationRing hX.satisfiesConditionStar hP
  have := Y.codimensionOneStalk_isDiscreteValuationRing hY.satisfiesConditionStar hQ
  set t := hY.localParameter (f P)
  have ht : Irreducible t := hY.irreducible_localParameter hQ
  set π := hX.localParameter P
  have hπ : Irreducible π := hX.irreducible_localParameter hP
  have hφt : (f.stalkMap P).hom t ≠ 0 := by
    intro h0
    have h1 := hX.finiteCurveFunctionFieldMap_algebraMap hY f P t
    rw [h0, map_zero, map_eq_zero_iff _ (hX.finiteCurveFunctionFieldMap hY f).injective,
      map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h1
    exact ht.ne_zero h1
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφt hπ
  refine ⟨n, ?_, ?_⟩
  · rw [hX.ramificationIndex_eq hY f hP ht, hX.finiteCurveFunctionFieldMap_algebraMap, hv,
      hX.ord_algebraMap_unit_mul_pow hP hπ]
  · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.map_span,
      Set.image_singleton, Ideal.span_singleton_pow, hv,
      Ideal.span_singleton_mul_left_unit v.isUnit]

private theorem not_pow_succ_le_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) : ¬ maximalIdeal R ^ n ≤ maximalIdeal R ^ (n + 1) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton, pow_succ]
  intro h
  exact hπ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left
    (pow_ne_zero n hπ.ne_zero)).1 (by simpa using h)))

/-- **The ideal-theoretic ramification index.** At a codimension-one point `P`, `e_P` is the
ramification index of `m_P` over `m_Q` for the local homomorphism `𝒪_{Y,Q} → 𝒪_{X,P}` of discrete
valuation rings. -/
theorem ramificationIndex_eq_ramificationIdx' (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] {P : X}
    (hP : coheight P = 1) :
    letI := (f.stalkMap P).hom.toAlgebra
    hX.ramificationIndex hY f P =
      (Ideal.ramificationIdx' (maximalIdeal (Y.presheaf.stalk (f P)))
        (maximalIdeal (X.presheaf.stalk P)) : ℤ) := by
  let _ := (f.stalkMap P).hom.toAlgebra
  let _ := hX.satisfiesConditionStar.isNoetherian
  have := X.codimensionOneStalk_isDiscreteValuationRing hX.satisfiesConditionStar hP
  obtain ⟨n, hn, hmap⟩ := hX.exists_map_maximalIdeal_eq_pow hY f hP
  have hmap' : (maximalIdeal (Y.presheaf.stalk (f P))).map
      (algebraMap (Y.presheaf.stalk (f P)) (X.presheaf.stalk P)) =
        maximalIdeal (X.presheaf.stalk P) ^ n := hmap
  rw [← hn, Ideal.ramificationIdx'_spec (hmap' ▸ le_rfl) (hmap' ▸ not_pow_succ_le_pow n)]

/-- Over an algebraically closed field `k`, a closed point `z` of a scheme locally of finite type
over `k` has residue field `k`: the map `k(g z) → k(z)` is surjective. -/
theorem surjective_residueFieldMap_of_isClosed [IsAlgClosed k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] {z : Z} (hz : IsClosed ({z} : Set Z)) :
    Function.Surjective (g.residueFieldMap z).hom := by
  set c := Spec.preimage ((Spec (.of k)).fromSpecResidueField (g z))
  have h1 : Spec.preimage (Z.fromSpecResidueField z ≫ g) = c ≫ g.residueFieldMap z := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have h2 : (residueFieldIsoBase g z hz).inv = c ≫ g.residueFieldMap z := h1
  intro y
  refine ⟨c ((residueFieldIsoBase g z hz).hom y), ?_⟩
  have h3 := ConcreteCategory.congr_hom (residueFieldIsoBase g z hz).hom_inv_id y
  rw [h2] at h3
  exact h3

private theorem pow_eq_self_iff {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) : maximalIdeal R ^ n = maximalIdeal R ↔ n = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, pow_one]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_span_singleton] at h
  have h' : Associated (π ^ n) (π ^ 1) := by rwa [pow_one]
  exact le_antisymm ((pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 h'.dvd)
    ((pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 h'.symm.dvd)

/-- **Unramified points.** For `k` algebraically closed and a closed point `P`, `e_P = 1` if and
only if `f` is unramified at `P`: `m_Q 𝒪_{X,P} = m_P` and `k(P)/k(Q)` is separable algebraic. -/
theorem ramificationIndex_eq_one_iff [IsAlgClosed k] (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] {P : X} (hP : coheight P = 1) :
    hX.ramificationIndex hY f P = 1 ↔ Hartshorne.HartshorneUnramifiedAt f P := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  have := X.codimensionOneStalk_isDiscreteValuationRing hX.satisfiesConditionStar hP
  obtain ⟨n, hn, hmap⟩ := hX.exists_map_maximalIdeal_eq_pow hY f hP
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := hY.locallyOfFiniteType
  have hsurj : Function.Surjective (f.residueFieldMap P).hom := by
    have h := surjective_residueFieldMap_of_isClosed (f ≫ Y ↘ Spec (.of k))
      ((hX.isClosed_singleton_iff_coheight_eq_one P).2 hP)
    rw [Scheme.residueFieldMap_comp] at h
    exact Function.Surjective.of_comp h
  have hres : letI := (f.residueFieldMap P).hom.toAlgebra
      Algebra.IsAlgebraic (Y.residueField (f P)) (X.residueField P) ∧
        Algebra.IsSeparable (Y.residueField (f P)) (X.residueField P) := by
    let _ := (f.residueFieldMap P).hom.toAlgebra
    refine ⟨⟨fun y ↦ ?_⟩, ⟨fun y ↦ ?_⟩⟩
    · obtain ⟨a, rfl⟩ := hsurj y
      exact isAlgebraic_algebraMap a
    · obtain ⟨a, rfl⟩ := hsurj y
      exact isSeparable_algebraMap a
  rw [← hn, Nat.cast_eq_one, ← pow_eq_self_iff (R := X.presheaf.stalk P), ← hmap]
  exact ⟨fun h ↦ ⟨h, hres⟩, fun h ↦ h.1⟩

/-- `f` is **tamely ramified** at `P` if `char k = 0`, or `char k = p` and `p ∤ e_P`.
Meaningful only at closed points (`coheight P = 1`), as in Hartshorne IV.2. -/
def IsTamelyRamifiedAt (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [LocallyQuasiFinite f] (P : X) : Prop :=
  ringChar k = 0 ∨ ¬ ((ringChar k : ℤ) ∣ hX.ramificationIndex hY f P)

/-- `f` is **wildly ramified** at `P` if it is not tamely ramified there.
Meaningful only at closed points (`coheight P = 1`). -/
def IsWildlyRamifiedAt (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [LocallyQuasiFinite f] (P : X) : Prop :=
  ¬ hX.IsTamelyRamifiedAt hY f P

end Scheme.IsNonsingularCurve

end AlgebraicGeometry
