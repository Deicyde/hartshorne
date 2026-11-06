/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.WeilClassGroup
import Hartshorne.Scheme.CodimensionOneStalkDVR
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Pullback of divisors along finite morphisms of nonsingular curves

Hartshorne, *Algebraic Geometry*, II.6, definitions before Proposition 6.9 (pp. 137–138).

A curve over a field `k` is an integral separated scheme of finite type over `k` of dimension
one; it is nonsingular when all its local rings are regular (Hartshorne II.6, p. 136). Such a
curve satisfies condition `(*)`, so its Weil divisors and class group are those of
`Hartshorne.Scheme.WeilClassGroup`. Its codimension-one points are exactly its closed points,
i.e. the points other than the generic point.

For a finite morphism `f : X ⟶ Y` of nonsingular curves:

* fibres of `f` are finite and discrete, so `f` maps the generic point to the generic point
  and closed points to closed points; hence `f` induces `f^# : K(Y) →+* K(X)` and its degree
  `deg f = [K(X) : K(Y)]` is defined;
* for a closed point `Q` of `Y` and a local parameter `t` (an irreducible element, i.e. a
  uniformizer, of the discrete valuation ring `𝒪_{Y,Q}`), `f^*Q = ∑_{f(P) = Q} ord_P(t) P`; the
  coefficient does not depend on `t` because two local parameters differ by a unit of `𝒪_{Y,Q}`,
  whose image in every `𝒪_{X,P}` above `Q` is a unit;
* `f^*` extends additively to `Div Y → Div X`, and `f^*((g)) = (f^# g)` because writing
  `g = u t^n` with `u` a unit gives `ord_P(f^# g) = ord_Q(g) ord_P(t)`; hence `f^*` descends to
  `Cl Y → Cl X`.

The degree of a curve divisor is the sum of its coefficients. The algebraic closedness of the
ground field and the `k`-linearity of `f` are part of Hartshorne's setting; they are recorded in
the main statements but are not needed for these constructions.
-/

noncomputable section

open CategoryTheory Limits Order TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- A **nonsingular curve** over a field `k` (Hartshorne II.6, p. 136): a scheme `X` over `k`
that is separated and of finite type over `k`, has dimension one, and all of whose local rings
are regular local rings. Integrality of `X`, also part of Hartshorne's definition of a curve, is
supplied separately as the instance `IsIntegral X`. -/
structure Scheme.IsNonsingularCurve (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] : Prop where
  isSeparated : IsSeparated (X ↘ Spec (.of k))
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ Spec (.of k))
  quasiCompact : QuasiCompact (X ↘ Spec (.of k))
  topologicalKrullDim_eq_one : topologicalKrullDim X = 1
  isRegularLocalRing_stalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- Points in a common fibre of a locally quasi-finite morphism admit no nontrivial
specialization, because the fibres are discrete. -/
theorem Scheme.Hom.eq_of_specializes_of_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] {x x' : X} (h : x ⤳ x') (hf : f x = f x') : x = x' := by
  have := (f.isDiscrete_preimage_singleton (f x')).to_subtype
  have hs : (⟨x, hf⟩ : f ⁻¹' {f x'}) ⤳ ⟨x', rfl⟩ := (subtype_specializes_iff _ _).mpr h
  exact congrArg Subtype.val hs.eq

private def Scheme.weilDivisorOfFiniteSupport {X : Scheme.{u}} (c : X → ℤ)
    (hfin : (Function.support c).Finite) (hc : ∀ x, coheight x ≠ 1 → c x = 0) :
    X.WeilDivisor :=
  ⟨{ toFun := c
     supportWithinDomain' := Set.subset_univ _
     supportLocallyFiniteWithinDomain' := fun _ _ ↦
       ⟨Set.univ, Filter.univ_mem, by simpa using hfin⟩ }, hc⟩

@[simp]
private theorem Scheme.weilDivisorOfFiniteSupport_apply {X : Scheme.{u}} (c : X → ℤ)
    (hfin : (Function.support c).Finite) (hc : ∀ x, coheight x ≠ 1 → c x = 0) (x : X) :
    (Scheme.weilDivisorOfFiniteSupport c hfin hc).1 x = c x :=
  rfl

private theorem Scheme.weilDivisor_ext {X : Scheme.{u}} {D E : X.WeilDivisor}
    (h : ∀ x, D.1 x = E.1 x) : D = E :=
  Subtype.ext (Function.locallyFinsuppWithin.ext h)

namespace Scheme.IsNonsingularCurve

section OneCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A nonsingular curve satisfies Hartshorne's condition `(*)`: it is Noetherian (being of
finite type over a field), integral, separated, and regular in codimension one. -/
theorem satisfiesConditionStar [IsIntegral X] (hX : X.IsNonsingularCurve k) :
    X.SatisfiesConditionStar := by
  have := hX.isSeparated
  have := hX.locallyOfFiniteType
  have := hX.quasiCompact
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  refine ⟨{}, inferInstance, ⟨?_⟩, fun x _ ↦ hX.isRegularLocalRing_stalk x⟩
  rw [show terminal.from X = (X ↘ Spec (.of k)) ≫ terminal.from _ from terminal.hom_ext _ _]
  infer_instance

/-- The Krull dimension of the specialization order of a curve is one. -/
theorem krullDim_eq_one (hX : X.IsNonsingularCurve k) : krullDim X = 1 := by
  rw [← krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  exact hX.topologicalKrullDim_eq_one

/-- On a curve, the codimension-one points are the points other than the generic point. -/
theorem coheight_eq_one_iff [IsIntegral X] (hX : X.IsNonsingularCurve k) (x : X) :
    coheight x = 1 ↔ x ≠ genericPoint X := by
  have hle : x ≤ genericPoint X := (genericPoint_spec X).specializes trivial
  constructor
  · rintro h rfl
    have : IsMax (genericPoint X) := fun y _ ↦ (genericPoint_spec X).specializes trivial
    rw [coheight_eq_zero.mpr this] at h
    exact zero_ne_one h
  · intro hx
    have hlt : x < genericPoint X := ⟨hle, fun h ↦ hx (h.antisymm hle).eq⟩
    have h1 : (coheight x : WithBot ℕ∞) ≤ 1 := hX.krullDim_eq_one ▸ coheight_le_krullDim x
    have h1' : coheight x ≤ 1 := by exact_mod_cast h1
    have h0 : coheight (genericPoint X) + 1 ≤ coheight x := coheight_add_one_le hlt
    exact le_antisymm h1' (le_trans (by simp) h0)

/-- A curve has a point other than its generic point. -/
theorem exists_ne_genericPoint [IsIntegral X] (hX : X.IsNonsingularCurve k) :
    ∃ x : X, x ≠ genericPoint X := by
  by_contra! h
  have : Subsingleton X := ⟨fun a b ↦ (h a).trans (h b).symm⟩
  have := hX.krullDim_eq_one ▸ (krullDim_nonpos_of_subsingleton (α := X))
  exact absurd this (by decide)

/-- On a curve, the closed points are exactly the codimension-one points, i.e. the prime
divisors. -/
theorem isClosed_singleton_iff_coheight_eq_one [IsIntegral X] (hX : X.IsNonsingularCurve k)
    (x : X) : IsClosed ({x} : Set X) ↔ coheight x = 1 := by
  rw [hX.coheight_eq_one_iff]
  constructor
  · rintro hc rfl
    obtain ⟨y, hy⟩ := hX.exists_ne_genericPoint
    have : y ∈ closure ({genericPoint X} : Set X) :=
      specializes_iff_mem_closure.mp ((genericPoint_spec X).specializes trivial)
    rw [hc.closure_eq] at this
    exact hy this
  · intro hx
    refine closure_subset_iff_isClosed.mp ?_
    intro y hy
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    by_contra hne
    have hlt : y < x := ⟨hxy, fun h ↦ hne (hxy.antisymm h).eq.symm⟩
    have h1 := (hX.coheight_eq_one_iff x).mpr hx
    have h2 : coheight x + 1 ≤ coheight y := coheight_add_one_le hlt
    have h3 : (coheight y : WithBot ℕ∞) ≤ 1 := hX.krullDim_eq_one ▸ coheight_le_krullDim y
    have h3' : coheight y ≤ 1 := by exact_mod_cast h3
    rw [h1] at h2
    exact absurd (h2.trans h3') (by decide)

variable [IsIntegral X]

/-- The image of a unit of a codimension-one stalk in the function field has order zero. -/
theorem ordHom_algebraMap_of_isUnit (hX : X.IsNonsingularCurve k) {x : X}
    (hx : coheight x = 1) {u : X.presheaf.stalk x} (hu : IsUnit u) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    X.ordHom x hx (algebraMap _ X.functionField u) = 1 := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  exact Ring.ordFrac_of_isUnit hu

/-- A local parameter at a codimension-one point has order one. -/
theorem ordHom_algebraMap_of_irreducible (hX : X.IsNonsingularCurve k) {x : X}
    (hx : coheight x = 1) {t : X.presheaf.stalk x} (ht : Irreducible t) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    X.ordHom x hx (algebraMap _ X.functionField t) = WithZero.exp 1 := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have := X.codimensionOneStalk_isDiscreteValuationRing hX.satisfiesConditionStar hx
  exact Ring.ordFrac_irreducible ht

/-- A chosen local parameter (uniformizer of the discrete valuation ring `𝒪_{X,x}`) at a
codimension-one point `x`; it is `0` at the generic point. -/
def localParameter (hX : X.IsNonsingularCurve k) (x : X) : X.presheaf.stalk x :=
  if hx : coheight x = 1 then
    haveI := X.codimensionOneStalk_isDiscreteValuationRing hX.satisfiesConditionStar hx
    Classical.choose (IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x))
  else 0

theorem irreducible_localParameter (hX : X.IsNonsingularCurve k) {x : X}
    (hx : coheight x = 1) : Irreducible (hX.localParameter x) := by
  have := X.codimensionOneStalk_isDiscreteValuationRing hX.satisfiesConditionStar hx
  rw [localParameter, dif_pos hx]
  exact Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x))

/-- The **degree of a divisor** on a curve, `deg (∑ nᵢ Pᵢ) = ∑ nᵢ`. -/
def divisorDegree (hX : X.IsNonsingularCurve k) : X.WeilDivisor →+ ℤ :=
  let _ := hX.satisfiesConditionStar.isNoetherian
  (Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id ℤ).comp
    (X.weilDivisorAddEquivFinsupp : X.WeilDivisor →+ (X.PrimeDivisor →₀ ℤ))

theorem divisorDegree_apply (hX : X.IsNonsingularCurve k) (D : X.WeilDivisor) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    hX.divisorDegree D = (X.weilDivisorAddEquivFinsupp D).sum fun _ n ↦ n := by
  intro _
  exact Finsupp.liftAddHom_apply _ _

theorem divisorDegree_single (hX : X.IsNonsingularCurve k) (P : X.PrimeDivisor) (n : ℤ) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    hX.divisorDegree (X.weilDivisorAddEquivFinsupp.symm (Finsupp.single P n)) = n := by
  intro _
  rw [divisorDegree_apply, AddEquiv.apply_symm_apply, Finsupp.sum_single_index rfl]

end OneCurve

section TwoCurves

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [IsIntegral X] [IsIntegral Y]

/-- A locally quasi-finite (e.g. finite) morphism of curves maps the generic point to the
generic point. -/
theorem apply_genericPoint_eq (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [LocallyQuasiFinite f] : f (genericPoint X) = genericPoint Y := by
  by_contra hne
  have hc := (hY.isClosed_singleton_iff_coheight_eq_one _).mpr
    ((hY.coheight_eq_one_iff _).mpr hne)
  obtain ⟨x, hx⟩ := hX.exists_ne_genericPoint
  have hsp : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hmem : f x ∈ closure ({f (genericPoint X)} : Set Y) :=
    specializes_iff_mem_closure.mp (hsp.map f.continuous)
  rw [hc.closure_eq] at hmem
  exact hx (f.eq_of_specializes_of_apply_eq hsp hmem.symm).symm

/-- A locally quasi-finite (e.g. finite) morphism of curves maps codimension-one points to
codimension-one points. -/
theorem coheight_apply_eq_one (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [LocallyQuasiFinite f] {x : X} (hx : coheight x = 1) :
    coheight (f x) = 1 := by
  rw [hY.coheight_eq_one_iff]
  rw [hX.coheight_eq_one_iff] at hx
  intro h
  rw [← hX.apply_genericPoint_eq hY f] at h
  exact hx (f.eq_of_specializes_of_apply_eq
    ((genericPoint_spec X).specializes trivial) h.symm).symm

/-- Points lying over a codimension-one point have codimension one. -/
theorem coheight_eq_one_of_coheight_apply_eq_one (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] {x : X}
    (hx : coheight (f x) = 1) : coheight x = 1 := by
  rw [hX.coheight_eq_one_iff]
  rintro rfl
  rw [hX.apply_genericPoint_eq hY f, hY.coheight_eq_one_iff] at hx
  exact hx rfl

/-- The function-field homomorphism `f^# : K(Y) →+* K(X)` induced by a finite (more generally,
locally quasi-finite) morphism of curves, which is dominant. -/
def finiteCurveFunctionFieldMap (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [LocallyQuasiFinite f] : Y.functionField →+* X.functionField :=
  (Y.presheaf.stalkSpecializes (specializes_of_eq (hX.apply_genericPoint_eq hY f)) ≫
    f.stalkMap (genericPoint X)).hom

/-- `f^#` is compatible with the stalk maps `𝒪_{Y,f(x)} → 𝒪_{X,x}`. -/
theorem finiteCurveFunctionFieldMap_algebraMap (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X)
    (a : Y.presheaf.stalk (f x)) :
    hX.finiteCurveFunctionFieldMap hY f (algebraMap _ Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  have hsp : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have h := Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) x hsp a
  change (f.stalkMap (genericPoint X)) ((Y.presheaf.stalkSpecializes _)
    ((Y.presheaf.stalkSpecializes _) a)) = (X.presheaf.stalkSpecializes _) _
  rw [← h]
  congr 1
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

/-- The **degree** of a finite morphism of curves, `deg f = [K(X) : K(Y)]`. -/
def finiteCurveDegree (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [LocallyQuasiFinite f] : ℕ :=
  letI := (hX.finiteCurveFunctionFieldMap hY f).toAlgebra
  Module.finrank Y.functionField X.functionField

/-- For `f(x) = Q` of codimension one and a local parameter `t` at `Q`,
`ord_x(f^# g) = ord_Q(g) · ord_x(f^# t)`. -/
theorem ord_finiteCurveFunctionFieldMap (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] {x : X}
    (hx : coheight x = 1) {t : Y.presheaf.stalk (f x)} (ht : Irreducible t)
    {g : Y.functionField} (hg : g ≠ 0) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    let _ := hY.satisfiesConditionStar.isNoetherian
    X.ord (hX.finiteCurveFunctionFieldMap hY f g) x =
      Y.ord g (f x) * X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ t)) x := by
  intro _ _
  have hQ := hX.coheight_apply_eq_one hY f hx
  have := Y.codimensionOneStalk_isDiscreteValuationRing hY.satisfiesConditionStar hQ
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := Y.functionField) ht hg
  set φ := hX.finiteCurveFunctionFieldMap hY f
  set c := X.ord (φ (algebraMap _ _ t)) x
  have ht0 : algebraMap _ Y.functionField t ≠ 0 := by
    simpa [map_ne_zero_iff _ (IsFractionRing.injective _ _)] using ht.ne_zero
  have hφt : φ (algebraMap _ _ t) ≠ 0 := (map_ne_zero φ).mpr ht0
  have hc : X.ordHom x hx (φ (algebraMap _ _ t)) = Multiplicative.ofAdd c :=
    (X.ord_eq_iff hx hφt).mp rfl
  have hYord : Y.ord (u • algebraMap _ _ t ^ n) (f x) = n := by
    rw [Y.ord_eq_iff hQ hg, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      ordHom_algebraMap_of_isUnit hY hQ u.isUnit, ordHom_algebraMap_of_irreducible hY hQ ht,
      one_mul, WithZero.exp, ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
  have hφg : φ (u • algebraMap _ _ t ^ n) =
      algebraMap _ _ (f.stalkMap x u) * φ (algebraMap _ _ t) ^ n := by
    rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      finiteCurveFunctionFieldMap_algebraMap]
  rw [hYord, X.ord_eq_iff hx ((map_ne_zero φ).mpr hg), hφg, map_mul, map_zpow₀,
    ordHom_algebraMap_of_isUnit hX hx (u.isUnit.map _), one_mul, hc, ← WithZero.coe_zpow,
    ← ofAdd_zsmul, smul_eq_mul]

/-- The order `ord_x(f^# t)` does not depend on the choice of local parameter `t` at `f(x)`. -/
theorem ord_finiteCurveFunctionFieldMap_eq_of_irreducible (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] {x : X}
    (hx : coheight x = 1) {t t' : Y.presheaf.stalk (f x)} (ht : Irreducible t)
    (ht' : Irreducible t') :
    let _ := hX.satisfiesConditionStar.isNoetherian
    X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ t')) x =
      X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ t)) x := by
  intro _
  let _ := hY.satisfiesConditionStar.isNoetherian
  have hQ := hX.coheight_apply_eq_one hY f hx
  have ht0 : algebraMap _ Y.functionField t' ≠ 0 := by
    simpa [map_ne_zero_iff _ (IsFractionRing.injective _ _)] using ht'.ne_zero
  rw [hX.ord_finiteCurveFunctionFieldMap hY f hx ht ht0]
  have h1 : Y.ord (algebraMap _ Y.functionField t') (f x) = 1 := by
    rw [Y.ord_eq_iff hQ ht0, ordHom_algebraMap_of_irreducible hY hQ ht']
    rfl
  rw [h1, one_mul]

/-- The multiplicity `ord_x(t)` of `x` in the pullback of `f(x)`, computed with the chosen local
parameter `t` at `f(x)`. -/
def finiteCurvePullbackMultiplicity (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) : ℤ :=
  let _ := hX.satisfiesConditionStar.isNoetherian
  X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ (hY.localParameter (f x)))) x

theorem finiteCurvePullbackMultiplicity_eq (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] {x : X}
    (hx : coheight x = 1) {t : Y.presheaf.stalk (f x)} (ht : Irreducible t) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    hX.finiteCurvePullbackMultiplicity hY f x =
      X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ t)) x :=
  hX.ord_finiteCurveFunctionFieldMap_eq_of_irreducible hY f hx ht
    (hY.irreducible_localParameter (hX.coheight_apply_eq_one hY f hx))

theorem finiteCurvePullbackMultiplicity_eq_zero (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] {x : X}
    (hx : coheight x ≠ 1) : hX.finiteCurvePullbackMultiplicity hY f x = 0 := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  exact X.ord_eq_zero_of_coheight_neq_one hx _

open Classical in
/-- The **pullback of a point** along a finite morphism of curves,
`f^*Q = ∑_{f(P) = Q} ord_P(t) P`, a Weil divisor because the fibre over `Q` is finite. -/
def finiteCurvePointPullback (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [IsFinite f] (Q : Y) : X.WeilDivisor :=
  weilDivisorOfFiniteSupport
    (fun x ↦ if f x = Q then hX.finiteCurvePullbackMultiplicity hY f x else 0)
    ((f.finite_preimage_singleton Q).subset fun x hx ↦ by
      by_contra h
      exact hx (if_neg h))
    (fun x hx ↦ by
      dsimp only
      split_ifs
      · exact hX.finiteCurvePullbackMultiplicity_eq_zero hY f hx
      · rfl)

open Classical in
private theorem finiteCurvePointPullback_apply_aux (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] {Q : Y}
    (hQ : IsClosed ({Q} : Set Y)) {t : Y.presheaf.stalk Q} (ht : Irreducible t) (x : X) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    (hX.finiteCurvePointPullback hY f Q).1 x =
      if f x = Q then X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ t)) x
      else 0 := by
  intro _
  change (if f x = Q then hX.finiteCurvePullbackMultiplicity hY f x else 0) = _
  split_ifs with h
  · subst h
    have hQ1 := (hY.isClosed_singleton_iff_coheight_eq_one _).mp hQ
    exact hX.finiteCurvePullbackMultiplicity_eq hY f
      (hX.coheight_eq_one_of_coheight_apply_eq_one hY f hQ1) ht
  · rfl

open Classical in
/-- **Independence of the local parameter.** For a closed point `Q` of `Y` and any local
parameter `t` at `Q`, the coefficient of `P` in `f^*Q` is `ord_P(t)` if `f(P) = Q` and `0`
otherwise. -/
theorem finiteCurvePointPullback_apply [IsAlgClosed k] (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] [f.IsOver (Spec (.of k))]
    {Q : Y} (hQ : IsClosed ({Q} : Set Y)) {t : Y.presheaf.stalk Q} (ht : Irreducible t)
    (x : X) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    (hX.finiteCurvePointPullback hY f Q).1 x =
      if f x = Q then X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ t)) x
      else 0 :=
  finiteCurvePointPullback_apply_aux hX hY f hQ ht x

/-- **Finiteness of the fibre sum.** The support of `f^*Q` lies in the fibre `f⁻¹(Q)`, which
is finite. -/
theorem finiteCurvePointPullback_support_subset (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] (Q : Y) :
    Function.support (hX.finiteCurvePointPullback hY f Q).1 ⊆ f ⁻¹' {Q} ∧
      (f ⁻¹' {Q}).Finite := by
  classical
  refine ⟨fun x hx ↦ ?_, f.finite_preimage_singleton Q⟩
  by_contra h
  apply hx
  change (if f x = Q then hX.finiteCurvePullbackMultiplicity hY f x else 0) = 0
  exact if_neg h

open Classical in
/-- The defining formula `f^*Q = ∑_{f(P) = Q} ord_P(t) P`, as a finite sum in the free abelian
group on prime divisors, for a closed point `Q` and any local parameter `t` at `Q`. -/
theorem weilDivisorAddEquivFinsupp_finiteCurvePointPullback [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f]
    [f.IsOver (Spec (.of k))] {Q : Y} (hQ : IsClosed ({Q} : Set Y))
    {t : Y.presheaf.stalk Q} (ht : Irreducible t) :
    let _ := hX.satisfiesConditionStar.isNoetherian
    X.weilDivisorAddEquivFinsupp (hX.finiteCurvePointPullback hY f Q) =
      ∑ P ∈ ((f.finite_preimage_singleton Q).preimage Subtype.val_injective.injOn :
          (Subtype.val ⁻¹' (f ⁻¹' {Q}) : Set X.PrimeDivisor).Finite).toFinset,
        Finsupp.single P (X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ t)) P.1) := by
  intro _
  ext P
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_preimage,
    Set.mem_singleton_iff]
  change (hX.finiteCurvePointPullback hY f Q).1 P.1 = _
  rw [finiteCurvePointPullback_apply_aux hX hY f hQ ht]

/-- The **pullback of divisors** `f^* : Div Y → Div X` along a finite morphism of curves: the
coefficient of `P` in `f^*D` is `D(f(P)) · ord_P(t)` for a local parameter `t` at `f(P)`. -/
def finiteCurveDivisorPullback (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [IsFinite f] : Y.WeilDivisor →+ X.WeilDivisor where
  toFun D := weilDivisorOfFiniteSupport
    (fun x ↦ D.1 (f x) * hX.finiteCurvePullbackMultiplicity hY f x)
    (by
      let _ := hY.satisfiesConditionStar.isNoetherian
      refine ((Scheme.WeilDivisor.support_finite D).preimage'
        fun y _ ↦ f.finite_preimage_singleton y).subset fun x hx ↦ ?_
      exact left_ne_zero_of_mul hx)
    (fun x hx ↦ by
      dsimp only
      rw [hX.finiteCurvePullbackMultiplicity_eq_zero hY f hx, mul_zero])
  map_zero' := weilDivisor_ext fun x ↦ by simp
  map_add' D E := weilDivisor_ext fun x ↦ by
    simp only [weilDivisorOfFiniteSupport_apply]
    change (D.1 (f x) + E.1 (f x)) * _ = D.1 (f x) * _ + E.1 (f x) * _
    rw [add_mul]

theorem finiteCurveDivisorPullback_apply (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] (D : Y.WeilDivisor) (x : X) :
    (hX.finiteCurveDivisorPullback hY f D).1 x =
      D.1 (f x) * hX.finiteCurvePullbackMultiplicity hY f x :=
  rfl

/-- `f^*` on divisors is the additive extension of `Q ↦ f^*Q`: it sends the prime divisor `Q`
(a generator of the free abelian group `Div Y`) to `f^*Q`. -/
theorem finiteCurveDivisorPullback_primeDivisor [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f]
    [f.IsOver (Spec (.of k))] (Q : Y.PrimeDivisor) :
    let _ := hY.satisfiesConditionStar.isNoetherian
    hX.finiteCurveDivisorPullback hY f
        (Y.weilDivisorAddEquivFinsupp.symm (Finsupp.single Q 1)) =
      hX.finiteCurvePointPullback hY f Q.1 := by
  classical
  intro _
  refine weilDivisor_ext fun x ↦ ?_
  rw [finiteCurveDivisorPullback_apply]
  change _ = if f x = Q.1 then hX.finiteCurvePullbackMultiplicity hY f x else 0
  set D := Y.weilDivisorAddEquivFinsupp.symm (Finsupp.single Q 1)
  have hD : ∀ P : Y.PrimeDivisor, D.1 P.1 = Finsupp.single Q 1 P := fun P ↦
    congrArg (fun F ↦ F P)
      (Y.weilDivisorAddEquivFinsupp.apply_symm_apply (Finsupp.single Q 1))
  split_ifs with h
  · rw [h, hD Q, Finsupp.single_eq_same, one_mul]
  · by_cases hc : coheight (f x) = 1
    · rw [hD ⟨f x, hc⟩, Finsupp.single_eq_of_ne (fun e ↦ h (congrArg Subtype.val e)),
        zero_mul]
    · rw [D.2 _ hc, zero_mul]

private theorem finiteCurveDivisorPullback_principalDivisor_aux (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] (g : Y.functionFieldˣ) :
    hX.finiteCurveDivisorPullback hY f (Y.principalDivisor hY.satisfiesConditionStar g) =
      X.principalDivisor hX.satisfiesConditionStar
        (Units.map (hX.finiteCurveFunctionFieldMap hY f : Y.functionField →* X.functionField)
          g) := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  let _ := hY.satisfiesConditionStar.isNoetherian
  refine weilDivisor_ext fun x ↦ ?_
  rw [finiteCurveDivisorPullback_apply, principalDivisor_apply, principalDivisor_apply]
  by_cases hx : coheight x = 1
  · have hQ := hX.coheight_apply_eq_one hY f hx
    have ht := hY.irreducible_localParameter hQ
    rw [hX.finiteCurvePullbackMultiplicity_eq hY f hx ht]
    exact (hX.ord_finiteCurveFunctionFieldMap hY f hx ht g.ne_zero).symm
  · rw [hX.finiteCurvePullbackMultiplicity_eq_zero hY f hx, mul_zero]
    exact (X.ord_eq_zero_of_coheight_neq_one hx _).symm

/-- **Pullback of principal divisors.** `f^*((g)) = (f^# g)` for every nonzero rational
function `g` on `Y`. -/
theorem finiteCurveDivisorPullback_principalDivisor [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f]
    [f.IsOver (Spec (.of k))] (g : Y.functionFieldˣ) :
    hX.finiteCurveDivisorPullback hY f (Y.principalDivisor hY.satisfiesConditionStar g) =
      X.principalDivisor hX.satisfiesConditionStar
        (Units.map (hX.finiteCurveFunctionFieldMap hY f : Y.functionField →* X.functionField)
          g) :=
  finiteCurveDivisorPullback_principalDivisor_aux hX hY f g

/-- The pullback `f^* : Cl Y → Cl X` on Weil divisor class groups, induced by `f^*` on divisors
since it maps principal divisors to principal divisors. -/
def finiteCurveClassGroupPullback (hX : X.IsNonsingularCurve k) (hY : Y.IsNonsingularCurve k)
    (f : X ⟶ Y) [IsFinite f] :
    Y.WeilClassGroup hY.satisfiesConditionStar →+ X.WeilClassGroup hX.satisfiesConditionStar :=
  QuotientAddGroup.map _ _ (hX.finiteCurveDivisorPullback hY f) (by
    intro D hD
    change D ∈ (Y.principalDivisorHom hY.satisfiesConditionStar).range at hD
    obtain ⟨g, rfl⟩ := hD
    change _ ∈ (X.principalDivisorHom hX.satisfiesConditionStar).range
    exact ⟨Additive.ofMul (Units.map
      (hX.finiteCurveFunctionFieldMap hY f : Y.functionField →* X.functionField) g.toMul),
      (finiteCurveDivisorPullback_principalDivisor_aux hX hY f g.toMul).symm⟩)

/-- `f^*` on class groups is induced by `f^*` on divisors: `f^*[D] = [f^*D]`. -/
theorem finiteCurveClassGroupPullback_weilDivisorClassHom (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] (D : Y.WeilDivisor) :
    hX.finiteCurveClassGroupPullback hY f (Y.weilDivisorClassHom hY.satisfiesConditionStar D) =
      X.weilDivisorClassHom hX.satisfiesConditionStar (hX.finiteCurveDivisorPullback hY f D) :=
  rfl

end TwoCurves

end Scheme.IsNonsingularCurve

end AlgebraicGeometry
