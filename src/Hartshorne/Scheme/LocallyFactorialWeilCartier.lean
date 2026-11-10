/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.TotalQuotientIntegral
import Hartshorne.Scheme.CartierDivisorSheaf
import Hartshorne.Scheme.PrincipalDivisor
import Hartshorne.Scheme.LocallyFactorial
import Hartshorne.Scheme.AffineUFDClassGroup
import Hartshorne.Scheme.AbsoluteNormalizationUniversal

/-!
# Weil and Cartier divisors on locally factorial schemes

Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.11 and Remark 6.11.2 (pp. 141--142).

Let `X` be an integral Noetherian scheme. Since `K_X` is the constant
sheaf `K(X)` (see `Hartshorne.Scheme.TotalQuotientIntegral`), a Cartier divisor is given locally by
rational functions `f_i ∈ K(X)^*` on an open cover, well defined up to regular units on overlaps.
Its Weil divisor has coefficient `ord_Y(f_i)` at a prime divisor `Y` meeting `U_i`; this is
`AlgebraicGeometry.Scheme.cartierToWeil`.

* For normal `X` the map is injective, and its image is exactly the subgroup of locally principal
  Weil divisors (Remark 6.11.2): `AlgebraicGeometry.Scheme.cartierEquivLocallyPrincipal`.
  Both directions rest on the fact that a rational function with nonnegative order at every
  codimension-one point of an open set is regular there; this follows from the height-one
  intersection theorem on affine opens and gluing. The inverse glues the local equations of a
  locally principal divisor.
* If `X` is also separated and locally factorial, every Weil divisor is locally principal: near a point `x`, each
  prime divisor through `x` corresponds to a height-one prime of the factorial local ring at `x`,
  which is principal, and its generator spreads out to a local equation. Hence `cartierToWeil` is
  an isomorphism (Proposition 6.11), `AlgebraicGeometry.Scheme.weilCartierEquiv`, under which
  principal Weil divisors correspond to principal Cartier divisors.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Order

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}}

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CartierDivisor

/-- Every Cartier divisor is represented near each point by a local total-quotient unit. -/
theorem exists_local_representative (D : X.CartierDivisor) (x : X) :
    ∃ p : (U : X.Opens) × X.totalQuotientUnitsSheaf.obj.obj (op U), x ∈ p.1 ∧
      D.restrict p.1 = X.toCartierDivisorSheaf.hom.app (op p.1) (Additive.ofMul p.2) := by
  have hloc : TopCat.Presheaf.IsLocallySurjective X.toCartierDivisorSheaf.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi X.toCartierDivisorSheaf).2
      (toCartierDivisorSheaf_epi X)
  obtain ⟨U, _, hex, hx⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).1 hloc ⊤ D x trivial
  obtain ⟨s, hs⟩ := hex
  exact ⟨⟨U, s.toMul⟩, hx, hs.symm⟩

end CartierDivisor

/-- If two local total-quotient units define the same local Cartier section, then their ratio
is a regular unit. -/
theorem exists_structureUnits_eq_div_of_toCartierDivisorSheaf_eq (U : X.Opens)
    (f g : X.totalQuotientUnitsSheaf.obj.obj (op U))
    (h : X.toCartierDivisorSheaf.hom.app (op U) (Additive.ofMul f) =
      X.toCartierDivisorSheaf.hom.app (op U) (Additive.ofMul g)) :
    ∃ a : X.structureUnitsSheaf.obj.obj (op U),
      X.structureUnitsToTotalQuotientUnits.hom.app (op U) a = f / g := by
  let i := X.structureUnitsToTotalQuotientUnitsAdd
  let q := X.toCartierDivisorSheaf
  have hz : q.hom.app (op U) (Additive.ofMul f - Additive.ofMul g) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr h
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
    ShortComplex.mk i q (cokernel.condition i)
  obtain ⟨t, ht⟩ := TopCat.Sheaf.sections_exact_of_left_exact (ShortComplex.exact_cokernel i)
    (show Mono S.f from structureUnitsToTotalQuotientUnitsAdd_mono X)
    (Additive.ofMul f - Additive.ofMul g) hz
  refine ⟨t.toMul, ?_⟩
  change Additive.ofMul
      (X.structureUnitsToTotalQuotientUnits.hom.app (op U) t.toMul) =
    Additive.ofMul (f / g) at ht
  exact Additive.ofMul.injective ht

/-- A regular unit defines the zero local Cartier section. -/
theorem toCartierDivisorSheaf_structureUnits (U : X.Opens)
    (a : X.structureUnitsSheaf.obj.obj (op U)) :
    X.toCartierDivisorSheaf.hom.app (op U)
      (Additive.ofMul (X.structureUnitsToTotalQuotientUnits.hom.app (op U) a)) = 0 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun φ ↦ φ.hom) X.structureUnitsToTotalQuotientUnitsAdd_comp_toCartierDivisorSheaf)
    (op U)) (Additive.ofMul a)

namespace CartierDivisor

variable [IsIntegral X] [IsNoetherian X]

/-- Two local equations of a Cartier divisor have the same order at every common point, since
their ratio is a regular unit. -/
theorem ord_eq_of_represents (D : X.CartierDivisor) {U V : X.Opens}
    (f : X.totalQuotientUnitsSheaf.obj.obj (op U))
    (g : X.totalQuotientUnitsSheaf.obj.obj (op V))
    (hf : D.restrict U = X.toCartierDivisorSheaf.hom.app (op U) (Additive.ofMul f))
    (hg : D.restrict V = X.toCartierDivisorSheaf.hom.app (op V) (Additive.ofMul g))
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) :
    X.ord (totalQuotientUnitsEquivFunctionField U (genericPoint_mem_opens_of_mem hxU) f :
      X.functionField) x =
    X.ord (totalQuotientUnitsEquivFunctionField V (genericPoint_mem_opens_of_mem hxV) g :
      X.functionField) x := by
  have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  have hW := genericPoint_mem_opens_of_mem hxW
  have hf' := D.restrict_eq_of_le (inf_le_left : U ⊓ V ≤ U) hf
  have hg' := D.restrict_eq_of_le (inf_le_right : U ⊓ V ≤ V) hg
  obtain ⟨a, ha⟩ :=
    exists_structureUnits_eq_div_of_toCartierDivisorSheaf_eq _ _ _ (hf'.symm.trans hg')
  have hae := congrArg (totalQuotientUnitsEquivFunctionField (U ⊓ V) hW) ha
  rw [map_div, totalQuotientUnitsEquivFunctionField_map, totalQuotientUnitsEquivFunctionField_map]
    at hae
  have hae' := congrArg (fun u : X.functionFieldˣ ↦ (u : X.functionField)) hae
  simp only [Units.val_div_eq_div_val] at hae'
  rw [totalQuotientUnitsEquivFunctionField_structureUnits (U ⊓ V) hW a] at hae'
  have : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hxW⟩⟩
  rw [eq_div_iff (Units.ne_zero _)] at hae'
  have hunit : IsUnit (X.germToFunctionField (U ⊓ V) (Units.val (α := Γ(X, U ⊓ V)) a)) :=
    (Units.isUnit (M := Γ(X, U ⊓ V)) a).map (X.germToFunctionField (U ⊓ V)).hom
  rw [← hae', ord_mul hunit.ne_zero (Units.ne_zero _)]
  rw [show X.presheaf.germ (U ⊓ V) (genericPoint X) hW (Units.val (α := Γ(X, U ⊓ V)) a) =
    X.germToFunctionField (U ⊓ V) (Units.val (α := Γ(X, U ⊓ V)) a) from rfl,
    ord_of_isUnit (Units.isUnit (M := Γ(X, U ⊓ V)) a) hxW, zero_add]

/-- A chosen local equation of a Cartier divisor near a point. -/
def localEquation (D : X.CartierDivisor) (x : X) :
    (U : X.Opens) × X.totalQuotientUnitsSheaf.obj.obj (op U) :=
  Classical.choose (D.exists_local_representative x)

omit [IsIntegral X] [IsNoetherian X] in
theorem mem_localEquation (D : X.CartierDivisor) (x : X) : x ∈ (D.localEquation x).1 :=
  (Classical.choose_spec (D.exists_local_representative x)).1

omit [IsIntegral X] [IsNoetherian X] in
theorem restrict_localEquation (D : X.CartierDivisor) (x : X) :
    D.restrict (D.localEquation x).1 = X.toCartierDivisorSheaf.hom.app (op (D.localEquation x).1)
      (Additive.ofMul (D.localEquation x).2) :=
  (Classical.choose_spec (D.exists_local_representative x)).2

/-- The order of a Cartier divisor at a point, computed from a local equation. -/
def weilCoeff (D : X.CartierDivisor) (x : X) : ℤ :=
  X.ord (totalQuotientUnitsEquivFunctionField _
    (genericPoint_mem_opens_of_mem (D.mem_localEquation x)) (D.localEquation x).2 :
      X.functionField) x

/-- The order of a Cartier divisor can be computed from any local equation. -/
theorem weilCoeff_eq (D : X.CartierDivisor) {U : X.Opens}
    (f : X.totalQuotientUnitsSheaf.obj.obj (op U))
    (hf : D.restrict U = X.toCartierDivisorSheaf.hom.app (op U) (Additive.ofMul f))
    {x : X} (hx : x ∈ U) :
    D.weilCoeff x = X.ord (totalQuotientUnitsEquivFunctionField U
      (genericPoint_mem_opens_of_mem hx) f : X.functionField) x :=
  D.ord_eq_of_represents _ f (D.restrict_localEquation x) hf (D.mem_localEquation x) hx

/-- The order of a sum of Cartier divisors is the sum of the orders. -/
theorem weilCoeff_add (D E : X.CartierDivisor) (x : X) :
    (D + E).weilCoeff x = D.weilCoeff x + E.weilCoeff x := by
  set U := (D.localEquation x).1
  set V := (E.localEquation x).1
  have hxU : x ∈ U := D.mem_localEquation x
  have hxV : x ∈ V := E.mem_localEquation x
  have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  have hf' := D.restrict_eq_of_le (inf_le_left : U ⊓ V ≤ U) (D.restrict_localEquation x)
  have hg' := E.restrict_eq_of_le (inf_le_right : U ⊓ V ≤ V) (E.restrict_localEquation x)
  have hsum : (D + E).restrict (U ⊓ V) = X.toCartierDivisorSheaf.hom.app (op (U ⊓ V))
      (Additive.ofMul
        (X.totalQuotientUnitsSheaf.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
            (D.localEquation x).2 *
          X.totalQuotientUnitsSheaf.obj.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op
            (E.localEquation x).2)) := by
    rw [show (D + E).restrict (U ⊓ V) = D.restrict (U ⊓ V) + E.restrict (U ⊓ V) from
      map_add _ D E, hf', hg']
    exact (map_add _ _ _).symm
  rw [D.weilCoeff_eq _ hf' hxW, E.weilCoeff_eq _ hg' hxW, (D + E).weilCoeff_eq _ hsum hxW,
    map_mul, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _)]

end CartierDivisor

open Set Filter in
private theorem finite_codimensionOne_compl_of_nonempty
    [IsNoetherian X] [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    {x : X | Order.coheight x = 1 ∧ x ∉ (U : Set X)}.Finite := by
  obtain ⟨T, hTfin, hTclosed, hTirr, hTC⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let _ : Fintype T := hTfin.fintype
  let g : T → X := fun t ↦ (hTirr t.1 t.2).genericPoint
  refine (Set.finite_range g).subset ?_
  intro x hx
  have hxC : x ∈ (U : Set X)ᶜ := hx.2
  have hclosureC : closure ({x} : Set X) ⊆ Uᶜ :=
    closure_minimal (by simpa) U.isOpen.isClosed_compl
  let Tf : Finset (Set X) := hTfin.toFinset
  have hTfclosed : ∀ t ∈ Tf, IsClosed t := by
    intro t ht
    exact hTclosed t (hTfin.mem_toFinset.mp ht)
  have hclosureUnion : closure ({x} : Set X) ⊆ ⋃₀ (Tf : Set (Set X)) := by
    rw [hTfin.coe_toFinset, ← hTC]
    exact hclosureC
  obtain ⟨t, htTf, hclosuret⟩ :=
    (isIrreducible_iff_sUnion_isClosed.mp isIrreducible_singleton.closure)
      Tf hTfclosed hclosureUnion
  have htT : t ∈ T := hTfin.mem_toFinset.mp htTf
  let Z : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  let W : IrreducibleCloseds X := ⟨t, hTirr t htT, hTclosed t htT⟩
  have hZW : Z ≤ W := by
    change (Z : Set X) ⊆ t
    simpa [Z] using hclosuret
  have hZcoheight : Order.coheight Z = 1 := by
    change Order.coheight (irreducibleSetEquivPoints.symm x) = 1
    rw [Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm]
    exact hx.1
  have hZW_eq : Z = W := by
    apply le_antisymm hZW
    by_contra hWZ
    have hlt : Z < W := ⟨hZW, hWZ⟩
    have hWle : Order.coheight W ≤ 1 := by
      rw [← hZcoheight]
      exact Order.coheight_anti hZW
    have hWfin : Order.coheight W < ⊤ := lt_of_le_of_lt hWle (by simp)
    have hcoheight_lt : Order.coheight W < Order.coheight Z :=
      Order.coheight_strictAnti hlt hWfin
    rw [hZcoheight] at hcoheight_lt
    have hWzero : Order.coheight W = 0 :=
      Order.lt_one_iff.mp hcoheight_lt
    let Wtop : IrreducibleCloseds X :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have hWtop : W = Wtop :=
      (Order.coheight_eq_zero.mp hWzero).eq_of_le (Set.subset_univ _)
    have htC : t ⊆ Uᶜ := by
      rw [hTC]
      exact subset_sUnion_of_mem htT
    obtain ⟨y, hy⟩ := (inferInstance : Nonempty U)
    have hyW : y ∈ (W : Set X) := by
      rw [hWtop]
      change y ∈ (Set.univ : Set X)
      trivial
    exact (show y ∉ (U : Set X) from htC hyW) hy
  refine ⟨⟨t, htT⟩, ?_⟩
  change irreducibleSetEquivPoints W = x
  rw [← hZW_eq]
  exact (irreducibleSetEquivPoints (α := X)).apply_symm_apply x

/-- On an integral Noetherian scheme, a nonzero rational function has nonzero order at only
finitely many points. -/
theorem finite_support_ord [IsIntegral X] [IsNoetherian X] {f : X.functionField} (hf : f ≠ 0) :
    (Function.support fun x : X ↦ X.ord f x).Finite := by
  obtain ⟨U, _, fU, hU, hUf, hfU⟩ := exists_isUnit_germ_eq X f hf
  refine (finite_codimensionOne_compl_of_nonempty U).subset ?_
  intro x hx
  change X.ord f x ≠ 0 at hx
  constructor
  · by_contra hcodim
    exact hx (X.ord_eq_zero_of_coheight_neq_one hcodim f)
  · intro hxU
    apply hx
    rw [← hUf]
    exact X.ord_of_isUnit hfU hxU

/-- The Weil divisor of a Cartier divisor. -/
def cartierToWeilFun [IsIntegral X] [IsNoetherian X] (D : X.CartierDivisor) : X.WeilDivisor :=
  ⟨{ toFun := D.weilCoeff
     supportWithinDomain' := Set.subset_univ _
     supportLocallyFiniteWithinDomain' := fun z _ ↦ by
       refine ⟨(D.localEquation z).1, (D.localEquation z).1.isOpen.mem_nhds
         (D.mem_localEquation z), ?_⟩
       have hfin := finite_support_ord
         (Units.ne_zero (totalQuotientUnitsEquivFunctionField _
           (genericPoint_mem_opens_of_mem (D.mem_localEquation z)) (D.localEquation z).2))
       refine hfin.subset ?_
       rintro y ⟨hy, hy'⟩
       rw [Function.mem_support, D.weilCoeff_eq _ (D.restrict_localEquation z) hy] at hy'
       exact hy' },
   fun x hx ↦ ord_eq_zero_of_coheight_neq_one hx _⟩

/-- The homomorphism from Cartier divisors to Weil divisors. -/
def cartierToWeil [IsIntegral X] [IsNoetherian X] :
    X.CartierDivisor →+ X.WeilDivisor :=
  AddMonoidHom.mk' cartierToWeilFun fun D E ↦
    Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ D.weilCoeff_add E x)

/-- The coefficient of the Weil divisor of a Cartier divisor at a point of an open set is the order
of any local equation on that open set. -/
theorem cartierToWeil_apply [IsIntegral X] [IsNoetherian X]
    (D : X.CartierDivisor) {U : X.Opens} (f : X.totalQuotientUnitsSheaf.obj.obj (op U))
    (hf : D.restrict U = X.toCartierDivisorSheaf.hom.app (op U) (Additive.ofMul f))
    {x : X} (hx : x ∈ U) :
    (cartierToWeil D).1 x = X.ord (totalQuotientUnitsEquivFunctionField U
      (genericPoint_mem_opens_of_mem hx) f : X.functionField) x :=
  D.weilCoeff_eq f hf hx

/-- Restricting a Cartier divisor to the whole scheme does nothing. -/
theorem CartierDivisor.restrict_top (D : X.CartierDivisor) : D.restrict ⊤ = D := by
  change X.cartierDivisorSheaf.obj.map (homOfLE le_top).op D = D
  rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id]
  rfl

/-- The Weil divisor of the principal Cartier divisor of a global section of `K_X^*` is the
principal Weil divisor of the corresponding rational function. -/
theorem cartierToWeil_principalCartierDivisor [IsIntegral X] [IsNoetherian X]
    (hX : X.SatisfiesConditionStar) (f : X.totalQuotientUnitsSheaf.obj.obj (op ⊤)) :
    cartierToWeil (X.principalCartierDivisor f) =
      X.principalDivisor hX (totalQuotientUnitsEquivFunctionField ⊤ trivial f) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  rw [X.principalDivisor_apply hX]
  exact cartierToWeil_apply _ f (X.principalCartierDivisor f).restrict_top
    (show x ∈ (⊤ : X.Opens) from trivial)

open Hartshorne in
@[deprecated Hartshorne.isIntegrallyClosed_sections_of_isNormal (since := "2026-11-09")]
theorem isIntegrallyClosed_of_isAffineOpen [IsIntegral X] [IsNormal X] {V : X.Opens}
    (hV : IsAffineOpen V) [Nonempty V] : IsIntegrallyClosed Γ(X, V) :=
  Hartshorne.isIntegrallyClosed_sections_of_isNormal X hV

/-- On a normal Noetherian scheme, the local ring at a codimension-one point is a discrete
valuation ring. -/
theorem isDiscreteValuationRing_stalk_of_isNormal [IsNoetherian X]
    [Hartshorne.IsNormal X] {z : X} (hz : coheight z = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk z) := by
  have hdim : ringKrullDim (X.presheaf.stalk z) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact WithBot.coe_eq_coe.mpr hz
  exact ((Hartshorne.dvr_characterizations (X.presheaf.stalk z) hdim).out 1 0).mp
    (show IsIntegrallyClosed (X.presheaf.stalk z) from inferInstance)

open Hartshorne in
/-- On a normal integral Noetherian scheme, a nonzero rational function with nonnegative order at
every codimension-one point of a nonempty affine open set is regular there. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg [IsIntegral X] [IsNoetherian X] [IsNormal X]
    {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V]
    {k : X.functionField} (hk : k ≠ 0)
    (h : ∀ y ∈ V, Order.coheight y = 1 → 0 ≤ X.ord k y) :
    ∃ a : Γ(X, V), X.germToFunctionField V a = k := by
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsIntegrallyClosed Γ(X, V) := Hartshorne.isIntegrallyClosed_sections_of_isNormal _ hV
  have : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  refine exists_algebraMap_eq_of_forall_height_one X.functionField k fun P hP hheight ↦ ?_
  let y : PrimeSpectrum Γ(X, V) := ⟨P, hP⟩
  have hy : hV.fromSpec y ∈ V := by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact Set.mem_range_self y
  let _ : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hV.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) P :=
    hV.isLocalization_stalk' y hy
  have hcoh : Order.coheight (hV.fromSpec y) = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight (hV.fromSpec y)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk (hV.fromSpec y)),
      hheight] at h1
    exact (WithBot.coe_eq_coe.mp h1).symm
  have : IsDiscreteValuationRing (X.presheaf.stalk (hV.fromSpec y)) :=
    isDiscreteValuationRing_stalk_of_isNormal hcoh
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) X.functionField :=
    functionField_isScalarTower X V ⟨hV.fromSpec y, hy⟩
  have hle := h _ hy hcoh
  rw [le_ord_iff hcoh hk] at hle
  exact mem_ofField_of_one_le_ordFrac (R := X.presheaf.stalk (hV.fromSpec y)) P hk hle

/-- The order of the inverse of a nonzero rational function is the negative of its order. -/
theorem ord_inv_eq_neg [IsIntegral X] [IsNoetherian X] {k : X.functionField} (hk : k ≠ 0)
    (y : X) : X.ord k⁻¹ y = -X.ord k y := by
  have h1 : X.ord (1 : X.functionField) y = 0 := by
    have h := X.ord_mul (x := y) (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at h
    omega
  have h := X.ord_mul (x := y) hk (inv_ne_zero hk)
  rw [mul_inv_cancel₀ hk, h1] at h
  omega

open Hartshorne in
/-- On a normal integral Noetherian scheme, a nonzero rational function with nonnegative order at
every codimension-one point of a nonempty open set is regular there: regularity is checked on an
affine cover, and the local regular functions glue. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg_of_opens [IsIntegral X] [IsNoetherian X]
    [IsNormal X] {W : X.Opens} [Nonempty W] {k : X.functionField} (hk : k ≠ 0)
    (h : ∀ y ∈ W, Order.coheight y = 1 → 0 ≤ X.ord k y) :
    ∃ a : Γ(X, W), X.germToFunctionField W a = k := by
  have hloc : ∀ x : W, ∃ V : X.Opens, IsAffineOpen V ∧ x.1 ∈ V ∧ V ≤ W := fun x ↦ by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.isOpen
    exact ⟨V, hV, hxV, hVW⟩
  choose V hV hxV hVW using hloc
  have hreg : ∀ x : W, ∃ a : Γ(X, V x),
      X.presheaf.germ (V x) (genericPoint X) (genericPoint_mem_opens_of_mem (hxV x)) a = k := by
    intro x
    have : Nonempty (V x) := ⟨⟨_, hxV x⟩⟩
    exact exists_germToFunctionField_eq_of_ord_nonneg (hV x) hk
      fun y hy hy1 ↦ h y (hVW x hy) hy1
  choose a ha using hreg
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.presheaf V a := by
    intro i j
    by_cases hη : genericPoint X ∈ V i ⊓ V j
    · apply germ_injective_of_isIntegral (X := X) (U := V i ⊓ V j) _ hη
      change X.presheaf.germ _ _ hη (X.presheaf.map (homOfLE inf_le_left).op (a i)) =
        X.presheaf.germ _ _ hη (X.presheaf.map (homOfLE inf_le_right).op (a j))
      rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, ha i, ha j]
    · have hbot := opens_eq_bot_of_genericPoint_notMem hη
      have : Subsingleton Γ(X, V i ⊓ V j) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
      exact Subsingleton.elim (α := Γ(X, V i ⊓ V j)) _ _
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V W (fun x ↦ homOfLE (hVW x))
    (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV _⟩) a hcompat
  obtain ⟨x⟩ := ‹Nonempty W›
  refine ⟨s, ?_⟩
  have hx := ha x
  rw [← hs x] at hx
  change X.presheaf.germ _ _ _ (X.presheaf.map (homOfLE (hVW x)).op s) = k at hx
  rw [X.presheaf.germ_res_apply] at hx
  exact hx

open Hartshorne in
/-- On a normal integral Noetherian scheme, a nonzero rational function with order zero at every
codimension-one point of a nonempty open set is a regular unit there. -/
theorem exists_unit_germToFunctionField_eq_of_ord_eq_zero [IsIntegral X] [IsNoetherian X]
    [IsNormal X] {V : X.Opens} [Nonempty V]
    (k : X.functionFieldˣ) (h : ∀ y ∈ V, Order.coheight y = 1 → X.ord (k : X.functionField) y = 0) :
    ∃ a : Γ(X, V)ˣ, X.germToFunctionField V a = k := by
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg_of_opens k.ne_zero
    fun y hy hy1 ↦ (h y hy hy1).ge
  obtain ⟨b, hb⟩ := exists_germToFunctionField_eq_of_ord_nonneg_of_opens (inv_ne_zero k.ne_zero)
    fun y hy hy1 ↦ by rw [ord_inv_eq_neg k.ne_zero, h y hy hy1, neg_zero]
  have hab : a * b = 1 := by
    apply X.germToFunctionField_injective V
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ k.ne_zero]
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ha⟩

/-- On a normal integral Noetherian scheme, a Cartier divisor with zero Weil divisor is zero. -/
theorem cartierToWeil_injective [IsIntegral X] [IsNoetherian X] [Hartshorne.IsNormal X] :
    Function.Injective (cartierToWeil (X := X)) := by
  rw [injective_iff_map_eq_zero]
  intro D hD
  have hloc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ D.restrict V = 0 := by
    intro x
    obtain ⟨⟨U, f⟩, hxU, hf⟩ := D.exists_local_representative x
    obtain ⟨_, ⟨V, -, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hηV := genericPoint_mem_opens_of_mem hxV
    have hfV := D.restrict_eq_of_le hVU hf
    obtain ⟨a, ha⟩ := exists_unit_germToFunctionField_eq_of_ord_eq_zero
      (totalQuotientUnitsEquivFunctionField V hηV
        (X.totalQuotientUnitsSheaf.obj.map (homOfLE hVU).op f)) fun y hy _ ↦ by
          refine (cartierToWeil_apply D _ hfV hy).symm.trans ?_
          rw [hD]
          rfl
    refine ⟨V, hxV, ?_⟩
    have heq : X.structureUnitsToTotalQuotientUnits.hom.app (op V) a =
        X.totalQuotientUnitsSheaf.obj.map (homOfLE hVU).op f := by
      apply (totalQuotientUnitsEquivFunctionField V hηV).injective
      ext
      rw [totalQuotientUnitsEquivFunctionField_structureUnits V hηV a]
      exact ha
    rw [hfV]
    refine (congrArg (fun t ↦ X.toCartierDivisorSheaf.hom.app (op V) (Additive.ofMul t))
      heq.symm).trans ?_
    exact toCartierDivisorSheaf_structureUnits V a
  choose V hxV hV using hloc
  apply X.cartierDivisorSheaf.eq_of_locally_eq' V ⊤ (fun x ↦ homOfLE le_top)
  · intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxV x⟩
  · intro x
    rw [map_zero]
    exact hV x

/-- The Weil divisor of a Cartier divisor is locally principal. -/
theorem isLocallyPrincipal_cartierToWeil [IsIntegral X] [IsNoetherian X]
    (D : X.CartierDivisor) :
    WeilDivisor.IsLocallyPrincipal (cartierToWeil D) := by
  intro x
  obtain ⟨⟨U, f⟩, hxU, hf⟩ := D.exists_local_representative x
  exact ⟨U, hxU, totalQuotientUnitsEquivFunctionField U (genericPoint_mem_opens_of_mem hxU) f,
    fun y hy ↦ (cartierToWeil_apply D f hf hy).trans rfl⟩

/-- On a normal integral Noetherian scheme, every locally principal Weil divisor comes from a
Cartier divisor. -/
theorem exists_cartierToWeil_eq_of_isLocallyPrincipal [IsIntegral X] [IsNoetherian X]
    [Hartshorne.IsNormal X] (W : X.WeilDivisor)
    (hW : WeilDivisor.IsLocallyPrincipal W) : ∃ D : X.CartierDivisor, cartierToWeil D = W := by
  classical
  choose V hxV k hk using hW
  let f : ∀ x, X.totalQuotientUnitsSheaf.obj.obj (op (V x)) := fun x ↦
    (totalQuotientUnitsEquivFunctionField (V x) (genericPoint_mem_opens_of_mem (hxV x))).symm (k x)
  have hf : ∀ x, totalQuotientUnitsEquivFunctionField (V x)
      (genericPoint_mem_opens_of_mem (hxV x)) (f x) = k x := fun x ↦
    MulEquiv.apply_symm_apply _ _
  have htrans : ∀ i j, ∃ a : X.structureUnitsSheaf.obj.obj (op (V i ⊓ V j)),
      X.structureUnitsToTotalQuotientUnits.hom.app (op (V i ⊓ V j)) a =
        X.totalQuotientUnitsSheaf.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (f i) /
          X.totalQuotientUnitsSheaf.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
            (f j) := by
    intro i j
    by_cases hη : genericPoint X ∈ V i ⊓ V j
    · have : Nonempty (V i ⊓ V j : X.Opens) := ⟨⟨_, hη⟩⟩
      obtain ⟨a, ha⟩ := exists_unit_germToFunctionField_eq_of_ord_eq_zero (V := V i ⊓ V j)
        (k i / k j)
        fun y hy _ ↦ by
          rw [Units.val_div_eq_div_val, div_eq_mul_inv, ord_mul (Units.ne_zero _)
            (inv_ne_zero (Units.ne_zero _)), ord_inv_eq_neg (Units.ne_zero _),
            ← hk i y hy.1, ← hk j y hy.2, add_neg_cancel]
      refine ⟨a, ?_⟩
      apply (totalQuotientUnitsEquivFunctionField _ hη).injective
      rw [map_div, totalQuotientUnitsEquivFunctionField_map,
        totalQuotientUnitsEquivFunctionField_map, hf i, hf j]
      ext
      rw [totalQuotientUnitsEquivFunctionField_structureUnits _ hη a]
      exact ha
    · have hbot := opens_eq_bot_of_genericPoint_notMem hη
      have : Subsingleton (X.totalQuotientSheaf.obj.obj (op (V i ⊓ V j))) :=
        CommRingCat.subsingleton_of_isTerminal (X.totalQuotientSheaf.isTerminalOfEqEmpty hbot)
      exact ⟨1, Subsingleton.elim (α := (X.totalQuotientSheaf.obj.obj (op (V i ⊓ V j)))ˣ)
        _ _⟩
  let sec : ∀ x, X.cartierDivisorSheaf.obj.obj (op (V x)) := fun x ↦
    X.toCartierDivisorSheaf.hom.app (op (V x)) (Additive.ofMul (f x))
  have hcompat : TopCat.Presheaf.IsCompatible X.cartierDivisorSheaf.obj V sec := by
    intro i j
    obtain ⟨a, ha⟩ := htrans i j
    have hmul : X.totalQuotientUnitsSheaf.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
        (f i) = X.structureUnitsToTotalQuotientUnits.hom.app (op (V i ⊓ V j)) a *
          X.totalQuotientUnitsSheaf.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
            (f j) := by
      rw [ha, div_mul_cancel]
    change X.cartierDivisorSheaf.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (sec i) =
      X.cartierDivisorSheaf.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (sec j)
    simp only [sec]
    rw [toCartierDivisorSheaf_naturality_apply, toCartierDivisorSheaf_naturality_apply, hmul]
    have hadd := map_add (ConcreteCategory.hom (X.toCartierDivisorSheaf.hom.app (op (V i ⊓ V j))))
      (Additive.ofMul (X.structureUnitsToTotalQuotientUnits.hom.app (op (V i ⊓ V j)) a))
      (Additive.ofMul (X.totalQuotientUnitsSheaf.obj.map
        (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (f j)))
    exact hadd.trans ((congrArg (· + _) (toCartierDivisorSheaf_structureUnits _ a)).trans
      (zero_add _))
  obtain ⟨D, hD, -⟩ : ∃! D : X.CartierDivisor, ∀ x, D.restrict (V x) = sec x :=
    X.cartierDivisorSheaf.existsUnique_gluing' V ⊤ (fun x ↦ homOfLE le_top)
      (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxV x⟩) sec hcompat
  refine ⟨D, Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)⟩
  have hrep : D.restrict (V y) =
      X.toCartierDivisorSheaf.hom.app (op (V y)) (Additive.ofMul (f y)) := hD y
  refine (cartierToWeil_apply D (f y) hrep (hxV y)).trans ?_
  rw [hf y]
  exact (hk y y (hxV y)).symm


/-- The height of the prime ideal of a point of an affine open set is the coheight of the
point. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.height_primeIdealOf {V : X.Opens}
    (hV : IsAffineOpen V) (z : V) :
    ((hV.primeIdealOf z).asIdeal.height : WithBot ℕ∞) = coheight z.1 := by
  have := hV.isLocalization_stalk z
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf z).asIdeal
    (X.presheaf.stalk z.1), ringKrullDim_stalk_eq_coheight]

/-- If `y` specializes to `x` in an affine open set, the prime ideal of `y` is contained in that
of `x`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.primeIdealOf_le_of_specializes {V : X.Opens}
    (hV : IsAffineOpen V) {y x : V} (h : (y : X) ⤳ x) :
    (hV.primeIdealOf y).asIdeal ≤ (hV.primeIdealOf x).asIdeal := by
  change hV.primeIdealOf y ≤ hV.primeIdealOf x
  rw [PrimeSpectrum.le_iff_specializes]
  exact (subtype_specializes_iff y x |>.mpr h).map (hV.isoSpec.hom.continuous)

theorem _root_.AlgebraicGeometry.IsAffineOpen.primeIdealOf_injective {V : X.Opens}
    (hV : IsAffineOpen V) :
    Function.Injective hV.primeIdealOf := by
  intro y z h
  apply Subtype.ext
  rw [← hV.fromSpec_primeIdealOf y, ← hV.fromSpec_primeIdealOf z, h]

open Classical Hartshorne in
/-- On a locally factorial scheme satisfying `(*)`, a prime divisor with generic point `y` through a
point `x` has a local equation near `x`: a rational function of order one at `y` and order zero
at every other codimension-one point of a neighbourhood of `x`. -/
theorem exists_local_uniformizer [IsIntegral X] [IsNoetherian X]
    (hX : X.SatisfiesConditionStar) (hlf : X.IsLocallyFactorial) {x y : X}
    (hy : coheight y = 1) (hyx : y ⤳ x) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ a : X.functionFieldˣ, ∀ z ∈ U, coheight z = 1 →
      X.ord (a : X.functionField) z = if z = y then 1 else 0 := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyV : y ∈ V := hyx.mem_open V.isOpen hxV
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  set q := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal with hq
  set m := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal with hm
  have hqm : q ≤ m := hV.primeIdealOf_le_of_specializes hyx
  have hqh : q.height = 1 := by
    have h := hV.height_primeIdealOf ⟨y, hyV⟩
    rw [hy] at h
    exact_mod_cast h
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) m := hV.isLocalization_stalk ⟨x, hxV⟩
  obtain ⟨hdom, hufd⟩ := hlf x
  have hdisj : Disjoint (m.primeCompl : Set Γ(X, V)) q := by
    rw [Set.disjoint_left]
    intro a ha haq
    exact ha (hqm haq)
  set P := q.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) with hP
  have : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ q
    inferInstance hdisj
  have hPh : P.height = 1 := by
    rw [hP, IsLocalization.height_map_of_disjoint m.primeCompl q hdisj, hqh]
  obtain ⟨g, hg⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hPh
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl g
  have hPb : P = Ideal.span {algebraMap Γ(X, V) (X.presheaf.stalk x) b} := by
    rw [hg]
    change Ideal.span _ = _
    rw [Ideal.span_singleton_eq_span_singleton]
    exact ⟨(IsLocalization.map_units (X.presheaf.stalk x) t).unit,
      IsLocalization.mk'_spec (X.presheaf.stalk x) b t⟩
  have hbq : b ∈ q := by
    have hmem : algebraMap Γ(X, V) (X.presheaf.stalk x) b ∈ P := by
      rw [hPb]
      exact Ideal.mem_span_singleton_self _
    rw [hP] at hmem
    have := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl (X.presheaf.stalk x)
      (I := q) inferInstance hdisj
    rw [← this]
    exact hmem
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, Ideal.span_singleton_eq_bot.mpr rfl] at hPb
    rw [hPb, Ideal.height_bot] at hPh
    exact zero_ne_one hPh
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian q : q.FG)
  have hloc : ∀ c ∈ G, ∃ s ∈ m.primeCompl, s * c ∈ Ideal.span {b} := by
    intro c hc
    have hcq : c ∈ q := hG ▸ Submodule.subset_span hc
    have hcP : algebraMap Γ(X, V) (X.presheaf.stalk x) c ∈ P := Ideal.mem_map_of_mem _ hcq
    rw [hPb, Ideal.mem_span_singleton'] at hcP
    obtain ⟨r, hr⟩ := hcP
    obtain ⟨⟨e, u⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl r
    have h1 : algebraMap Γ(X, V) (X.presheaf.stalk x) (e * b) =
        algebraMap Γ(X, V) (X.presheaf.stalk x) (u * c) := by
      rw [map_mul, map_mul, ← hr, ← mul_assoc, mul_comm (algebraMap _ _ (u : Γ(X, V))),
        IsLocalization.mk'_spec]
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists m.primeCompl (X.presheaf.stalk x)).1 h1
    refine ⟨w * u, m.primeCompl.mul_mem w.2 u.2, ?_⟩
    rw [Ideal.mem_span_singleton']
    exact ⟨w * e, by rw [mul_assoc, hw, ← mul_assoc]⟩
  choose! sc hsc hsc' using hloc
  set s : Γ(X, V) := ∏ c ∈ G, sc c with hs
  have hsm : s ∈ m.primeCompl := m.primeCompl.prod_mem fun c hc ↦ hsc c hc
  have hsq : ∀ c ∈ q, s * c ∈ Ideal.span {b} := by
    have hle : q ≤ Submodule.comap (LinearMap.mulLeft Γ(X, V) s) (Ideal.span {b}) := by
      rw [← hG, Submodule.span_le]
      intro c hc
      change s * c ∈ Ideal.span {b}
      rw [hs, ← Finset.prod_erase_mul _ _ hc, mul_assoc]
      exact Ideal.mul_mem_left _ _ (hsc' c hc)
    exact fun c hc ↦ hle hc
  have hxU : x ∈ X.basicOpen s := by
    rw [X.mem_basicOpen s x hxV]
    exact IsLocalization.map_units (X.presheaf.stalk x) (⟨s, hsm⟩ : m.primeCompl)
  have hbK : X.germToFunctionField V b ≠ 0 := fun h ↦
    hb0 (X.germToFunctionField_injective V (h.trans (map_zero _).symm))
  refine ⟨X.basicOpen s, hxU, Units.mk0 _ hbK, fun z hzU hz ↦ ?_⟩
  have hzV : z ∈ V := X.basicOpen_le s hzU
  set qz := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal with hqz
  let _ : Algebra Γ(X, V) (X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk z) qz := hV.isLocalization_stalk ⟨z, hzV⟩
  have : IsDiscreteValuationRing (X.presheaf.stalk z) :=
    X.codimensionOneStalk_isDiscreteValuationRing hX hz
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk z) X.functionField :=
    functionField_isScalarTower X V ⟨z, hzV⟩
  have hsz : s ∉ qz := by
    have hu := (X.mem_basicOpen s z hzV).1 hzU
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z) qz s).1 hu
  have hqzh : qz.height = 1 := by
    have h := hV.height_primeIdealOf ⟨z, hzV⟩
    rw [hz] at h
    exact_mod_cast h
  rw [Units.val_mk0]
  split_ifs with hzy
  · subst hzy
    rw [ord_eq_iff hz hbK]
    change Ring.ordFrac (X.presheaf.stalk z) (algebraMap Γ(X, V) X.functionField b) = _
    have hmax : qz.map (algebraMap Γ(X, V) (X.presheaf.stalk z)) =
        Ideal.span {algebraMap Γ(X, V) (X.presheaf.stalk z) b} := by
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro c hc
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (hsq c hc)
        have hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk z) s) :=
          (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z) qz s).2 hsz
        rw [Ideal.mem_comap, Ideal.mem_span_singleton']
        refine ⟨hu.unit⁻¹ * algebraMap Γ(X, V) (X.presheaf.stalk z) d, ?_⟩
        rw [mul_assoc, ← map_mul, hd, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.mem_map_of_mem _ hbq
    rw [IsScalarTower.algebraMap_apply Γ(X, V) (X.presheaf.stalk z) X.functionField]
    apply Ring.ordFrac_irreducible
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal qz (X.presheaf.stalk z), hmax]
  · rw [ord_eq_iff hz hbK]
    change Ring.ordFrac (X.presheaf.stalk z) (algebraMap Γ(X, V) X.functionField b) = _
    rw [ofAdd_zero, WithZero.coe_one,
      ordFrac_algebraMap_eq_one_iff_notMem_of_isLocalizationAtPrime
        (R := X.presheaf.stalk z) (K := X.functionField) qz b]
    intro hbz
    have hle : q ≤ qz := by
      intro c hc
      have hsc : s * c ∈ qz := by
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (hsq c hc)
        rw [← hd]
        exact Ideal.mul_mem_left _ _ hbz
      exact ((inferInstance : qz.IsPrime).mem_or_mem hsc).resolve_left hsz
    have : q.FiniteHeight := ⟨Or.inr (by rw [hqh]; exact ENat.one_ne_top)⟩
    have heq : q = qz := Ideal.eq_of_le_of_height_le (I := q) (J := qz) hle
      (by rw [hqh, hqzh])
    apply hzy
    have := hV.primeIdealOf_injective (PrimeSpectrum.ext heq.symm)
    exact congrArg Subtype.val this

/-- Membership in a finite intersection of open sets. -/
theorem mem_finset_inf_opens {ι : Type*} (s : Finset ι) (f : ι → X.Opens) (x : X) :
    x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  rw [← SetLike.mem_coe, Opens.coe_finset_inf, Finset.inf_eq_iInf]
  simp

/-- The order of vanishing at a point as a homomorphism on the units of the function field. -/
def ordUnitsHom [IsIntegral X] [IsNoetherian X] (z : X) :
    X.functionFieldˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (X.ord (u : X.functionField) z)
  map_one' := by
    have h := X.ord_mul (x := z) (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at h
    rw [Units.val_one, show X.ord (1 : X.functionField) z = 0 by omega, ofAdd_zero]
  map_mul' u v := by
    rw [Units.val_mul, ord_mul u.ne_zero v.ne_zero, ofAdd_add]

/-- On a locally factorial scheme satisfying `(*)`, every Weil divisor is locally principal: near
a point `x`, the divisor agrees with the product of the local uniformizers of the prime divisors
through `x`, raised to the coefficients. -/
theorem isLocallyPrincipal_of_isLocallyFactorial_of_satisfiesConditionStar [IsIntegral X]
    [IsNoetherian X] (hX : X.SatisfiesConditionStar) (hlf : X.IsLocallyFactorial)
    (W : X.WeilDivisor) : WeilDivisor.IsLocallyPrincipal W := by
  classical
  intro x
  have hfin : W.1.support.Finite := WeilDivisor.support_finite W
  set T := hfin.toFinset with hT
  set Tx := T.filter (fun y ↦ y ⤳ x) with hTx
  have hcoh : ∀ y ∈ T, coheight y = 1 := by
    intro y hy
    by_contra h
    exact (hfin.mem_toFinset.mp hy) (W.2 y h)
  have hP : ∀ y ∈ Tx, ∃ U : X.Opens, x ∈ U ∧ ∃ a : X.functionFieldˣ, ∀ z ∈ U,
      coheight z = 1 → X.ord (a : X.functionField) z = if z = y then 1 else 0 := by
    intro y hy
    rw [Finset.mem_filter] at hy
    exact exists_local_uniformizer hX hlf (hcoh y hy.1) hy.2
  choose! U hxU a ha using hP
  let C : X → X.Opens := fun y ↦ ⟨(closure {y})ᶜ, isClosed_closure.isOpen_compl⟩
  let U' : X.Opens := Tx.inf U ⊓ (T.filter (fun y ↦ ¬ y ⤳ x)).inf C
  refine ⟨U', ⟨(mem_finset_inf_opens _ _ _).2 fun y hy ↦ hxU y hy,
    (mem_finset_inf_opens _ _ _).2 fun y hy ↦ ?_⟩, ∏ y ∈ Tx, a y ^ W.1 y, fun z hz ↦ ?_⟩
  · rw [Finset.mem_filter] at hy
    change x ∉ closure {y}
    rw [← specializes_iff_mem_closure]
    exact hy.2
  by_cases hz1 : coheight z = 1
  · have hord : X.ord ((∏ y ∈ Tx, a y ^ W.1 y : X.functionFieldˣ) : X.functionField) z =
        ∑ y ∈ Tx, W.1 y * X.ord (a y : X.functionField) z := by
      have := congrArg Multiplicative.toAdd (map_prod (ordUnitsHom z) (fun y ↦ a y ^ W.1 y) Tx)
      simp only [map_zpow, toAdd_prod, toAdd_zpow] at this
      exact this
    rw [hord]
    have hU : ∀ y ∈ Tx, z ∈ U y := (mem_finset_inf_opens _ _ _).1 hz.1
    rw [Finset.sum_congr rfl fun y hy ↦ by rw [ha y hy z (hU y hy) hz1]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hzT
    · rfl
    · by_contra hW
      have hzT' : z ∈ T := hfin.mem_toFinset.mpr hW
      have hzx : ¬ z ⤳ x := fun h ↦ hzT (Finset.mem_filter.mpr ⟨hzT', h⟩)
      have := (mem_finset_inf_opens _ _ _).1 hz.2 z (Finset.mem_filter.mpr ⟨hzT', hzx⟩)
      exact this (subset_closure rfl)
  · rw [W.2 z hz1, ord_eq_zero_of_coheight_neq_one hz1]


section LocallyFactorial

/-- A locally factorial scheme is normal. -/
theorem isNormal_of_isLocallyFactorial (hlf : X.IsLocallyFactorial) : Hartshorne.IsNormal X where
  isDomain_stalk x := (hlf x).1
  isIntegrallyClosed_stalk x := by
    have := (hlf x).1
    have := (hlf x).2
    infer_instance

/-- An integral separated Noetherian locally factorial scheme satisfies condition `(*)`. -/
theorem satisfiesConditionStar_of_isLocallyFactorial [IsIntegral X] [IsNoetherian X]
    [X.IsSeparated] (hlf : X.IsLocallyFactorial) : X.SatisfiesConditionStar :=
  @Hartshorne.satisfiesConditionStar_of_isNormal X _ _ _ (isNormal_of_isLocallyFactorial hlf)

/-- On an integral separated Noetherian locally factorial scheme, every Weil divisor is locally
principal. -/
theorem isLocallyPrincipal_of_isLocallyFactorial [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (hlf : X.IsLocallyFactorial) (W : X.WeilDivisor) : WeilDivisor.IsLocallyPrincipal W :=
  isLocallyPrincipal_of_isLocallyFactorial_of_satisfiesConditionStar
    (satisfiesConditionStar_of_isLocallyFactorial hlf) hlf W

/-- **Hartshorne II.6, Proposition 6.11.** On an integral separated Noetherian locally factorial
scheme, Weil divisors and Cartier divisors are identified; the inverse equivalence is the Weil
divisor of a Cartier divisor, `cartierToWeil`. -/
def weilCartierEquiv [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (hlf : X.IsLocallyFactorial) : X.WeilDivisor ≃+ X.CartierDivisor :=
  have := isNormal_of_isLocallyFactorial hlf
  (AddEquiv.ofBijective (cartierToWeil (X := X))
    ⟨cartierToWeil_injective, fun W ↦ exists_cartierToWeil_eq_of_isLocallyPrincipal W
      (isLocallyPrincipal_of_isLocallyFactorial hlf W)⟩).symm

/-- The inverse of `weilCartierEquiv` sends a Cartier divisor to its Weil divisor. -/
theorem weilCartierEquiv_symm_apply [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (hlf : X.IsLocallyFactorial) (D : X.CartierDivisor) :
    (weilCartierEquiv hlf).symm D = cartierToWeil D :=
  rfl

/-- Under `weilCartierEquiv`, the principal Weil divisor of `f ∈ K(X)^*` corresponds to the
principal Cartier divisor of `f`, viewed as a global section of `K_X^*`. -/
theorem weilCartierEquiv_principalDivisor [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (hlf : X.IsLocallyFactorial) (f : X.functionFieldˣ) :
    weilCartierEquiv hlf (X.principalDivisor (satisfiesConditionStar_of_isLocallyFactorial hlf) f) =
      X.principalCartierDivisor ((totalQuotientUnitsEquivFunctionField ⊤ trivial).symm f) := by
  apply (weilCartierEquiv hlf).symm.injective
  rw [AddEquiv.symm_apply_apply, weilCartierEquiv_symm_apply,
    cartierToWeil_principalCartierDivisor (satisfiesConditionStar_of_isLocallyFactorial hlf),
    MulEquiv.apply_symm_apply]

/-- Under `weilCartierEquiv`, the subgroup of principal Weil divisors corresponds to the subgroup
of principal Cartier divisors. -/
theorem map_principalDivisorSubgroup_weilCartierEquiv [IsIntegral X] [IsNoetherian X]
    [X.IsSeparated] (hlf : X.IsLocallyFactorial) :
    (X.principalDivisorSubgroup (satisfiesConditionStar_of_isLocallyFactorial hlf)).map
        (weilCartierEquiv hlf).toAddMonoidHom =
      X.principalCartierDivisorSubgroup := by
  ext D
  constructor
  · rintro ⟨W, ⟨f, rfl⟩, rfl⟩
    refine ⟨Additive.ofMul ((totalQuotientUnitsEquivFunctionField ⊤ trivial).symm f.toMul), ?_⟩
    exact (weilCartierEquiv_principalDivisor hlf f.toMul).symm
  · rintro ⟨F, rfl⟩
    refine ⟨X.principalDivisor (satisfiesConditionStar_of_isLocallyFactorial hlf)
      (totalQuotientUnitsEquivFunctionField ⊤ trivial F.toMul),
      ⟨Additive.ofMul _, rfl⟩, ?_⟩
    change weilCartierEquiv hlf _ = X.principalCartierDivisor F.toMul
    rw [weilCartierEquiv_principalDivisor, MulEquiv.symm_apply_apply]

end LocallyFactorial

section Normal

variable (X) [IsIntegral X] [IsNoetherian X] [Hartshorne.IsNormal X]

/-- The subgroup of locally principal Weil divisors on a normal integral Noetherian scheme. -/
def locallyPrincipalWeilDivisors : AddSubgroup X.WeilDivisor :=
  (cartierToWeil (X := X)).range.copy
    {W | WeilDivisor.IsLocallyPrincipal W} (Set.ext fun W ↦
      ⟨fun hW ↦ exists_cartierToWeil_eq_of_isLocallyPrincipal W hW, by
        rintro ⟨D, rfl⟩
        exact isLocallyPrincipal_cartierToWeil D⟩)

variable {X} in
theorem mem_locallyPrincipalWeilDivisors (W : X.WeilDivisor) :
    W ∈ X.locallyPrincipalWeilDivisors ↔ WeilDivisor.IsLocallyPrincipal W :=
  Iff.rfl

/-- **Hartshorne II.6, Remark 6.11.2.** On a normal integral Noetherian scheme, the Weil divisor of
a Cartier divisor identifies Cartier divisors with locally principal Weil divisors. -/
def cartierEquivLocallyPrincipal : X.CartierDivisor ≃+ X.locallyPrincipalWeilDivisors :=
  (AddMonoidHom.ofInjective (cartierToWeil_injective (X := X))).trans
    (AddEquiv.addSubgroupCongr (AddSubgroup.copy_eq _ _ _).symm)

variable {X} in
/-- The identification of Remark 6.11.2 is the Weil divisor of a Cartier divisor. -/
theorem coe_cartierEquivLocallyPrincipal (D : X.CartierDivisor) :
    (cartierEquivLocallyPrincipal X D : X.WeilDivisor) = cartierToWeil D :=
  rfl

end Normal

end

end AlgebraicGeometry.Scheme
