/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.AffineNormalizationSpec
import Hartshorne.Intersection.NormalizationLocalOrder
import Hartshorne.Intersection.RationalEquivalenceLocalization
import Hartshorne.Scheme.AffineLineClassGroup

/-!
# Orders on the normalization pushed forward are orders on the variety

Let `ν : W ⟶ V` be a morphism of locally Noetherian integral schemes sending the generic point to
the generic point, and `y ∈ V`. We say that the *fibre order formula* holds at `y`
(`FibreOrdFormula`) if for every nonzero rational function `g` on `V`,
`∑_{ν(z) = y} ord_z(ν^♯ g) [κ(z) : κ(y)] = ord_y(g)`, where orders are Mathlib's length-based
orders of vanishing. The formula is transported along open immersions
(`FibreOrdFormula.of_isOpenImmersion`).

For a Noetherian domain `D` whose integral closure `O` in its fraction field is finite over `D`,
the formula holds for `Spec O ⟶ Spec D` at every point of codimension one
(`fibreOrdFormula_specMap_integralClosure`): this is the length formula for orders through the
normalization, in the form `Hartshorne.NormalizationLocalOrder.length_quotient_eq_finsum_primesOver`.
Covering a variety by affine opens, the formula holds for the normalization of any integral
scheme of finite type over a field at every point of codimension one
(`fibreOrdFormula_absoluteNormalizationMap`). Equivalently, the pushforward along the
normalization of the principal divisor of `g` has coefficient `ord_y(g)` at `y`.
-/

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Order

namespace Hartshorne

section General

/-- The order of vanishing of the image of a nonzero element of a codimension-one stalk is the
length of the quotient of the stalk by it. -/
theorem Scheme.ord_algebraMap_stalk {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {x : X} (hx : coheight x = 1) {s : X.presheaf.stalk x} (hs : s ≠ 0) :
    X.ord (algebraMap _ X.functionField s) x = (Ring.ord (X.presheaf.stalk x) s).toNat := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hnz : s ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero hs
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  rw [Scheme.ord_eq_iff hx (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hnz), ← hm,
    ENat.toNat_natCast]
  unfold Scheme.ordHom
  rw [Ring.ordFrac_eq_ord _ hs]
  simp [Ring.ordMonoidWithZeroHom, ← hm, hs]

/-- A dominant morphism of integral schemes maps the generic point to the generic point. -/
theorem Scheme.Hom.apply_genericPoint_of_isDominant {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y)
  change closure _ = _
  apply Set.eq_univ_of_univ_subset
  rw [← f.denseRange.closure_eq]
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ closure ({genericPoint X} : Set X) := by
    rw [(genericPoint_spec X).def]
    trivial
  have := image_closure_subset_closure_image f.base.hom.continuous ⟨z, hz, rfl⟩
  rwa [Set.image_singleton] at this

end General

section FibreOrdFormula

variable {W V : Scheme.{u}} [IsIntegral W] [IsIntegral V] [IsLocallyNoetherian W]
  [IsLocallyNoetherian V]

/-- The fibre order formula for `ν : W ⟶ V` at `y`: for every nonzero rational function `g` on
`V`, `∑_{ν(z) = y} ord_z(ν^♯ g) [κ(z) : κ(y)] = ord_y(g)`. -/
def FibreOrdFormula (ν : W ⟶ V) (hν : ν (genericPoint W) = genericPoint V) (y : V) : Prop :=
  ∀ g : V.functionField, g ≠ 0 →
    ∑ᶠ z ∈ ν ⁻¹' {y}, W.ord (ν.genericFunctionFieldMap hν g) z * (ν.residueDegree z : ℤ) =
      V.ord g y

/-- The fibre order formula is transported along open immersions `a : W' ⟶ W`, `b : V' ⟶ V`
with `a ≫ ν = ν' ≫ b`, provided the fibre of `ν` over `b(y')` lies in the image of `a`. -/
theorem FibreOrdFormula.of_isOpenImmersion {W' V' : Scheme.{u}} [IsIntegral W'] [IsIntegral V']
    [IsLocallyNoetherian W'] [IsLocallyNoetherian V'] {ν : W ⟶ V} {ν' : W' ⟶ V'}
    (a : W' ⟶ W) (b : V' ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b] (hsq : a ≫ ν = ν' ≫ b)
    (hν : ν (genericPoint W) = genericPoint V) (hν' : ν' (genericPoint W') = genericPoint V')
    {y' : V'} (hfib : ν ⁻¹' {b y'} ⊆ Set.range a) (h : FibreOrdFormula ν' hν' y') :
    FibreOrdFormula ν hν (b y') := by
  intro g hg
  have ha := genericPoint_eq_of_isOpenImmersion a
  have hb := genericPoint_eq_of_isOpenImmersion b
  let g' := b.genericFunctionFieldMap hb g
  have hg' : g' ≠ 0 := (map_ne_zero_iff _ (b.genericFunctionFieldMap hb).hom.injective).mpr hg
  have hcomp : ν'.genericFunctionFieldMap hν' g' =
      a.genericFunctionFieldMap ha (ν.genericFunctionFieldMap hν g) := by
    have hab : (a ≫ ν).base (genericPoint W') = genericPoint V := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app, ha, hν]
    have h1 := Scheme.Hom.genericFunctionFieldMap_comp a ν ha hν hab
    have h2 := Scheme.Hom.genericFunctionFieldMap_comp ν' b hν' hb (by rw [← hsq]; exact hab)
    rw [Scheme.Hom.genericFunctionFieldMap_congr hsq hab (by rw [← hsq]; exact hab), h2] at h1
    exact (ConcreteCategory.congr_hom h1 g).trans rfl
  have hord : V'.ord g' y' = V.ord g (b y') :=
    ord_functionFieldIsoOfIsOpenImmersion_hom b g y'
  rw [← hord, ← h g' hg']
  symm
  refine finsum_mem_eq_of_bijOn a ⟨?_, ?_, ?_⟩ ?_
  · intro z hz
    change ν (a z) = b y'
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, show ν' z = y' from hz]
  · exact a.isOpenEmbedding.injective.injOn
  · intro z hz
    obtain ⟨z', rfl⟩ := hfib hz
    refine ⟨z', ?_, rfl⟩
    apply b.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
    exact hz
  · intro z _
    have e1 : W'.ord (a.genericFunctionFieldMap ha (ν.genericFunctionFieldMap hν g)) z =
        W.ord (ν.genericFunctionFieldMap hν g) (a z) :=
      ord_functionFieldIsoOfIsOpenImmersion_hom a _ z
    rw [hcomp, e1]
    congr 2
    have h1 := residueDegree_comp a ν z
    have h2 := residueDegree_comp ν' b z
    rw [residueDegree_eq_one_of_isOpenImmersion a z, mul_one] at h1
    rw [residueDegree_eq_one_of_isOpenImmersion b (ν' z), one_mul] at h2
    rw [← h2, ← hsq, h1]

end FibreOrdFormula

end Hartshorne
