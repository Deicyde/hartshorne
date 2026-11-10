/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.WeilDivisor
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Principal Weil divisors

Hartshorne, *Algebraic Geometry*, II.6, Lemma 6.1 and the following
definition (p. 131).

The section `OrdTransport` and the function-field isomorphism
`Hartshorne.functionFieldIsoOfIsOpenImmersion` of an open immersion of integral schemes record
that orders of vanishing are invariant under isomorphisms of codimension-one stalks and under open
immersions (`Hartshorne.ord_functionFieldIsoOfIsOpenImmersion_hom`).
-/

noncomputable section

open Filter Set TopologicalSpace

namespace AlgebraicGeometry

universe u

private theorem finite_codimensionOne_compl
    {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
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

/-- **Hartshorne II.6, Lemma 6.1.** A nonzero rational function has nonzero
order at only finitely many codimension-one points. -/
theorem Scheme.finite_support_ord_of_satisfiesConditionStar
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    ∀ {f : X.functionField}, f ≠ 0 →
      (Function.support fun x : X ↦ X.ord f x).Finite := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  intro f hf
  obtain ⟨U, _, fU, hU, hUf, hfU⟩ := exists_isUnit_germ_eq X f hf
  let _ : Nonempty U := hU
  refine (finite_codimensionOne_compl U).subset ?_
  intro x hx
  change X.ord f x ≠ 0 at hx
  constructor
  · by_contra hcodim
    exact hx (X.ord_eq_zero_of_coheight_neq_one hcodim f)
  · intro hxU
    apply hx
    rw [← hUf]
    exact X.ord_of_isUnit hfU hxU

private noncomputable def principalDivisorOfNonzero
    {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    (hX : X.SatisfiesConditionStar) (f : X.functionField) (hf : f ≠ 0) :
    X.WeilDivisor := by
  let coeff : X → ℤ := fun x ↦ X.ord f x
  have hfin : coeff.support.Finite :=
    X.finite_support_ord_of_satisfiesConditionStar hX hf
  let D : AlgebraicCycle X ℤ :=
    { toFun := coeff
      supportWithinDomain' := subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ ↦
        ⟨Set.univ, univ_mem, by simpa [coeff] using hfin⟩ }
  refine ⟨D, ?_⟩
  intro x hx
  exact X.ord_eq_zero_of_coheight_neq_one hx f

/-- The principal Weil divisor of a nonzero rational function, represented as
a unit of the function field. -/
noncomputable def Scheme.principalDivisor
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    X.functionFieldˣ → X.WeilDivisor := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  exact fun f ↦ principalDivisorOfNonzero hX f f.ne_zero

@[simp]
theorem Scheme.principalDivisor_apply
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    ∀ (f : X.functionFieldˣ) (x : X),
      (X.principalDivisor hX f).1 x = X.ord (f : X.functionField) x := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  intro f x
  rfl

/-- Principal divisors define a homomorphism from the multiplicative group of
the function field, written additively, to the Weil divisor group. -/
noncomputable def Scheme.principalDivisorHom
    {X : Scheme.{u}} (hX : X.SatisfiesConditionStar) :
    let _ : IsNoetherian X := hX.isNoetherian
    let _ : IsIntegral X := hX.isIntegral
    Additive X.functionFieldˣ →+ X.WeilDivisor := by
  dsimp only
  let _ : IsNoetherian X := hX.isNoetherian
  let _ : IsIntegral X := hX.isIntegral
  refine
    { toFun := fun f ↦ X.principalDivisor hX f.toMul
      map_zero' := ?_
      map_add' := ?_ }
  · apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    change X.ord (1 : X.functionField) x = 0
    have h := X.ord_mul (x := x) (f := (1 : X.functionField))
      (g := (1 : X.functionField)) one_ne_zero one_ne_zero
    have h' : X.ord (1 : X.functionField) x + 0 =
        X.ord (1 : X.functionField) x + X.ord (1 : X.functionField) x := by
      simpa using h
    have hzero : 0 = X.ord (1 : X.functionField) x :=
      add_left_cancel h'
    exact hzero.symm
  · intro f g
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    change X.ord ((f.toMul * g.toMul : X.functionFieldˣ) : X.functionField) x =
      X.ord (f.toMul : X.functionField) x + X.ord (g.toMul : X.functionField) x
    exact X.ord_mul f.toMul.ne_zero g.toMul.ne_zero

end AlgebraicGeometry

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Order

universe u

section OrdTransport

/-- The order `Ring.ord` (length of `R ⧸ (x)`) is invariant under ring isomorphisms. -/
theorem ring_ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap R S) := e.surjective
  rw [Ring.ord, Ring.ord, ← Module.length_eq_of_surjective (S := R) (R := S)
    (M := S ⧸ Ideal.span {e x}) hsurj]
  let f : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) (fun _ ↦ rfl)
  have hmap : Ideal.span {e x} = (Ideal.span {x}).map f := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  exact ((Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) f
    hmap).toLinearEquiv.length_eq).symm

/-- `Ring.ordMonoidWithZeroHom` is invariant under ring isomorphisms of domains. -/
theorem ordMonoidWithZeroHom_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] (e : R ≃+* S) (x : R) :
    Ring.ordMonoidWithZeroHom S (e x) = Ring.ordMonoidWithZeroHom R x := by
  by_cases hx : x = 0
  · simp [hx]
  have hex : e x ≠ 0 := (map_ne_zero_iff _ e.injective).2 hx
  simp [Ring.ordMonoidWithZeroHom, ring_ord_ringEquiv, mem_nonZeroDivisors_iff_ne_zero, hx, hex]

/-- `Ring.ordFrac` is invariant under a ring isomorphism together with a compatible
isomorphism of fraction fields. -/
theorem ordFrac_ringEquiv {R S K L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [CommRing S] [IsDomain S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra S L] [IsFractionRing S L]
    (e : R ≃+* S) (eK : K ≃+* L) (h : ∀ r, eK (algebraMap R K r) = algebraMap S L (e r))
    (k : K) : Ring.ordFrac S (eK k) = Ring.ordFrac R k := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [map_div₀, h, h, map_div₀, map_div₀]
  by_cases ha : a = 0
  · simp [ha]
  rw [Ring.ordFrac_eq_ord S (K := L) ((map_ne_zero_iff _ e.injective).2 ha),
    Ring.ordFrac_eq_ord R (K := K) ha,
    Ring.ordFrac_eq_ord S (K := L) ((map_ne_zero_iff _ e.injective).2 hb0),
    Ring.ordFrac_eq_ord R (K := K) hb0,
    ordMonoidWithZeroHom_ringEquiv, ordMonoidWithZeroHom_ringEquiv]

end OrdTransport

section OpenImmersion

variable {X Y : Scheme.{u}}

/-- The function field of an integral scheme is identified with that of an integral scheme openly
immersed in it, via the stalk map at the generic point. -/
noncomputable def functionFieldIsoOfIsOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f]
    [IsIntegral X] [IsIntegral Y] : X.functionField ≅ Y.functionField :=
  have : IsIso (X.presheaf.stalkSpecializes
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion f)).specializes) :=
    (X.presheaf.stalkCongr (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion f))).isIso_inv
  asIso (X.presheaf.stalkSpecializes
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion f)).specializes ≫
    f.stalkMap (genericPoint Y))

/-- The function field isomorphism of an open immersion is compatible with its stalk maps. -/
theorem functionFieldIsoOfIsOpenImmersion_hom_algebraMap (f : Y ⟶ X) [IsOpenImmersion f]
    [IsIntegral X] [IsIntegral Y] (y : Y) (r : X.presheaf.stalk (f y)) :
    (functionFieldIsoOfIsOpenImmersion f).hom
        (algebraMap (X.presheaf.stalk (f y)) X.functionField r) =
      algebraMap (Y.presheaf.stalk y) Y.functionField (f.stalkMap y r) := by
  have key : X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ _) :
        genericPoint X ⤳ f y) ≫ (functionFieldIsoOfIsOpenImmersion f).hom =
      f.stalkMap y ≫ Y.presheaf.stalkSpecializes
        ((genericPoint_spec Y).specializes (Set.mem_univ _)) := by
    rw [functionFieldIsoOfIsOpenImmersion, asIso_hom,
      TopCat.Presheaf.stalkSpecializes_comp_assoc, Scheme.Hom.stalkSpecializes_stalkMap]
  exact ConcreteCategory.congr_hom key r

/-- The order of vanishing at a point of an integral scheme openly immersed in `X` agrees with
the order of vanishing at its image, under the function field isomorphism. -/
theorem ord_functionFieldIsoOfIsOpenImmersion_hom (f : Y ⟶ X) [IsOpenImmersion f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (g : X.functionField) (y : Y) :
    Scheme.ord ((functionFieldIsoOfIsOpenImmersion f).hom g) y = Scheme.ord g (f y) := by
  by_cases hy : coheight y = 1
  · have hy' : coheight (f y) = 1 := (coheight_eq_of_isOpenImmersion f).trans hy
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hy, Scheme.ord_eq_ordHom_of_coheight_eq_one hy']
    congr 2
    unfold Scheme.ordHom
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (f y)) := krullDimLE_of_coheight_le hy'.le
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
    exact ordFrac_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
      (functionFieldIsoOfIsOpenImmersion f).commRingCatIsoToRingEquiv
      (fun r ↦ functionFieldIsoOfIsOpenImmersion_hom_algebraMap f y r) g
  · have hy' : coheight (f y) ≠ 1 := by rwa [coheight_eq_of_isOpenImmersion]
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hy, Scheme.ord_eq_zero_of_coheight_neq_one hy']

end OpenImmersion

end Hartshorne
