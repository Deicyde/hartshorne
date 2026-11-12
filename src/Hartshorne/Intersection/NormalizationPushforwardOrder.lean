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

On `Spec`, orders of elements are lengths over the localization (`Spec.ord_algebraMap`), stalk
maps of `Spec S ⟶ Spec R` are the induced local homomorphisms (`Spec.stalkIso_hom_stalkMap`,
`Spec.stalkMap_algebraMap`), and residue degrees are inertia degrees
(`Spec.residueDegree_map_eq_inertiaDeg`). Together with the length formula for orders through the
normalization in the form `Hartshorne.NormalizationLocalOrder.length_quotient_eq_finsum_primesOver`,
these are the inputs for the fibre order formula for `Spec O ⟶ Spec D`, `O` the integral closure
of a Noetherian domain `D`.
-/

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Order

namespace Hartshorne

section General

/-- The order of vanishing of the image of a nonzero element of a codimension-one stalk is the
length of the quotient of the stalk by it. -/
private theorem Scheme.ord_algebraMap_stalk {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
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

section Spec

attribute [local instance] FreeLocusAux.freeLocusStalkAlgebra
  FreeLocusAux.freeLocus_asIdeal_isPrime specStalk_functionField_isScalarTower

/-- The canonical map from `R` to the stalk of `Spec R` at `x` is `Rₓ → 𝒪_{Spec R, x}`
precomposed with `R → Rₓ`. -/
theorem Spec.algebraMap_stalk_eq_stalkIso_inv (R : CommRingCat.{u}) (x : Spec R) (a : R) :
    algebraMap R ((Spec R).presheaf.stalk x) a =
      (Spec.stalkIso R x).inv (algebraMap R (Localization.AtPrime x.asIdeal) a) := by
  have h := ConcreteCategory.congr_hom (Spec.algebraMap_stalkIso_inv (R := R) x) a
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h
  rw [h]
  rfl

/-- On `Spec R` for a Noetherian domain `R`, the order at a codimension-one point `x` of
`a ∈ R ∖ 0` is `ord_{Rₓ}(a)`. -/
theorem Spec.ord_algebraMap (R : CommRingCat.{u}) [IsDomain R] [IsNoetherianRing R]
    {x : Spec R} (hx : coheight x = 1) {a : R} (ha : a ≠ 0) :
    (Spec R).ord (algebraMap R (Spec R).functionField a) x =
      (Ring.ord (Localization.AtPrime x.asIdeal) (algebraMap R _ a)).toNat := by
  have hloc : algebraMap R (Localization.AtPrime x.asIdeal) a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective _ x.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha
  rw [IsScalarTower.algebraMap_apply R ((Spec R).presheaf.stalk x),
    Spec.algebraMap_stalk_eq_stalkIso_inv, Scheme.ord_algebraMap_stalk hx]
  · exact congrArg (fun t : ℕ∞ ↦ ((t.toNat : ℕ) : ℤ))
      (ring_ord_ringEquiv (Spec.stalkIso R x).commRingCatIsoToRingEquiv.symm _)
  · exact (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (Spec.stalkIso R x).inv).1).mpr hloc

/-- Under the identifications `𝒪_{Spec R, x} ≅ Rₓ`, the stalk map of `Spec S ⟶ Spec R` is the
induced local homomorphism. -/
theorem Spec.stalkIso_hom_stalkMap {R S : CommRingCat.{u}} (f : R ⟶ S) (q : PrimeSpectrum S)
    (s : (Spec R).presheaf.stalk (Spec.map f q)) :
    (Spec.stalkIso S q).hom ((Spec.map f).stalkMap q s) =
      Localization.localRingHom (PrimeSpectrum.comap f.hom q).asIdeal q.asIdeal f.hom rfl
        ((Spec.stalkIso R (PrimeSpectrum.comap f.hom q)).hom s) := by
  have h := Scheme.localRingHom_comp_stalkIso_apply f q s
  refine (congrArg (fun t ↦ (Spec.stalkIso S q).hom t) h).symm.trans ?_
  exact Iso.inv_hom_id_apply (Spec.stalkIso S q) _

/-- The residue degree of `Spec O ⟶ Spec D` at `𝔔` is the inertia degree of `𝔔` over `D`. -/
theorem Spec.residueDegree_map_eq_inertiaDeg {D O : Type u} [CommRing D] [CommRing O]
    [Algebra D O] (𝔔 : Spec (.of O)) :
    (Spec.map (CommRingCat.ofHom (algebraMap D O))).residueDegree 𝔔 = 𝔔.asIdeal.inertiaDeg D := by
  let j : CommRingCat.of D ⟶ CommRingCat.of O := CommRingCat.ofHom (algebraMap D O)
  have : 𝔔.asIdeal.IsPrime := 𝔔.isPrime
  let p : Ideal D := 𝔔.asIdeal.under D
  have : p.IsPrime := Ideal.IsPrime.under D 𝔔.asIdeal
  let _ := Localization.AtPrime.algebraOfLiesOver p 𝔔.asIdeal
  rw [Ideal.inertiaDeg_eq p 𝔔.asIdeal, Scheme.Hom.residueDegree]
  let x : Spec (.of D) := PrimeSpectrum.comap j.hom 𝔔
  let i1 := (Scheme.Spec.residueFieldIso (.of D) x).commRingCatIsoToRingEquiv
  let i2 := (Scheme.Spec.residueFieldIso (.of O) 𝔔).commRingCatIsoToRingEquiv
  let _ := ((Spec.map j).residueFieldMap 𝔔).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (S₀ := (Spec (.of O)).residueField 𝔔)
    (R₁ := p.ResidueField) (S₁ := 𝔔.asIdeal.ResidueField) i1 i2 ?_
  ext z
  obtain ⟨s, rfl⟩ := (Spec (.of D)).residue_surjective x z
  change algebraMap p.ResidueField 𝔔.asIdeal.ResidueField (i1 ((Spec (.of D)).residue x s)) =
    i2 (((Spec.map j).residueFieldMap 𝔔) ((Spec (.of D)).residue x s))
  have h1 := ConcreteCategory.congr_hom (Scheme.Spec.residue_residueFieldIso_hom (.of D) x) s
  have h2 : (Spec.map j).residueFieldMap 𝔔 ((Spec (.of D)).residue x s) =
      (Spec (.of O)).residue 𝔔 ((Spec.map j).stalkMap 𝔔 s) :=
    ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap (Spec.map j) 𝔔) s
  have h3 := ConcreteCategory.congr_hom (Scheme.Spec.residue_residueFieldIso_hom (.of O) 𝔔)
    ((Spec.map j).stalkMap 𝔔 s)
  simp only [ConcreteCategory.comp_apply] at h1 h3
  have h4 : (Spec.stalkIso (.of O) 𝔔).hom ((Spec.map j).stalkMap 𝔔 s) =
      Localization.localRingHom x.asIdeal 𝔔.asIdeal j.hom rfl ((Spec.stalkIso (.of D) x).hom s) :=
    Spec.stalkIso_hom_stalkMap j 𝔔 s
  rw [show i1 ((Spec (.of D)).residue x s) = _ from h1, h2, show i2 _ = _ from h3, h4]
  rfl

/-- The stalk map of `Spec S ⟶ Spec R` sends the image of `r ∈ R` to the image of `f(r)`. -/
theorem Spec.stalkMap_algebraMap {R S : CommRingCat.{u}} (f : R ⟶ S) (q : Spec S) (r : R) :
    (Spec.map f).stalkMap q (algebraMap R ((Spec R).presheaf.stalk (Spec.map f q)) r) =
      algebraMap S ((Spec S).presheaf.stalk q) (f r) := by
  apply (ConcreteCategory.bijective_of_isIso (Spec.stalkIso S q).hom).1
  have e1 : algebraMap R ((Spec R).presheaf.stalk (Spec.map f q)) r =
      (Spec.stalkIso R (PrimeSpectrum.comap f.hom q)).inv
        (algebraMap R (Localization.AtPrime (PrimeSpectrum.comap f.hom q).asIdeal) r) :=
    Spec.algebraMap_stalk_eq_stalkIso_inv R _ r
  have e2 := Spec.algebraMap_stalk_eq_stalkIso_inv S q (f r)
  refine (Spec.stalkIso_hom_stalkMap f q _).trans ?_
  calc _ = Localization.localRingHom (PrimeSpectrum.comap f.hom q).asIdeal q.asIdeal f.hom rfl
        (algebraMap R _ r) :=
        congrArg _ ((congrArg _ e1).trans (Iso.inv_hom_id_apply _ _))
    _ = algebraMap S (Localization.AtPrime q.asIdeal) (f.hom r) :=
        Localization.localRingHom_to_map _ _ _ _ _
    _ = _ := ((congrArg _ e2).trans (Iso.inv_hom_id_apply _ _)).symm

/-- Orders of quotients: `ord(f / g) = ord f - ord g` for nonzero `f, g`. -/
theorem Scheme.ord_div {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) (x : X) :
    X.ord (f / g) x = X.ord f x - X.ord g x := by
  have h := Scheme.ord_mul (x := x) (div_ne_zero hf hg) hg
  rw [div_mul_cancel₀ f hg] at h
  omega

end Spec

end Hartshorne
