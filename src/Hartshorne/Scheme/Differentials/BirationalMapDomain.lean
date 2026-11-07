/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CodimensionOneStalkDVR
import Hartshorne.Scheme.Codimension
import Hartshorne.Scheme.Regular
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# The domain of a birational map has codimension-two complement

Hartshorne, *Algebraic Geometry*, II.8, the codimension argument in the proof of
Theorem 8.19 (p. 181).

Let `X` be a nonsingular variety and `X'` a proper variety over a field `k`, and
let `T : X ⤏ X'` be a birational map with maximal domain of definition `V`.
Every point of codimension one of `X` lies in `V`, hence `X \ V` has
codimension at least two.

A variety over `k` is an integral scheme, separated and of finite type over
`Spec k`; a proper variety is moreover proper over `Spec k`. Nonsingularity is
`AlgebraicGeometry.Scheme.IsRegular`. A birational map is a rational map
`T : X ⤏ X'` represented by a partial isomorphism over `Spec k`, and its maximal
domain of definition is Mathlib's `Scheme.RationalMap.domain`, the union of the
domains of all representatives. Codimension is `Hartshorne.codim`; a point of
codimension one is a point whose closure has codimension one.

## Proof

A nonsingular variety satisfies Hartshorne's condition `(*)`, so at a point `x`
of codimension one the stalk `𝒪_{X,x}` is a discrete valuation ring with
fraction field `K(X)`. The rational map gives a `k`-morphism `Spec K(X) ⟶ X'`;
the existence part of the valuative criterion for the proper morphism
`X' ⟶ Spec k` extends it to `Spec 𝒪_{X,x} ⟶ X'`, which spreads out to a
partial map defined at `x` (Mathlib's `Scheme.PartialMap.ofFromSpecStalk`). It
agrees with `T` at the generic point, so it represents `T` and `x ∈ V`. The
generic point lies in the dense open `V`, so every point outside `V` has
coheight at least two, which is the codimension statement.
-/

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace

universe u

/-- The restrictions of a partial map to the local schemes of its domain are
compatible with specialization. -/
private theorem specMap_stalkSpecializes_fromSpecStalkOfMem {X Y : Scheme.{u}}
    (g : X.PartialMap Y) {x y : X} (h : x ⤳ y) (hx : x ∈ g.domain) (hy : y ∈ g.domain) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ g.fromSpecStalkOfMem hy =
      g.fromSpecStalkOfMem hx := by
  simp only [Scheme.PartialMap.fromSpecStalkOfMem, ← Category.assoc]
  congr 1
  rw [← cancel_mono g.domain.ι]
  simp

variable {k : Type u} [Field k] {X X' : Scheme.{u}}
  [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]

/-- **Hartshorne II.8, proof of Theorem 8.19 (p. 181).** Let `X` be a nonsingular
variety and `X'` a proper variety over `k`, and let `T : X ⤏ X'` be a birational
map with maximal domain of definition `V = T.domain`. Then every point of
codimension one of `X` lies in `V`, hence `X \ V` has codimension at least
two. -/
theorem Scheme.RationalMap.codim_compl_domain_birational
    (hX : IsIntegral X ∧ IsSeparated (X ↘ Spec (.of k)) ∧
      LocallyOfFiniteType (X ↘ Spec (.of k)) ∧ QuasiCompact (X ↘ Spec (.of k)))
    (hXreg : X.IsRegular)
    (hX' : IsIntegral X' ∧ IsProper (X' ↘ Spec (.of k)))
    (T : X ⤏ X')
    (hT : ∃ f : X.PartialIso X',
      f.IsOver (X ↘ Spec (.of k)) (X' ↘ Spec (.of k)) ∧ f.toRationalMap = T) :
    (∀ x : X, Hartshorne.codim (closure ({x} : Set X)) = 1 → x ∈ T.domain) ∧
      2 ≤ Hartshorne.codim ((T.domain : Set X)ᶜ) := by
  obtain ⟨hint, hsep, hlft, hqc⟩ := hX
  obtain ⟨-, hprop⟩ := hX'
  obtain ⟨f, hf, rfl⟩ := hT
  -- `X` satisfies condition `(*)`.
  have hstar : X.SatisfiesConditionStar := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    have hsepX : X.IsSeparated := ⟨by
      rw [show Limits.terminal.from X = (X ↘ Spec (.of k)) ≫ Limits.terminal.from _ from
        Limits.terminal.hom_ext _ _]
      infer_instance⟩
    exact ⟨{}, hint, hsepX, fun x _ ↦ hXreg.2 x⟩
  have η_spec : ∀ x : X, genericPoint X ⤳ x := fun x ↦ genericPoint_specializes x
  -- Codimension-one points lie in the domain.
  have hmem : ∀ x : X, Order.coheight x = 1 → x ∈ f.toRationalMap.domain := by
    intro x hx
    have hdvr : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      X.codimensionOneStalk_isDiscreteValuationRing hstar hx
    have hex : ValuativeCriterion.Existence (X' ↘ Spec (.of k)) := by
      have h := (IsProper.eq_valuativeCriterion ▸ hprop :)
      exact h.1.1.1.existence
    have hφ : f.toRationalMap.fromFunctionField ≫ (X' ↘ Spec (.of k)) =
        X.fromSpecStalk _ ≫ (X ↘ Spec (.of k)) := by
      change (f.source.fromSpecStalkOfMem _ _ ≫ f.iso.hom ≫ f.target.ι) ≫ _ = _
      rw [Category.assoc, Category.assoc, hf]
      exact Scheme.Opens.fromSpecStalkOfMem_ι_assoc _ _ _ _
    have hsq : f.toRationalMap.fromFunctionField ≫ (X' ↘ Spec (.of k)) =
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
          X.fromSpecStalk x ≫ (X ↘ Spec (.of k)) := by
      rw [hφ, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc (η_spec x)]
      rfl
    let sq : ValuativeCommSq (X' ↘ Spec (.of k)) :=
      { R := X.presheaf.stalk x
        domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
        valuationRing := inferInstance
        K := X.functionField
        i₁ := f.toRationalMap.fromFunctionField
        i₂ := X.fromSpecStalk x ≫ (X ↘ Spec (.of k))
        commSq := ⟨hsq⟩ }
    obtain ⟨⟨l, hl₁, hl₂⟩⟩ := hex sq
    have hl₂' : (l : Spec (X.presheaf.stalk x) ⟶ X') ≫ (X' ↘ Spec (.of k)) =
        X.fromSpecStalk x ≫ (X ↘ Spec (.of k)) := hl₂
    let g := Scheme.PartialMap.ofFromSpecStalk (X ↘ Spec (.of k)) (X' ↘ Spec (.of k)) l hl₂'
    have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
    have hg : g.toRationalMap = f.toRationalMap := by
      apply Scheme.RationalMap.eq_of_fromFunctionField_eq
      rw [Scheme.RationalMap.fromFunctionField_toRationalMap, Scheme.PartialMap.fromFunctionField,
        ← specMap_stalkSpecializes_fromSpecStalkOfMem g (η_spec x) _ hxg,
        Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
      exact hl₁
    exact Scheme.RationalMap.mem_domain.mpr ⟨g, hxg, hg⟩
  -- Points outside the domain have coheight at least two.
  have htwo : ∀ z : X, z ∉ f.toRationalMap.domain → 2 ≤ Order.coheight z := by
    intro z hz
    have h1 : Order.coheight z ≠ 1 := fun h ↦ hz (hmem z h)
    have h0 : Order.coheight z ≠ 0 := by
      intro h
      have hmax : IsMax z := Order.coheight_eq_zero.mp h
      have hzη : z ⤳ genericPoint X := hmax (η_spec z)
      have hη : genericPoint X ∈ f.toRationalMap.domain :=
        ((genericPoint_spec X).mem_open_set_iff f.toRationalMap.domain.isOpen).mpr
          (by simpa using f.toRationalMap.dense_domain.nonempty)
      exact hz (hzη.mem_open f.toRationalMap.domain.isOpen hη)
    generalize Order.coheight z = c at h0 h1 ⊢
    induction c using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      norm_cast at h0 h1 ⊢
      omega
  refine ⟨fun x hx ↦ hmem x ((Hartshorne.codim_closure_singleton_eq_coheight x).symm.trans hx), ?_⟩
  refine le_iInf₂ fun Z hZ ↦ ?_
  let e : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints
  rw [← Order.coheight_orderIso e]
  exact htwo _ (hZ (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem)

end AlgebraicGeometry
