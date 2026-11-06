/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# The local dimension formula for a flat fibre

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.5 (p. 256).

Let `f : X ⟶ Y` be a flat morphism of schemes of finite type over a field, `x ∈ X` and
`y = f x`. Then `dim 𝒪_{X_y,x} = dim 𝒪_{X,x} - dim 𝒪_{Y,y}`; since all three local rings are
Noetherian, hence finite-dimensional, this is stated additively as
`dim 𝒪_{X_y,x} + dim 𝒪_{Y,y} = dim 𝒪_{X,x}`.

The proof has two parts.

* Algebra: for the flat local homomorphism `𝒪_{Y,y} → 𝒪_{X,x}` of Noetherian local rings,
  `dim 𝒪_{X,x} = dim 𝒪_{Y,y} + dim 𝒪_{X,x}/𝔪_y 𝒪_{X,x}`. This is Mathlib's height formula
  for algebras with going-down, and flat algebras have going-down.
* Geometry: `dim 𝒪_{X_y,x} = dim 𝒪_{X,x}/𝔪_y 𝒪_{X,x}`. The stalk map of the fibre inclusion
  is surjective, and a prime of `𝒪_{X,x}` contains its kernel exactly when the corresponding
  generalization of `x` lies in the fibre, exactly when the prime contains `𝔪_y 𝒪_{X,x}`.
  So the two quotients have the same prime spectrum.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hartshorne

universe u

/-- For a flat local homomorphism `A → B` of Noetherian local rings,
`dim B = dim A + dim B/𝔪_A B` (Matsumura, Theorem 15.1). -/
theorem ringKrullDim_eq_add_ringKrullDim_quotient_of_flat {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : φ.Flat) :
    ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map φ) := by
  algebraize [φ]
  have hJ : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B :=
    Ideal.map_le_iff_le_comap.mpr (maximalIdeal_comap φ).ge
  have : (maximalIdeal B).LiesOver (maximalIdeal A) := ⟨(maximalIdeal_comap φ).symm⟩
  have : Nontrivial (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hJ)
  have : IsLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal B).map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) =
      maximalIdeal _ := by
    apply IsLocalRing.eq_maximalIdeal
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      (maximalIdeal.isMaximal B)).resolve_left fun htop ↦ (maximalIdeal.isMaximal B).ne_top ?_
    have := congrArg (Ideal.comap (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))) htop
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hJ, Ideal.comap_top] at this
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A)
    (maximalIdeal B)
  rw [hmax] at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    ← maximalIdeal_height_eq_ringKrullDim, h, WithBot.coe_add]
  rfl

/-- The canonical maps `Spec 𝒪_{S,s} ⟶ S` are compatible with stalk maps, pointwise. -/
theorem fromSpecStalk_stalkMap_apply {S T : Scheme.{u}} (h : S ⟶ T) (s : S)
    (q : Spec (S.presheaf.stalk s)) :
    h (S.fromSpecStalk s q) = T.fromSpecStalk (h s) (Spec.map (h.stalkMap s) q) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- Let `g : F ⟶ X` be a preimmersion whose image is the fibre of `f : X ⟶ Y` through
`g x'`. Then `dim 𝒪_{F,x'} = dim 𝒪_{X,g x'}/𝔪_{f(g x')} 𝒪_{X,g x'}`. -/
theorem ringKrullDim_stalk_eq_ringKrullDim_quotient_of_range_eq {F X Y : Scheme.{u}}
    (g : F ⟶ X) [IsPreimmersion g] (f : X ⟶ Y) (x' : F)
    (hg : Set.range g = f ⁻¹' {f (g x')}) :
    ringKrullDim (F.presheaf.stalk x') =
      ringKrullDim (X.presheaf.stalk (g x') ⧸
        (maximalIdeal (Y.presheaf.stalk (f (g x')))).map (f.stalkMap (g x')).hom) := by
  have hψ : Function.Surjective (g.stalkMap x').hom := g.stalkMap_surjective x'
  have key : ∀ Q : Spec (X.presheaf.stalk (g x')),
      (maximalIdeal (Y.presheaf.stalk (f (g x')))).map (f.stalkMap (g x')).hom ≤ Q.asIdeal ↔
        X.fromSpecStalk (g x') Q ∈ Set.range g := by
    intro Q
    have h1 : X.fromSpecStalk (g x') Q ∈ Set.range g ↔
        Spec.map (f.stalkMap (g x')) Q = closedPoint _ := by
      rw [hg, Set.mem_preimage, Set.mem_singleton_iff, fromSpecStalk_stalkMap_apply]
      conv_lhs => rhs; rw [← Scheme.fromSpecStalk_closedPoint (x := f (g x')) (X := Y)]
      exact (Y.fromSpecStalk (f (g x'))).isEmbedding.injective.eq_iff
    refine Iff.trans ?_ h1.symm
    rw [Ideal.map_le_iff_le_comap]
    constructor
    · intro h
      exact PrimeSpectrum.ext
        (le_antisymm (le_maximalIdeal (PrimeSpectrum.isPrime _).ne_top) h)
    · intro h
      exact (congrArg PrimeSpectrum.asIdeal h).ge
  have hS : PrimeSpectrum.zeroLocus
        (RingHom.ker (g.stalkMap x').hom : Set (X.presheaf.stalk (g x'))) =
      PrimeSpectrum.zeroLocus
        ((maximalIdeal (Y.presheaf.stalk (f (g x')))).map (f.stalkMap (g x')).hom :
          Set (X.presheaf.stalk (g x'))) := by
    ext Q
    rw [← range_comap_of_surjective (hf := hψ), PrimeSpectrum.mem_zeroLocus,
      SetLike.coe_subset_coe]
    refine Iff.trans ?_ (key Q).symm
    constructor
    · rintro ⟨q', rfl⟩
      exact ⟨F.fromSpecStalk x' q', fromSpecStalk_stalkMap_apply g x' q'⟩
    · rintro ⟨z', hz'⟩
      have hsp : g z' ⤳ g x' := by
        rw [hz']
        exact (Scheme.range_fromSpecStalk (x := g x')).subset ⟨Q, rfl⟩
      rw [g.isEmbedding.toIsInducing.specializes_iff] at hsp
      obtain ⟨q', rfl⟩ : z' ∈ Set.range (F.fromSpecStalk x') := by
        rw [Scheme.range_fromSpecStalk]; exact hsp
      refine ⟨q', (X.fromSpecStalk (g x')).isEmbedding.injective ?_⟩
      rw [← hz', fromSpecStalk_stalkMap_apply g x' q']
      rfl
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ).symm,
    ringKrullDim_quotient, ringKrullDim_quotient, hS]

/-- **Hartshorne III Proposition 9.5.** Let `f : X → Y` be a flat morphism of schemes of finite
type over a field `k`. For `x ∈ X` with `y = f x`, the local ring of the scheme-theoretic fibre
`X_y` at `x` satisfies `dim 𝒪_{X_y,x} = dim 𝒪_{X,x} - dim 𝒪_{Y,y}`, stated additively as
`dim 𝒪_{X_y,x} + dim 𝒪_{Y,y} = dim 𝒪_{X,x}`. -/
theorem ringKrullDim_stalk_fiber_add_ringKrullDim_stalk_of_flat {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (f : X ⟶ Y) (hf : Flat f.left)
    (x : X.left) :
    ringKrullDim ((f.left.fiber (f.left x)).presheaf.stalk (f.left.asFiber x)) +
        ringKrullDim (Y.left.presheaf.stalk (f.left x)) =
      ringKrullDim (X.left.presheaf.stalk x) := by
  have : LocallyOfFiniteType X.hom := hX.1
  have : LocallyOfFiniteType Y.hom := hY.1
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have h := ringKrullDim_stalk_eq_ringKrullDim_quotient_of_range_eq
    (f.left.fiberι (f.left x)) f.left (f.left.asFiber x)
    (by rw [Scheme.Hom.fiberι_asFiber, Scheme.Hom.range_fiberι])
  rw [Scheme.Hom.fiberι_asFiber] at h
  rw [h, ringKrullDim_eq_add_ringKrullDim_quotient_of_flat (f.left.stalkMap x).hom
    ((Flat.iff_flat_stalkMap f.left).mp hf x), add_comm]

end Hartshorne
