/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.FlatFamilies.AssociatedPoints
import Hartshorne.Curve.DVR
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Flatness over a regular curve

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.7 (pp. 257–258).

Let `f : X ⟶ Y` with `X` locally Noetherian and `Y` integral, one-dimensional, with regular
local rings. Then `f` is flat if and only if every associated point of `X` maps to the generic
point of `Y`. If `X` is reduced, this is equivalent to every irreducible component of `X`
dominating `Y`.

The proof works stalk by stalk. Every local ring of `Y` is a field or a discrete valuation ring,
hence a Bézout domain, so flatness of `𝒪_{Y,f(x)} → 𝒪_{X,x}` means that nonzero elements map
to non-zero-divisors. Zero-divisors of the Noetherian local ring `𝒪_{X,x}` lie in associated
primes, and every associated prime of `𝒪_{X,x}` comes from an associated point of `X`
specializing to `x`.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing Order Topology

namespace Hartshorne

universe u

/-- Over a Bézout domain, a ring map is flat if and only if it sends every nonzero element to a
non-zero-divisor. -/
theorem ringHom_flat_iff_forall_ne_zero_map_mem_nonZeroDivisors {R A : Type*} [CommRing R]
    [CommRing A] [IsDomain R] [IsBezout R] (φ : R →+* A) :
    φ.Flat ↔ ∀ r : R, r ≠ 0 → φ r ∈ nonZeroDivisors A := by
  let := φ.toAlgebra
  change Module.Flat R A ↔ _
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
  constructor
  · intro h r hr
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    apply h a
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, ?_⟩
    rw [Submonoid.mk_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    exact ha
  · intro h a ha
    obtain ⟨⟨r, hr⟩, hra⟩ := (Submodule.mem_torsion_iff a).mp ha
    rw [Submonoid.mk_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm] at hra
    exact (mem_nonZeroDivisors_iff_right.mp (h r (nonZeroDivisors.ne_zero hr))) a hra

/-- Every associated prime of the local ring at a point of a locally Noetherian scheme comes
from an associated point specializing to that point: its elements become nonunits in the local
ring at the associated point. -/
theorem exists_mem_associatedPoints_specializes_of_mem_associatedPrimes {X : Scheme.{u}}
    [IsLocallyNoetherian X] {x : X} {p : Ideal (X.presheaf.stalk x)}
    (hp : p ∈ associatedPrimes (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    ∃ (x' : X) (h : x' ⤳ x), x' ∈ associatedPoints X ∧
      ∀ a ∈ p, X.presheaf.stalkSpecializes h a ∈ maximalIdeal (X.presheaf.stalk x') := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (by trivial) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let xU : U := ⟨x, hxU⟩
  let q := hU.primeIdealOf xU
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf xU
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal := hU.isLocalization_stalk xU
  set P := p.comap (algebraMap Γ(X, U) (X.presheaf.stalk x)) with hPdef
  have hPass : P ∈ associatedPrimes Γ(X, U) Γ(X, U) :=
    Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      q.asIdeal.primeCompl (Algebra.linearMap Γ(X, U) (X.presheaf.stalk x)) p hp
      ((isNoetherianRing_iff_ideal_fg _).mp inferInstance _)
  have hPprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hPass).isPrime
  have hpm : p ≤ maximalIdeal _ := le_maximalIdeal (AssociatedPrimes.mem_iff.mp hp).isPrime.ne_top
  have hPq : P ≤ q.asIdeal := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x) q.asIdeal]
    exact Ideal.comap_mono hpm
  let y : PrimeSpectrum Γ(X, U) := ⟨P, hPprime⟩
  have hy : hU.fromSpec y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self y
  have hspec : hU.fromSpec y ⤳ x := by
    have := ((PrimeSpectrum.le_iff_specializes y q).mp hPq).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf xU] at this
  let : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hy⟩
  have hloc' : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hy
  have hunder : (maximalIdeal (X.presheaf.stalk (hU.fromSpec y))).comap
      (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))) = P :=
    IsLocalization.AtPrime.under_maximalIdeal _ y.asIdeal
  refine ⟨hU.fromSpec y, hspec, ?_, ?_⟩
  · change IsAssociatedPrime _ _
    rw [← AssociatedPrimes.mem_iff]
    apply Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      y.asIdeal.primeCompl (Algebra.linearMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)))
    rw [hunder]
    exact hPass
  · intro a ha
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl a
    have hspec_alg : ∀ t : Γ(X, U),
        X.presheaf.stalkSpecializes hspec (algebraMap Γ(X, U) (X.presheaf.stalk x) t) =
          algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) t := by
      intro t
      change (X.presheaf.germ U x hxU ≫ X.presheaf.stalkSpecializes hspec) t = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    have hkey := IsLocalization.mk'_spec (X.presheaf.stalk x) r s
    have hrP : r ∈ P := by
      change algebraMap _ _ r ∈ p
      rw [← hkey]
      exact Ideal.mul_mem_right _ _ ha
    have hr' : algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) r ∈ maximalIdeal _ := by
      rw [← hunder] at hrP
      exact hrP
    have hs' : algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) (s : Γ(X, U)) ∉
        maximalIdeal _ := by
      intro hs
      have hsP : (s : Γ(X, U)) ∈ P := by
        rw [← hunder]
        exact hs
      exact s.2 (hPq hsP)
    have hmul := congrArg (X.presheaf.stalkSpecializes hspec) hkey
    rw [map_mul, hspec_alg, hspec_alg] at hmul
    rw [← hmul] at hr'
    exact ((maximalIdeal.isMaximal _).isPrime.mem_or_mem hr').resolve_right hs'

/-- On an integral scheme, a point whose local ring is a field is the generic point. -/
theorem eq_genericPoint_of_isField_stalk {Y : Scheme.{u}} [IsIntegral Y] {y : Y}
    (h : IsField (Y.presheaf.stalk y)) : y = genericPoint Y := by
  have h0 : ringKrullDim (Y.presheaf.stalk y) = 0 := ringKrullDim_eq_zero_of_isField h
  rw [ringKrullDim_stalk_eq_coheight] at h0
  have hc : coheight y = 0 := by exact_mod_cast h0
  have hle : y ≤ genericPoint Y := (genericPoint_spec Y).specializes trivial
  exact (Specializes.antisymm (coheight_eq_zero.mp hc hle) (genericPoint_specializes y)).eq

/-- On an integral scheme, specializing a nonzero germ to the generic point gives a unit. -/
theorem isUnit_stalkSpecializes_of_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y] {y z : Y}
    (hz : z = genericPoint Y) (h : z ⤳ y) {r : Y.presheaf.stalk y} (hr : r ≠ 0) :
    IsUnit (Y.presheaf.stalkSpecializes h r) := by
  subst hz
  have hinj : Function.Injective (Y.presheaf.stalkSpecializes h) :=
    IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
  have hne : (Y.presheaf.stalkSpecializes h r : Y.functionField) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hr
  exact hne.isUnit

/-- The local rings of an integral scheme of dimension at most one whose local rings are regular
are Bézout domains. -/
theorem isBezout_stalk_of_isRegularLocalRing {Y : Scheme.{u}} [IsIntegral Y]
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (hdim : topologicalKrullDim Y ≤ 1)
    (y : Y) : IsBezout (Y.presheaf.stalk y) := by
  have hkd : krullDim Y ≤ 1 := by
    rw [← krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
    exact hdim
  have hcoh : coheight y ≤ 1 := by
    have : (coheight y : WithBot ℕ∞) ≤ 1 := (coheight_le_krullDim y).trans hkd
    exact_mod_cast this
  rcases (show coheight y = 0 ∨ coheight y = 1 by
      rcases (le_iff_lt_or_eq.mp hcoh) with h | h
      · exact Or.inl (Order.lt_one_iff.mp h)
      · exact Or.inr h) with h0 | h1
  · have : Ring.KrullDimLE 0 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le (by rw [h0]; rfl)
    let _ : Field (Y.presheaf.stalk y) := (Ring.KrullDimLE.isField_of_isDomain).toField
    infer_instance
  · have hd : ringKrullDim (Y.presheaf.stalk y) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h1]
      rfl
    have := hreg y
    have : IsDiscreteValuationRing (Y.presheaf.stalk y) :=
      ((dvr_characterizations (Y.presheaf.stalk y) hd).out 2 0).mp (hreg y)
    infer_instance

/-- **Hartshorne III, Proposition 9.7.** Let `f : X ⟶ Y` with `X` locally Noetherian and `Y`
integral of dimension one with regular local rings. Then `f` is flat if and only if every
associated point of `X` maps to the generic point of `Y`. -/
theorem flat_iff_forall_mem_associatedPoints_eq_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsIntegral Y]
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : topologicalKrullDim Y = 1) :
    Flat f ↔ ∀ x ∈ associatedPoints X, f x = genericPoint Y := by
  have hbez := isBezout_stalk_of_isRegularLocalRing hreg hdim.le
  rw [Flat.iff_flat_stalkMap]
  constructor
  · intro hflat x hx
    by_contra hne
    have hnf : ¬ IsField (Y.presheaf.stalk (f x)) :=
      fun h ↦ hne (eq_genericPoint_of_isField_stalk h)
    obtain ⟨t, htm, ht0⟩ : ∃ t ∈ maximalIdeal (Y.presheaf.stalk (f x)), t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hnf (isField_iff_maximalIdeal_eq.mpr ((Submodule.eq_bot_iff _).mpr hcon))
    have := hbez (f x)
    have hreg' := (ringHom_flat_iff_forall_ne_zero_map_mem_nonZeroDivisors _).mp (hflat x) t ht0
    exact (mem_associatedPoints_iff_maximalIdeal_subset_zeroDivisors X x).mp hx _
      (map_nonunit (f.stalkMap x).hom t htm) hreg'
  · intro hass x
    have := hbez (f x)
    rw [ringHom_flat_iff_forall_ne_zero_map_mem_nonZeroDivisors]
    intro r hr
    by_contra hzd
    have hmem : f.stalkMap x r ∈
        ⋃ p ∈ associatedPrimes (X.presheaf.stalk x) (X.presheaf.stalk x), (p : Set _) := by
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
      exact hzd
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hmem
    obtain ⟨p, hp, hrp⟩ := hmem
    obtain ⟨x', hx'x, hx'ass, hpm⟩ := exists_mem_associatedPoints_specializes_of_mem_associatedPrimes hp
    have hunit := isUnit_stalkSpecializes_of_eq_genericPoint (hass x' hx'ass)
      (f.base.hom.map_specializes hx'x) hr
    have hnu := hpm _ hrp
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply] at hnu
    exact hnu (hunit.map (f.stalkMap x').hom)

/-- On a reduced scheme, the associated points are exactly the generic points of the irreducible
components. -/
theorem mem_associatedPoints_iff_closure_mem_irreducibleComponents {X : Scheme.{u}}
    [IsReduced X] (x : X) : x ∈ associatedPoints X ↔ closure {x} ∈ irreducibleComponents X := by
  constructor
  · intro hx
    obtain ⟨-, v, hv⟩ := hx
    have hv0 : v ≠ 0 := by
      rintro rfl
      apply (maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
      rw [hv]
      simp
    obtain ⟨Q, hQ, hvQ⟩ : ∃ Q ∈ minimalPrimes (X.presheaf.stalk x), v ∉ Q := by
      by_contra hcon
      push Not at hcon
      apply hv0
      have hvinf : v ∈ sInf (minimalPrimes (X.presheaf.stalk x)) := Submodule.mem_sInf.mpr hcon
      rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hvinf
      exact (Ideal.mem_radical_iff.mp hvinf).elim fun n hn ↦
        (isNilpotent_iff_eq_zero.mp ⟨n, (Submodule.mem_bot _).mp hn⟩)
    have hmQ : maximalIdeal (X.presheaf.stalk x) ≤ Q := by
      intro a ha
      rw [hv, Ideal.mem_radical_iff] at ha
      obtain ⟨n, hn⟩ := ha
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hn
      have hQmem : a ^ n * v ∈ Q := hn ▸ Q.zero_mem
      exact hQ.1.1.mem_of_pow_mem n ((hQ.1.1.mem_or_mem hQmem).resolve_right hvQ)
    have hdim : Ring.KrullDimLE 0 (X.presheaf.stalk x) := by
      rw [Ring.krullDimLE_zero_iff]
      intro I hI
      have hIm : I ≤ maximalIdeal _ := le_maximalIdeal hI.ne_top
      have hQI : Q ≤ I := hQ.2 ⟨hI, bot_le⟩ (hIm.trans hmQ)
      rw [le_antisymm hIm (hmQ.trans hQI)]
      exact maximalIdeal.isMaximal _
    have hc : coheight x = 0 := by
      have hle := Ring.krullDimLE_iff.mp hdim
      rw [ringKrullDim_stalk_eq_coheight] at hle
      have hle' : coheight x ≤ 0 := by exact_mod_cast hle
      exact nonpos_iff_eq_zero.mp hle'
    have hmax : IsMax x := coheight_eq_zero.mp hc
    rw [irreducibleComponents_eq_maximals_closed]
    refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, fun Z hZ hxZ ↦ ?_⟩
    have hg : closure {hZ.2.genericPoint} = Z := hZ.2.isGenericPoint_genericPoint hZ.1
    have hgx : hZ.2.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hg]
      exact hxZ (subset_closure rfl)
    have hxg : x ⤳ hZ.2.genericPoint := hmax hgx
    rw [← hg]
    exact specializes_iff_closure_subset.mp hxg
  · intro hx
    have hm : maximalIdeal (X.presheaf.stalk x) = ⊥ :=
      isField_iff_maximalIdeal_eq.mp (isField_stalk_of_closure_mem_irreducibleComponents X x hx)
    refine ⟨(maximalIdeal.isMaximal _).isPrime, 1, ?_⟩
    ext a
    rw [hm, Ideal.mem_radical_iff, Submodule.mem_bot]
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul, mul_one]
    exact ⟨fun ha ↦ ⟨1, by rw [ha, pow_one]⟩, fun ⟨n, hn⟩ ↦ isNilpotent_iff_eq_zero.mp ⟨n, hn⟩⟩

/-- The image of the closure of a point is dense in an integral scheme exactly when the point
maps to the generic point. -/
theorem dense_image_closure_singleton_iff {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    (x : X) : Dense (f '' closure {x}) ↔ f x = genericPoint Y := by
  have hcl : closure (f '' closure {x}) = closure {f x} := by
    apply le_antisymm
    · apply closure_minimal _ isClosed_closure
      calc f '' closure {x} ⊆ closure (f '' {x}) :=
            image_closure_subset_closure_image f.continuous
        _ = closure {f x} := by rw [Set.image_singleton]
    · apply closure_mono
      rw [Set.singleton_subset_iff]
      exact Set.mem_image_of_mem _ (subset_closure rfl)
  rw [dense_iff_closure_eq, hcl]
  constructor
  · intro h
    exact (show IsGenericPoint (f x) Set.univ from h).eq (genericPoint_spec Y)
  · intro h
    rw [h]
    exact genericPoint_closure Y

/-- **Hartshorne III, Proposition 9.7**, reduced case. For a reduced scheme `X` and an integral
scheme `Y`, every associated point of `X` maps to the generic point of `Y` if and only if every
irreducible component of `X` dominates `Y`. -/
theorem forall_mem_associatedPoints_eq_genericPoint_iff_forall_dense_image
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] [IsIntegral Y] :
    (∀ x ∈ associatedPoints X, f x = genericPoint Y) ↔
      ∀ Z ∈ irreducibleComponents X, Dense (f '' Z) := by
  constructor
  · intro h Z hZ
    have hg : closure {hZ.1.genericPoint} = Z :=
      hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
    have hmem : hZ.1.genericPoint ∈ associatedPoints X := by
      rw [mem_associatedPoints_iff_closure_mem_irreducibleComponents, hg]
      exact hZ
    have hd := (dense_image_closure_singleton_iff f _).mpr (h _ hmem)
    rwa [hg] at hd
  · intro h x hx
    exact (dense_image_closure_singleton_iff f x).mp
      (h _ ((mem_associatedPoints_iff_closure_mem_irreducibleComponents x).mp hx))

/-- **Hartshorne III, Proposition 9.7**, reduced case. Let `f : X ⟶ Y` with `X` reduced and
locally Noetherian and `Y` integral of dimension one with regular local rings. Then `f` is flat
if and only if every irreducible component of `X` dominates `Y`. -/
theorem flat_iff_forall_mem_irreducibleComponents_dense_image {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsReduced X] [IsIntegral Y]
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : topologicalKrullDim Y = 1) :
    Flat f ↔ ∀ Z ∈ irreducibleComponents X, Dense (f '' Z) :=
  (flat_iff_forall_mem_associatedPoints_eq_genericPoint f hreg hdim).trans
    (forall_mem_associatedPoints_eq_genericPoint_iff_forall_dense_image f)

end Hartshorne
