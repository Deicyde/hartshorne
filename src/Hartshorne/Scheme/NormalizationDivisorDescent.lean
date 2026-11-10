/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.InvertibleSectionDivisor
import Hartshorne.Scheme.CartierClassPicardIntegral
import Hartshorne.Scheme.AbsoluteNormalizationUniversal
import Hartshorne.Scheme.AbsoluteNormalizationFinite
import Hartshorne.Scheme.Differentials.DenseNonsingularLocus
import Hartshorne.Scheme.RegularLocalFactorial
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Hartshorne.Scheme.VarietyBasicInstances
import Hartshorne.Scheme.AbsoluteNormalizationNormal

/-!
# Toward descending a very ample sheaf from the normalization of a curve

Building blocks for Hartshorne III, Exercise 5.8(b).
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

noncomputable section

/-- In an irreducible Noetherian `T₀` space of dimension one (e.g. an integral Noetherian scheme
of dimension one), every proper closed subset is finite. -/
theorem finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_eq_one
    {X : Type*} [TopologicalSpace X] [T0Space X] [IrreducibleSpace X]
    [NoetherianSpace X] (hdim : topologicalKrullDim X = 1)
    {Z : Set X} (hZclosed : IsClosed Z) (hZproper : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨S, hSfinite, hSclosed, hSirreducible, hZ⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZclosed
  rw [hZ]
  refine hSfinite.sUnion fun C hCS => ?_
  have hCZ : C ⊆ Z := by
    rw [hZ]
    exact Set.subset_sUnion_of_mem hCS
  have hCproper : C ≠ Set.univ := by
    intro hC
    apply hZproper
    exact Set.eq_univ_of_univ_subset (by simpa [hC] using hCZ)
  let C' : IrreducibleCloseds X := ⟨C, hSirreducible C hCS, hSclosed C hCS⟩
  let X' : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hCX : C' < X' := by
    refine lt_of_le_of_ne (Set.subset_univ C) ?_
    intro h
    apply hCproper
    simpa [C', X'] using congrArg (fun W : IrreducibleCloseds X => (W : Set X)) h
  have hdim' : Order.krullDim (IrreducibleCloseds X) ≤ 1 := by
    simpa [topologicalKrullDim] using hdim.le
  have hCmin : IsMin C' :=
    (Order.krullDim_le_one_iff.mp hdim' C').resolve_right (fun hCmax => hCmax.not_lt hCX)
  -- every point of `C` is a generic point of `C`
  have hgen : ∀ y ∈ C, closure ({y} : Set X) = C := by
    intro y hy
    let y' : IrreducibleCloseds X :=
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hyC : y' ≤ C' :=
      (hSclosed C hCS).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hy)
    exact congrArg (fun W : IrreducibleCloseds X => (W : Set X)) (hCmin.eq_of_le hyC)
  obtain ⟨x, hxC⟩ := (hSirreducible C hCS).nonempty
  refine (Set.finite_singleton x).subset fun y hy => ?_
  have : closure ({y} : Set X) = closure {x} := (hgen y hy).trans (hgen x hxC).symm
  exact (inseparable_iff_closure_eq.mpr this).eq

/-- An open subscheme all of whose points are regular is normal. -/
theorem isNormal_of_forall_isRegularAt {X : Scheme.{u}} (U : X.Opens)
    (h : ∀ x ∈ U, X.IsRegularAt x) : Hartshorne.IsNormal U := by
  have key : ∀ x : U, IsDomain (U.toScheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (U.toScheme.presheaf.stalk x) := by
    intro x
    have : IsRegularLocalRing (X.presheaf.stalk x.1) := h x.1 x.2
    have : IsDomain (X.presheaf.stalk x.1) := Hartshorne.RegularLocal.isDomain _
    have : UniqueFactorizationMonoid (X.presheaf.stalk x.1) :=
      Hartshorne.RegularLocalFactorial.uniqueFactorizationMonoid_of_isRegularLocalRing _
    let e := (Scheme.Opens.stalkIso U x).commRingCatIsoToRingEquiv
    have : IsDomain (U.toScheme.presheaf.stalk x) := e.toMulEquiv.isDomain
    exact ⟨this, IsIntegrallyClosed.of_equiv e.symm⟩
  exact ⟨fun x ↦ (key x).1, fun x ↦ (key x).2⟩

/-- **The normalization is an isomorphism over a dense open set of regular points.** For an
integral scheme locally of finite type over a perfect field. -/
theorem exists_isIso_absoluteNormalizationMap_restrict {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ (∀ x ∈ U, X.IsRegularAt x) ∧
      IsIso (Hartshorne.absoluteNormalizationMap X ∣_ U) := by
  obtain ⟨U, hne, -, hreg⟩ := Hartshorne.exists_nonempty_dense_isRegularAt f
  have := isNormal_of_forall_isRegularAt U hreg
  exact ⟨U, hne, hreg, Hartshorne.isIso_absoluteNormalizationMap_restrict_of_isNormal X U⟩

/-- On an integral Noetherian scheme of dimension one, the complement of a nonempty open set is
finite. -/
theorem finite_compl_of_topologicalKrullDim_eq_one {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] (hdim : topologicalKrullDim X = 1) {U : X.Opens}
    (hU : (U : Set X).Nonempty) : ((U : Set X)ᶜ).Finite := by
  refine finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_eq_one hdim
    U.isOpen.isClosed_compl fun h ↦ ?_
  obtain ⟨x, hx⟩ := hU
  exact (Set.eq_univ_iff_forall.mp h x) hx

/-- For an integral scheme of finite type over a field, the normalization map has finite
fibres over finite sets. -/
theorem finite_preimage_absoluteNormalizationMap {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec (.of k)) (hf : Hartshorne.FiniteType f) {S : Set X}
    (hS : S.Finite) :
    (Hartshorne.absoluteNormalizationMap X ⁻¹' S).Finite := by
  have := Hartshorne.isFinite_absoluteNormalizationMap_of_finiteType_field k X f hf
  exact (Hartshorne.absoluteNormalizationMap X).finite_preimage hS

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}}

/-- Linearly equivalent Cartier divisors have isomorphic invertible sheaves. -/
theorem nonempty_sheaf_iso_of_linearEquivalent {D E : X.CartierDivisor}
    (h : D.LinearEquivalent E) : Nonempty (D.sheaf ≅ E.sheaf) := by
  have h1 := congrArg X.cartierClassToPicard ((cartierDivisorClass_eq_iff D E).2 h)
  rw [cartierClassToPicard_apply, cartierClassToPicard_apply] at h1
  exact (Hartshorne.Ringed.Pic.mk_eq_mk_iff _ _).1 (Additive.ofMul.injective h1)

/-- A nonzero global section of an invertible sheaf `L` on an integral scheme has an effective
divisor of zeros `D`, and `𝒪_X(D) ≅ L`. -/
theorem exists_isDivisorOfZeros_of_isInvertible [IsIntegral X] {L : X.Modules}
    (hL : L.IsInvertible) {s : L.val.obj (op ⊤)} (hs : s ≠ 0) :
    ∃ D : X.CartierDivisor, IsDivisorOfZeros L s D ∧ D.IsEffective ∧ Nonempty (D.sheaf ≅ L) := by
  obtain ⟨D₀, ⟨χ⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso hL
  obtain ⟨D, hD, hDeff, hlin⟩ := exists_isDivisorOfZeros χ.symm hs
  obtain ⟨e⟩ := nonempty_sheaf_iso_of_linearEquivalent hlin
  exact ⟨D, hD, hDeff, ⟨e ≪≫ χ⟩⟩

/-- The divisor of zeros of `s` is trivial over an open set where `s` generates `L`. -/
theorem IsDivisorOfZeros.restrict_eq_zero {L : X.Modules} {s : L.val.obj (op ⊤)}
    {D : X.CartierDivisor} (hD : IsDivisorOfZeros L s D) {V : X.Opens}
    (ψ : L.over V ≅ SheafOfModules.unit _) (hu : IsUnit (trivApply ψ (resTop L V s))) :
    D.restrict V = 0 := by
  obtain ⟨f, hf, hDV⟩ := hD V ψ
  rw [hDV]
  let a : X.structureUnitsSheaf.obj.obj (op V) := (show Γ(X, V)ˣ from hu.unit)
  have ha : X.structureUnitsToTotalQuotientUnits.hom.app (op V) a = f := by
    refine Units.ext ?_
    change X.toK V hu.unit = kUnitVal f
    rw [hu.unit_spec]
    exact hf
  rw [← ha]
  exact Scheme.toCartierDivisorSheaf_structureUnits V a

end Scheme.CartierDivisor

open Scheme.CartierDivisor in
/-- **Reduction of the divisor part of Hartshorne III, Exercise 5.8(b) to choosing a section.**
Let `X` be an integral scheme of finite type and dimension one over a perfect field, with
normalization `ν : X̃ ⟶ X`. There is a finite set `S` of points of `X̃` such that for every
invertible sheaf `L` on `X̃` and every nonzero global section `s` of `L` generating `L` near each
point of `S`, the divisor of zeros `D = (s)₀` is effective, `𝒪(D) ≅ L`, and `D` is trivial near
every point of `X̃` lying over a singular point of `X`. -/
theorem exists_finite_set_divisor_of_generates {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) (hf : Hartshorne.FiniteType f)
    (hdim : topologicalKrullDim X = 1) :
    ∃ S : Set (Hartshorne.absoluteNormalization X), S.Finite ∧
      ∀ (L : (Hartshorne.absoluteNormalization X).Modules), L.IsInvertible →
        ∀ s : L.val.obj (op ⊤), s ≠ 0 →
          (∀ x ∈ S, ∃ (V : (Hartshorne.absoluteNormalization X).Opens)
            (ψ : L.over V ≅ SheafOfModules.unit _), x ∈ V ∧
              IsUnit (trivApply ψ (resTop L V s))) →
          ∃ D : (Hartshorne.absoluteNormalization X).CartierDivisor, D.IsEffective ∧
            Nonempty (D.sheaf ≅ L) ∧
            ∀ x, ¬ X.IsRegularAt (Hartshorne.absoluteNormalizationMap X x) →
              ∃ V : (Hartshorne.absoluteNormalization X).Opens, x ∈ V ∧ D.restrict V = 0 := by
  have := hf.1
  have := Hartshorne.isNoetherian_of_finiteType f hf
  obtain ⟨U, hU, hreg, -⟩ := exists_isIso_absoluteNormalizationMap_restrict f
  refine ⟨Hartshorne.absoluteNormalizationMap X ⁻¹' ((U : Set X)ᶜ),
    finite_preimage_absoluteNormalizationMap f hf
      (finite_compl_of_topologicalKrullDim_eq_one hdim hU),
    fun L hL s hs hgen ↦ ?_⟩
  obtain ⟨D, hD, hDeff, hDL⟩ := exists_isDivisorOfZeros_of_isInvertible hL hs
  refine ⟨D, hDeff, hDL, fun x hx ↦ ?_⟩
  obtain ⟨V, ψ, hxV, hu⟩ := hgen x fun hxU ↦ hx (hreg _ hxU)
  exact ⟨V, hxV, hD.restrict_eq_zero ψ hu⟩

end

end AlgebraicGeometry
