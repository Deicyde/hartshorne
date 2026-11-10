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
import Mathlib.Algebra.Module.Submodule.Union
import Hartshorne.Scheme.GloballyGenerated
import Hartshorne.Scheme.RelativeVeryAmple
import Hartshorne.Scheme.VanishingIdealSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Hartshorne.Scheme.CartierDivisorPullback

/-!
# Descending a very ample sheaf from the normalization of a curve

Hartshorne III, Exercise 5.8(b): for a proper integral curve `X` over an algebraically closed field
with normalization `ν : X̃ ⟶ X` and a very ample `L` on `X̃`, there is an effective divisor `D` on
`X̃` with `𝒪(D) ≅ L` whose points lie over nonsingular points of `X`, and an invertible `L₀` on `X`
with `ν^* L₀ ≅ L` (`AlgebraicGeometry.exists_pullback_iso_of_isVeryAmpleRelative`).

The divisor is the divisor of zeros of a section of `L` avoiding the finite preimage of the
singular locus (a hyperplane section misses finitely many points over an infinite field). It
descends along `ν` because `ν` is an isomorphism over a dense open set `U` and `D` is trivial near
`ν⁻¹(Uᶜ)` (`AlgebraicGeometry.Scheme.exists_cartierPullbackData_of_isIso_morphismRestrict`).
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

open Scheme.CartierDivisor in
/-- The germ at `x` of the coordinate of a global section in a trivialization near `x`. -/
def trivGerm {Y : Scheme.{u}} {L : Y.Modules} {V : Y.Opens}
    (ψ : L.over V ≅ SheafOfModules.unit _) {x : Y} (hx : x ∈ V) (s : L.val.obj (op ⊤)) :
    Y.presheaf.stalk x :=
  Y.presheaf.germ V x hx (trivApply ψ (resTop L V s))

set_option backward.isDefEq.respectTransparency false in
open Scheme.CartierDivisor in
/-- `trivGerm` is additive. -/
theorem trivGerm_add {Y : Scheme.{u}} {L : Y.Modules} {V : Y.Opens}
    (ψ : L.over V ≅ SheafOfModules.unit _) {x : Y} (hx : x ∈ V) (s t : L.val.obj (op ⊤)) :
    trivGerm ψ hx (s + t) = trivGerm ψ hx s + trivGerm ψ hx t := by
  unfold trivGerm trivApply resTop
  rw [map_add, map_add, map_add]

set_option backward.isDefEq.respectTransparency false in
open Scheme.CartierDivisor in
/-- `trivGerm` is semilinear over the global sections. -/
theorem trivGerm_smul {Y : Scheme.{u}} {L : Y.Modules} {V : Y.Opens}
    (ψ : L.over V ≅ SheafOfModules.unit _) {x : Y} (hx : x ∈ V)
    (c : Y.ringCatSheaf.obj.obj (op ⊤)) (s : L.val.obj (op ⊤)) :
    trivGerm ψ hx (c • s) =
      Y.presheaf.germ ⊤ x trivial (show Γ(Y, ⊤) from c) * trivGerm ψ hx s := by
  unfold trivGerm trivApply resTop
  rw [PresheafOfModules.map_smul, map_smul, smul_eq_mul, map_mul]
  congr 1
  exact Y.presheaf.germ_res_apply (homOfLE (le_top : V ≤ ⊤)) x hx (show Γ(Y, ⊤) from c)

/-- **Choosing a section that generates at finitely many points.** Over an infinite field `k`
acting on global sections, if at each of finitely many points `x` some global section of `L`
generates `L` at `x` (its coordinate in a fixed trivialization near `x` has a unit germ), then a
single global section does so at all of them. -/
theorem exists_isUnit_trivGerm {k : Type u} [Field k] [Infinite k] {Y : Scheme.{u}}
    (φ : k →+* Γ(Y, ⊤)) {L : Y.Modules} (S : Finset Y) (V : Y → Y.Opens) (hxV : ∀ x, x ∈ V x)
    (ψ : ∀ x, L.over (V x) ≅ SheafOfModules.unit _)
    (h : ∀ x ∈ S, ∃ t : L.val.obj (op ⊤), IsUnit (trivGerm (ψ x) (hxV x) t)) :
    ∃ s : L.val.obj (op ⊤), ∀ x ∈ S, IsUnit (trivGerm (ψ x) (hxV x) s) := by
  let _ : Module k (L.val.obj (op ⊤)) :=
    Module.compHom _ (show k →+* Y.ringCatSheaf.obj.obj (op ⊤) from φ)
  let N : S → Submodule k (L.val.obj (op ⊤)) := fun x ↦
    { carrier := {s | trivGerm (ψ x) (hxV x) s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x.1)}
      add_mem' := fun {a b} ha hb ↦ by
        show trivGerm (ψ x) (hxV x) (a + b) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x.1)
        rw [trivGerm_add]
        exact add_mem ha hb
      zero_mem' := by
        show trivGerm (ψ x) (hxV x) 0 ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x.1)
        have := trivGerm_add (ψ x) (hxV x) 0 0
        rw [add_zero, left_eq_add] at this
        rw [this]
        exact zero_mem _
      smul_mem' := fun c a ha ↦ by
        show trivGerm (ψ x) (hxV x) ((show Y.ringCatSheaf.obj.obj (op ⊤) from φ c) • a) ∈
          IsLocalRing.maximalIdeal (Y.presheaf.stalk x.1)
        rw [trivGerm_smul]
        exact Ideal.mul_mem_left _ _ ha }
  have hN : ∀ x, N x ≠ ⊤ := by
    intro x htop
    obtain ⟨t, ht⟩ := h x.1 x.2
    have : t ∈ N x := htop ▸ Submodule.mem_top
    exact (IsLocalRing.mem_maximalIdeal _).mp this ht
  have hcard : (Finset.univ : Finset S).card < ENat.card k := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.natCast_lt_top _
  obtain ⟨s, -, hs⟩ := Set.exists_of_ssubset
    (Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ N hN hcard)
  refine ⟨s, fun x hx ↦ ?_⟩
  by_contra hu
  apply hs
  refine Set.mem_biUnion (Finset.mem_univ ⟨x, hx⟩) ?_
  exact (IsLocalRing.mem_maximalIdeal _).mpr hu

open Scheme.CartierDivisor in
/-- The divisor of zeros of `s` is trivial near a point where `s` generates `L`, i.e. where the
coordinate of `s` in a trivialization has a unit germ. -/
theorem Scheme.CartierDivisor.IsDivisorOfZeros.exists_restrict_eq_zero {Y : Scheme.{u}}
    {L : Y.Modules}
    {s : L.val.obj (op ⊤)} {D : Y.CartierDivisor} (hD : IsDivisorOfZeros L s D) {V : Y.Opens}
    (ψ : L.over V ≅ SheafOfModules.unit _) {x : Y} (hx : x ∈ V)
    (hu : IsUnit (trivGerm ψ hx s)) : ∃ W : Y.Opens, x ∈ W ∧ D.restrict W = 0 := by
  obtain ⟨W, i, hxW, hW⟩ := RingedSpace.isUnit_res_of_isUnit_germ Y.toRingedSpace V
    (trivApply ψ (resTop L V s)) x hx hu
  obtain ⟨f, hf, hDV⟩ := hD V ψ
  have hWV : W ≤ V := leOfHom i
  refine ⟨W, hxW, ?_⟩
  rw [← D.restrict_restrict hWV, hDV, Scheme.toCartierDivisorSheaf_naturality_apply]
  let a : Y.structureUnitsSheaf.obj.obj (op W) := (show Γ(Y, W)ˣ from hW.unit)
  have ha : Y.structureUnitsToTotalQuotientUnits.hom.app (op W) a =
      Y.totalQuotientUnitsSheaf.obj.map (homOfLE hWV).op f := by
    refine Units.ext ?_
    change Y.toK W hW.unit = Y.totalQuotientSheaf.obj.map (homOfLE hWV).op (kUnitVal f)
    rw [hW.unit_spec, ← hf, toK_naturality]
    rfl
  rw [← ha]
  exact Scheme.toCartierDivisorSheaf_structureUnits W a

open Scheme.CartierDivisor in
/-- **Reduction of the divisor part of Hartshorne III, Exercise 5.8(b) to choosing a section**,
germ form. Let `X` be an integral scheme of finite type and dimension one over a perfect field,
with normalization `ν : X̃ ⟶ X`. There is a nonempty open `U` of regular points of `X`, over which
`ν` is an isomorphism and whose preimage has finite complement, such that for every invertible
sheaf `L` on `X̃` and every nonzero global section `s` of `L` generating `L` at each point outside
`ν⁻¹(U)` (for some trivialization near the point), the divisor of zeros `D = (s)₀` is effective,
`𝒪(D) ≅ L`, and `D` is trivial near every point outside `ν⁻¹(U)`. -/
theorem exists_finite_set_divisor_of_isUnit_trivGerm {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    (hf : Hartshorne.FiniteType f) (hdim : topologicalKrullDim X = 1) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ (∀ x ∈ U, X.IsRegularAt x) ∧
      IsIso (Hartshorne.absoluteNormalizationMap X ∣_ U) ∧
      (Hartshorne.absoluteNormalizationMap X ⁻¹' ((U : Set X)ᶜ)).Finite ∧
      ∀ (L : (Hartshorne.absoluteNormalization X).Modules), L.IsInvertible →
        ∀ s : L.val.obj (op ⊤), s ≠ 0 →
          (∀ x, x ∉ Hartshorne.absoluteNormalizationMap X ⁻¹ᵁ U →
            ∃ (V : (Hartshorne.absoluteNormalization X).Opens)
            (ψ : L.over V ≅ SheafOfModules.unit _) (hx : x ∈ V), IsUnit (trivGerm ψ hx s)) →
          ∃ D : (Hartshorne.absoluteNormalization X).CartierDivisor, D.IsEffective ∧
            Nonempty (D.sheaf ≅ L) ∧
            ∀ x, x ∉ Hartshorne.absoluteNormalizationMap X ⁻¹ᵁ U →
              ∃ V : (Hartshorne.absoluteNormalization X).Opens, x ∈ V ∧ D.restrict V = 0 := by
  have := hf.1
  have := Hartshorne.isNoetherian_of_finiteType f hf
  obtain ⟨U, hU, hreg, hiso⟩ := exists_isIso_absoluteNormalizationMap_restrict f
  refine ⟨U, hU, hreg, hiso, finite_preimage_absoluteNormalizationMap f hf
    (finite_compl_of_topologicalKrullDim_eq_one hdim hU), fun L hL s hs hgen ↦ ?_⟩
  obtain ⟨D, hD, hDeff, hDL⟩ := exists_isDivisorOfZeros_of_isInvertible hL hs
  refine ⟨D, hDeff, hDL, fun x hx ↦ ?_⟩
  obtain ⟨V, ψ, hxV, hu⟩ := hgen x hx
  exact hD.exists_restrict_eq_zero ψ hxV hu

/-- The preimage functor on opens of a morphism of schemes is final: every comma category has the
terminal object `⊤`. -/
instance opensMap_final {X Y : Scheme.{u}} (f : X ⟶ Y) : (Opens.map f.base).Final := by
  constructor
  intro U
  refine isConnected_of_isTerminal _
    (x := StructuredArrow.mk (homOfLE le_top : U ⟶ (Opens.map f.base).obj ⊤)) ?_
  refine IsTerminal.ofUniqueHom
    (fun A ↦ StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)) ?_
  intro A m
  ext
  exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- **Pullback preserves generation by global sections.** -/
theorem isGloballyGenerated_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {F : Y.Modules}
    (hF : F.IsGloballyGenerated) : ((Scheme.Modules.pullback f).obj F).IsGloballyGenerated := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  obtain ⟨I, p, hp⟩ := (Scheme.Modules.isGloballyGenerated_iff_exists_epi F).1 hF
  refine (Scheme.Modules.isGloballyGenerated_iff_exists_epi _).2
    ⟨I, (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).inv ≫
      (Scheme.Modules.pullback f).map p, ?_⟩
  have : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ ((Scheme.Modules.pullback f).map p) :=
    @Functor.map_epi _ _ _ _ (Scheme.Modules.pullback f) _ _ _ p hp
  exact epi_comp _ _

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **A very ample sheaf is generated by global sections**: it is the pullback of `𝒪(1)` along
an immersion into projective space, and `𝒪(1)` is generated by the coordinate sections. -/
theorem isGloballyGenerated_of_isVeryAmpleRelative {X Y : Scheme.{u}} {p : X ⟶ Y}
    {L : X.Modules} (hL : Hartshorne.IsVeryAmpleRelative p L) : L.IsGloballyGenerated := by
  obtain ⟨-, r, i, -, -, -, ⟨e⟩⟩ := hL
  have h1 : (Hartshorne.projectiveSpaceIntTwistingSheaf.{u} r 1).IsGloballyGenerated :=
    Hartshorne.ProjTwistingSheaf.isGloballyGenerated (Hartshorne.adjoin_intGrading_one_eq_top r)
  have h2 := isGloballyGenerated_pullback i (isGloballyGenerated_pullback
    (Limits.pullback.fst (Hartshorne.projectiveSpaceOverIntegersMap.{u} r)
      (Hartshorne.schemeToSpecZ Y)) h1)
  obtain ⟨I, q, hq⟩ := (Scheme.Modules.isGloballyGenerated_iff_exists_epi _).1 h2
  have : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ e.hom :=
    @IsIso.epi_of_iso _ _ _ _ e.hom ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  exact (Scheme.Modules.isGloballyGenerated_iff_exists_epi L).2 ⟨I, q ≫ e.hom, epi_comp _ _⟩

/-- If an invertible sheaf is generated by global sections, every point lies in the nonvanishing
locus of some global section. -/
theorem exists_mem_nonvanishingLocus_of_isGloballyGenerated {X : Scheme.{u}} {L : X.Modules}
    (hL : L.IsInvertible) (hg : L.IsGloballyGenerated) (x : X) :
    ∃ s : Γ(L, ⊤), x ∈ Hartshorne.nonvanishingLocus L s := by
  obtain ⟨ι, σ, hσ⟩ := hg
  obtain ⟨U, e, hxU, he⟩ := Hartshorne.exists_isTrivializingSection hL x
  by_contra hall
  push Not at hall
  apply he.germ_not_mem hxU
  have hle : Submodule.span (X.presheaf.stalk x)
      (Set.range fun i => L.presheaf.germ ⊤ x trivial (σ i)) ≤
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_contra h
    exact hall (σ i) h
  exact hle ((hσ x).symm ▸ Submodule.mem_top)

/-- The generator `ψ⁻¹(1)` of a trivialization `ψ : L|_U ≅ 𝒪_U`, as a section of `L` over `U`. -/
def trivSection {Y : Scheme.{u}} {L : Y.Modules} {U : Y.Opens}
    (ψ : L.over U ≅ SheafOfModules.unit _) : Γ(L, U) :=
  ((L.over U).unitHomEquiv ψ.inv).val (op (Over.mk (𝟙 U)))

/-- The inverse of a trivialization is multiplication by its generator. -/
theorem triv_inv_app {Y : Scheme.{u}} {L : Y.Modules} {U : Y.Opens}
    (ψ : L.over U ≅ SheafOfModules.unit _) (V : Y.Opens) (h : V ≤ U) (r : Γ(Y, V)) :
    (show Γ(L, V) from ψ.inv.val.app (op (Over.mk (homOfLE h))) r) =
      r • L.presheaf.map (homOfLE h).op (trivSection ψ) := by
  set σ := (L.over U).unitHomEquiv ψ.inv
  have hφ : ψ.inv = (L.over U).unitHomEquiv.symm σ := (Equiv.symm_apply_apply _ _).symm
  have hσ := σ.2 (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op
  rw [hφ]
  change r • (show Γ(L, V) from σ.val (op (Over.mk (homOfLE h)))) = _
  rw [← hσ]
  rfl

open Scheme.CartierDivisor in
/-- **The generator of a trivialization is a trivializing section**, and every section over `U`
is its coordinate times the generator. -/
theorem isTrivializingSection_trivSection {Y : Scheme.{u}} {L : Y.Modules} {U : Y.Opens}
    (ψ : L.over U ≅ SheafOfModules.unit _) :
    Hartshorne.IsTrivializingSection L U (trivSection ψ) ∧
      ∀ t : Γ(L, U), t = (show Γ(Y, U) from trivApply ψ t) • trivSection ψ := by
  have hinv : ∀ (V : Y.Opens) (h : V ≤ U) (t : Γ(L, V)),
      (show Γ(L, V) from ψ.inv.val.app (op (Over.mk (homOfLE h)))
        (ψ.hom.val.app (op (Over.mk (homOfLE h))) t)) = t :=
    fun V h t ↦ ConcreteCategory.congr_hom
      (congrArg (fun α : L.over U ⟶ L.over U ↦ α.val.app (op (Over.mk (homOfLE h))))
        ψ.hom_inv_id) (show (L.over U).val.obj (op (Over.mk (homOfLE h))) from t)
  have hhom : ∀ (V : Y.Opens) (h : V ≤ U) (r : Γ(Y, V)),
      (show Γ(Y, V) from ψ.hom.val.app (op (Over.mk (homOfLE h)))
        (ψ.inv.val.app (op (Over.mk (homOfLE h))) r)) = r :=
    fun V h r ↦ ConcreteCategory.congr_hom
      (congrArg (fun α : SheafOfModules.unit _ ⟶ SheafOfModules.unit _ ↦
        α.val.app (op (Over.mk (homOfLE h)))) ψ.inv_hom_id)
        (show (SheafOfModules.unit ((Y.ringCatSheaf).over U)).val.obj
          (op (Over.mk (homOfLE h))) from r)
  refine ⟨fun V h ↦ ⟨fun a b hab ↦ ?_, fun t ↦ ?_⟩, fun t ↦ ?_⟩
  · have ha := triv_inv_app ψ V h a
    have hb := triv_inv_app ψ V h b
    have := congrArg (fun z : Γ(L, V) ↦
      (show Γ(Y, V) from ψ.hom.val.app (op (Over.mk (homOfLE h))) z))
      (ha.trans (hab.trans hb.symm))
    exact (hhom V h a).symm.trans (this.trans (hhom V h b))
  · refine ⟨ψ.hom.val.app (op (Over.mk (homOfLE h))) t, ?_⟩
    exact (triv_inv_app ψ V h _).symm.trans (hinv V h t)
  · have h1 := (triv_inv_app ψ U le_rfl (trivApply ψ t)).symm.trans (hinv U le_rfl t)
    have h2 : L.presheaf.map (homOfLE (le_refl U)).op (trivSection ψ) = trivSection ψ := by
      rw [show (homOfLE (le_refl U)).op = 𝟙 (op U) from rfl, CategoryTheory.Functor.map_id]
      rfl
    rw [h2] at h1
    exact h1.symm

/-- A global section nonvanishing at `x` has a unit coordinate germ at `x` in every
trivialization near `x`. -/
theorem isUnit_trivGerm_of_mem_nonvanishingLocus {Y : Scheme.{u}} {L : Y.Modules} {U : Y.Opens}
    (ψ : L.over U ≅ SheafOfModules.unit _) {x : Y} (hx : x ∈ U) {s : Γ(L, ⊤)}
    (hs : x ∈ Hartshorne.nonvanishingLocus L s) : IsUnit (trivGerm ψ hx s) := by
  obtain ⟨he, hdecomp⟩ := isTrivializingSection_trivSection ψ
  have hfg := hdecomp (L.presheaf.map (homOfLE le_top).op s)
  have := (he.mem_nonvanishingLocus_iff hfg hx).1 hs
  exact (Scheme.mem_basicOpen Y _ x hx).1 this

/-- The coordinate germ of the zero section is zero. -/
theorem trivGerm_zero {Y : Scheme.{u}} {L : Y.Modules} {V : Y.Opens}
    (ψ : L.over V ≅ SheafOfModules.unit _) {x : Y} (hx : x ∈ V) : trivGerm ψ hx 0 = 0 := by
  have := trivGerm_add ψ hx 0 0
  rwa [add_zero, left_eq_add] at this

/-- If `f` is an isomorphism over `U`, then `f` induces isomorphisms on sections over every open
contained in `U`. -/
theorem isIso_app_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    [IsIso (f ∣_ U)] {V : Y.Opens} (hV : V ≤ U) : IsIso (f.app V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hV
  have h := morphismRestrict_app f U (U.ι ⁻¹ᵁ V)
  have : IsIso (f.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) := by
    have : IsIso ((f ∣_ U).app (U.ι ⁻¹ᵁ V)) := inferInstance
    rw [h] at this
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (f.app _)
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U (U.ι ⁻¹ᵁ V))).op)
      inferInstance this
  rwa [e] at this

/-- If `f` is an isomorphism over `U`, then `f` is injective over `U`. -/
theorem eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    [IsIso (f ∣_ U)] {x x' : X} (h : f x = f x') (hx : x ∈ f ⁻¹ᵁ U) : x = x' := by
  have hinj : Function.Injective (f ∣_ U) := (Scheme.homeoOfIso (asIso (f ∣_ U))).injective
  have hx' : x' ∈ f ⁻¹ᵁ U := show f x' ∈ U from h ▸ hx
  have := @hinj ⟨x, hx⟩ ⟨x', hx'⟩ (Subtype.ext ((morphismRestrict_base_coe f U ⟨x, hx⟩).trans
    (h.trans (morphismRestrict_base_coe f U ⟨x', hx'⟩).symm)))
  exact congrArg Subtype.val this

/-- If `f` is an isomorphism over `U`, every point of `U` has a preimage. -/
theorem exists_eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    [IsIso (f ∣_ U)] {y : Y} (hy : y ∈ U) : ∃ x, f x = y := by
  obtain ⟨x, hx⟩ := (Scheme.homeoOfIso (asIso (f ∣_ U))).surjective ⟨y, hy⟩
  refine ⟨x.1, ?_⟩
  have := congrArg Subtype.val hx
  simpa using this

namespace Scheme

/-- The principal divisor of a quotient of rational functions. -/
theorem principalCartierDivisor_globalUnit_div {X : Scheme.{u}} [IsIntegral X]
    (g g' : X.functionFieldˣ) :
    X.principalCartierDivisor (globalUnit X (g / g')) =
      X.principalCartierDivisor (globalUnit X g) - X.principalCartierDivisor (globalUnit X g') := by
  rw [globalUnit, map_div]
  exact X.principalCartierDivisorHom.map_sub (Additive.ofMul _) (Additive.ofMul _)

/-- On an open set containing the generic point, the principal divisor of a rational function
vanishes exactly when the function is a regular unit there. -/
theorem principalCartierDivisor_restrict_eq_zero_iff {X : Scheme.{u}} [IsIntegral X]
    {V : X.Opens} (hη : genericPoint X ∈ V) (g : X.functionFieldˣ) :
    (X.principalCartierDivisor (globalUnit X g)).restrict V = 0 ↔
      ∃ a : Γ(X, V)ˣ, X.presheaf.germ V (genericPoint X) hη a = g := by
  rw [principalCartierDivisor_restrict]
  have h0 : (0 : X.cartierDivisorSheaf.obj.obj (op V)) =
      X.toCartierDivisorSheaf.hom.app (op V) (Additive.ofMul (1 : X.totalQuotientUnitsSheaf.obj.obj (op V))) :=
    ((X.toCartierDivisorSheaf.hom.app (op V)).hom.map_zero).symm
  rw [h0, toCartierDivisorSheaf_apply_eq_iff_ratio, div_one]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have := congrArg (fun t => (totalQuotientUnitsEquivFunctionField V hη t : X.functionField)) ha
    simp only at this
    rw [totalQuotientUnitsEquivFunctionField_restrict_top, MulEquiv.apply_symm_apply] at this
    exact (totalQuotientUnitsEquivFunctionField_structureUnits V hη a).symm.trans this
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (totalQuotientUnitsEquivFunctionField V hη).injective
    ext
    rw [totalQuotientUnitsEquivFunctionField_restrict_top, MulEquiv.apply_symm_apply]
    exact (totalQuotientUnitsEquivFunctionField_structureUnits V hη a).trans ha

/-- A morphism that is an isomorphism on sections over `V` detects whether a principal divisor
vanishes on `V`. -/
theorem principalCartierDivisor_restrict_eq_zero_iff_of_isIso_app {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y)
    {V : Y.Opens} (hη : genericPoint Y ∈ V) [IsIso (f.app V)] (g : Y.functionFieldˣ) :
    (Y.principalCartierDivisor (globalUnit Y g)).restrict V = 0 ↔
      (X.principalCartierDivisor
        (globalUnit X (genericFunctionFieldUnitsMap f hf g))).restrict (f ⁻¹ᵁ V) = 0 := by
  rw [principalCartierDivisor_restrict_eq_zero_iff hη,
    principalCartierDivisor_restrict_eq_zero_iff (genericPoint_mem_preimage_of_mem f hf hη)]
  let e : Γ(Y, V) ≃+* Γ(X, f ⁻¹ᵁ V) := (asIso (f.app V)).commRingCatIsoToRingEquiv
  have he : ∀ r, e r = f.app V r := fun r => rfl
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨Units.map e.toMonoidHom a, ?_⟩
    rw [Units.coe_map]
    change X.presheaf.germ _ _ _ (e a) = _
    rw [he, ← genericFunctionFieldMap_germ f hf hη, ha]
    rfl
  · rintro ⟨b, hb⟩
    refine ⟨Units.map e.symm.toMonoidHom b, ?_⟩
    apply (f.genericFunctionFieldMap hf).hom.injective
    rw [Units.coe_map]
    change f.genericFunctionFieldMap hf (Y.presheaf.germ _ _ _ (e.symm b)) = _
    rw [genericFunctionFieldMap_germ f hf hη, ← he, e.apply_symm_apply, hb]
    rfl

end Scheme

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}}

/-- The zero divisor restricts to zero. -/
theorem restrict_zero (O : X.Opens) : (0 : X.CartierDivisor).restrict O = 0 :=
  (X.cartierDivisorSheaf.obj.map (homOfLE le_top).op).hom.map_zero

/-- Restriction of Cartier divisors is additive. -/
theorem restrict_sub (A B : X.CartierDivisor) (O : X.Opens) :
    (A - B).restrict O = A.restrict O - B.restrict O :=
  (X.cartierDivisorSheaf.obj.map (homOfLE le_top).op).hom.map_sub A B

/-- Two divisors agreeing on an open set agree on every smaller open set. -/
theorem restrict_congr_of_le {A B : X.CartierDivisor} {O O' : X.Opens} (h : O' ≤ O)
    (hAB : A.restrict O = B.restrict O) : A.restrict O' = B.restrict O' := by
  rw [← A.restrict_restrict h, hAB, B.restrict_restrict]

/-- A Cartier divisor that vanishes near every point of an open set vanishes on it. -/
theorem restrict_eq_zero_of_locally (E : X.CartierDivisor) {O : X.Opens}
    (h : ∀ x ∈ O, ∃ W : X.Opens, x ∈ W ∧ E.restrict W = 0) : E.restrict O = 0 := by
  choose W hxW hW using fun x : O ↦ h x.1 x.2
  apply X.cartierDivisorSheaf.eq_of_locally_eq' (fun x : O ↦ W x ⊓ O) O
    (fun _ ↦ homOfLE inf_le_right) (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _, hx⟩)
  intro i
  rw [E.restrict_restrict, ← E.restrict_restrict (inf_le_left : W i ⊓ O ≤ W i), hW i]
  simp only [map_zero]

end Scheme.CartierDivisor

namespace Scheme

/-- The principal divisor of the constant function `1` is zero. -/
theorem principalCartierDivisor_globalUnit_one {X : Scheme.{u}} [IsIntegral X] :
    X.principalCartierDivisor (globalUnit X 1) = 0 := by
  rw [globalUnit, map_one]
  exact X.principalCartierDivisorHom.map_zero

open CartierDivisor in
/-- **Descent of a Cartier divisor along a morphism that is an isomorphism over `U`.** Let
`f : X ⟶ Y` be a closed morphism of integral schemes that maps the generic point to the generic
point, induces a surjection of function fields, and is an isomorphism over an open `U`. A Cartier
divisor on `X` that is trivial near every point outside `f⁻¹(U)` is, locally, the pullback of
local equations of a Cartier divisor on `Y`. -/
theorem exists_cartierPullbackData_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y)
    (hcl : IsClosedMap f.base) {U : Y.Opens} [IsIso (f ∣_ U)]
    (hsurj : Function.Surjective (f.genericFunctionFieldMap hf))
    (E : X.CartierDivisor) (hE : ∀ x, x ∉ f ⁻¹ᵁ U → ∃ W : X.Opens, x ∈ W ∧ E.restrict W = 0) :
    ∃ D : Y.CartierDivisor, CartierPullbackData f hf D E := by
  classical
  have hloc : ∀ y : Y, ∃ (V : Y.Opens) (g : Y.functionFieldˣ), y ∈ V ∧
      E.restrict (f ⁻¹ᵁ V) = (X.principalCartierDivisor
        (globalUnit X (genericFunctionFieldUnitsMap f hf g))).restrict (f ⁻¹ᵁ V) ∧
      (V ≤ U ∨ g = 1) := by
    intro y
    by_cases hy : y ∈ U
    · obtain ⟨x, rfl⟩ := exists_eq_of_isIso_morphismRestrict f hy
      obtain ⟨V₀, f₀, hxV₀, hf₀⟩ := E.exists_localEquation x
      have hη₀ : genericPoint X ∈ V₀ := genericPoint_mem_opens_of_mem hxV₀
      set h := totalQuotientUnitsEquivFunctionField V₀ hη₀ f₀ with hh
      obtain ⟨g₀, hg₀⟩ := hsurj (h : X.functionField)
      have hg₀ne : g₀ ≠ 0 := by
        rintro rfl
        rw [map_zero] at hg₀
        exact h.ne_zero hg₀.symm
      let g : Y.functionFieldˣ := Units.mk0 g₀ hg₀ne
      have hgh : genericFunctionFieldUnitsMap f hf g = h := Units.ext hg₀
      have hV₀ : E.restrict V₀ = (X.principalCartierDivisor (globalUnit X h)).restrict V₀ := by
        rw [hf₀, principalCartierDivisor_restrict]
        congr 2
        apply (totalQuotientUnitsEquivFunctionField V₀ hη₀).injective
        rw [totalQuotientUnitsEquivFunctionField_restrict_top, MulEquiv.apply_symm_apply]
      let V : Y.Opens := U ⊓ ⟨(f.base '' (V₀ : Set X)ᶜ)ᶜ,
        (hcl _ V₀.isOpen.isClosed_compl).isOpen_compl⟩
      have hfV : f ⁻¹ᵁ V ≤ V₀ := by
        intro x' hx'
        by_contra hx'V₀
        exact hx'.2 ⟨x', hx'V₀, rfl⟩
      refine ⟨V, g, ⟨hy, ?_⟩, ?_, Or.inl inf_le_left⟩
      · rintro ⟨x', hx', hx'x⟩
        have hx'U : x' ∈ f ⁻¹ᵁ U := show f.base x' ∈ U from hx'x ▸ hy
        exact hx' ((eq_of_isIso_morphismRestrict f hx'x hx'U) ▸ hxV₀)
      · rw [hgh]
        exact restrict_congr_of_le hfV hV₀
    · let Z : Set X := {x | ∀ W : X.Opens, x ∈ W → E.restrict W ≠ 0}
      have hZ : IsClosed Z := by
        rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
        intro x hx
        simp only [Z, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hx
        obtain ⟨W, hxW, hW⟩ := hx
        exact ⟨W, fun x' hx' hZ' ↦ hZ' W hx' hW, W.isOpen, hxW⟩
      let V : Y.Opens := ⟨(f.base '' Z)ᶜ, (hcl _ hZ).isOpen_compl⟩
      refine ⟨V, 1, ?_, ?_, Or.inr rfl⟩
      · rintro ⟨x, hxZ, rfl⟩
        by_cases hxU : x ∈ f ⁻¹ᵁ U
        · exact hy hxU
        · obtain ⟨W, hxW, hW⟩ := hE x hxU
          exact hxZ W hxW hW
      · rw [show genericFunctionFieldUnitsMap f hf 1 = 1 from map_one _,
          principalCartierDivisor_globalUnit_one, restrict_zero]
        apply restrict_eq_zero_of_locally
        intro x hx
        have hxZ : x ∉ Z := fun hxZ ↦ hx ⟨x, hxZ, rfl⟩
        simp only [Z, Set.mem_ofPred_eq, not_forall, not_not] at hxZ
        obtain ⟨W, hxW, hW⟩ := hxZ
        exact ⟨W, hxW, hW⟩
  choose V g hyV hEV hVU using hloc
  have hcompat : ∀ y z, (Y.principalCartierDivisor (globalUnit Y (g y))).restrict (V y ⊓ V z) =
      (Y.principalCartierDivisor (globalUnit Y (g z))).restrict (V y ⊓ V z) := by
    intro y z
    have hηyz : genericPoint Y ∈ V y ⊓ V z :=
      ⟨genericPoint_mem_opens_of_mem (hyV y), genericPoint_mem_opens_of_mem (hyV z)⟩
    rw [← sub_eq_zero, ← restrict_sub, ← principalCartierDivisor_globalUnit_div]
    by_cases hU' : V y ≤ U ∨ V z ≤ U
    · have hle : V y ⊓ V z ≤ U :=
        hU'.elim (fun h ↦ inf_le_left.trans h) (fun h ↦ inf_le_right.trans h)
      have := isIso_app_of_isIso_morphismRestrict f hle
      rw [principalCartierDivisor_restrict_eq_zero_iff_of_isIso_app f hf hηyz,
        show genericFunctionFieldUnitsMap f hf (g y / g z) = genericFunctionFieldUnitsMap f hf (g y) /
          genericFunctionFieldUnitsMap f hf (g z) from map_div _ _ _,
        principalCartierDivisor_globalUnit_div, restrict_sub, sub_eq_zero,
        ← restrict_congr_of_le (show f ⁻¹ᵁ (V y ⊓ V z) ≤ f ⁻¹ᵁ V y from fun _ hx ↦ hx.1) (hEV y),
        ← restrict_congr_of_le (show f ⁻¹ᵁ (V y ⊓ V z) ≤ f ⁻¹ᵁ V z from fun _ hx ↦ hx.2) (hEV z)]
    · simp only [not_or] at hU'
      rw [(hVU y).resolve_left hU'.1, (hVU z).resolve_left hU'.2, div_one,
        principalCartierDivisor_globalUnit_one, restrict_zero]
  obtain ⟨D, hD, -⟩ := Y.cartierDivisorSheaf.existsUnique_gluing' V ⊤ (fun _ ↦ homOfLE le_top)
    (fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hyV y⟩)
    (fun y ↦ (Y.principalCartierDivisor (globalUnit Y (g y))).restrict (V y)) (by
      intro y z
      exact ((Y.principalCartierDivisor (globalUnit Y (g y))).restrict_restrict inf_le_left).trans
        ((hcompat y z).trans
          ((Y.principalCartierDivisor (globalUnit Y (g z))).restrict_restrict inf_le_right).symm))
  exact ⟨D, fun x ↦ ⟨V (f.base x), f ⁻¹ᵁ V (f.base x), g (f.base x), hyV (f.base x), le_rfl,
    hD (f.base x), hEV (f.base x)⟩⟩

end Scheme

/-- A morphism of integral schemes that is an isomorphism over a nonempty open set sends the
generic point to the generic point. -/
theorem map_genericPoint_of_isIso_morphismRestrict {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) {U : Y.Opens} [IsIso (f ∣_ U)] (hU : (U : Set Y).Nonempty) :
    f.base (genericPoint X) = genericPoint Y := by
  obtain ⟨y, hy⟩ := hU
  obtain ⟨x, hx⟩ :=
    exists_eq_of_isIso_morphismRestrict f (Scheme.genericPoint_mem_opens_of_mem hy)
  have h1 := (genericPoint_specializes x).map f.continuous
  rw [hx] at h1
  exact (h1.antisymm (genericPoint_specializes _)).eq

/-- A closed morphism of integral schemes that is an isomorphism over an open set containing the
generic point induces a surjection of function fields. -/
theorem surjective_genericFunctionFieldMap_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y)
    (hcl : IsClosedMap f.base) {U : Y.Opens} [IsIso (f ∣_ U)] (hU : genericPoint Y ∈ U) :
    Function.Surjective (f.genericFunctionFieldMap hf) := by
  intro t
  obtain ⟨W, hW, s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq X.presheaf (show X.presheaf.stalk (genericPoint X) from t)
  let V : Y.Opens := U ⊓ ⟨(f.base '' (W : Set X)ᶜ)ᶜ,
    (hcl _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hfV : f ⁻¹ᵁ V ≤ W := by
    intro x' hx'
    by_contra hx'W
    exact hx'.2 ⟨x', hx'W, rfl⟩
  have hηV : genericPoint Y ∈ V := by
    refine ⟨hU, ?_⟩
    rintro ⟨x', hx', hx'η⟩
    have hx'U : x' ∈ f ⁻¹ᵁ U := show f.base x' ∈ U from hx'η ▸ hU
    exact hx' ((eq_of_isIso_morphismRestrict f (hx'η.trans hf.symm) hx'U) ▸ hW)
  have := isIso_app_of_isIso_morphismRestrict f (inf_le_left : V ≤ U)
  refine ⟨Y.presheaf.germ V _ hηV (inv (f.app V) (X.presheaf.map (homOfLE hfV).op s)), ?_⟩
  rw [Scheme.genericFunctionFieldMap_germ f hf hηV, IsIso.inv_hom_id_apply]
  exact X.presheaf.germ_res_apply (homOfLE hfV) _ _ s

/-- **The divisor part of Hartshorne III, Exercise 5.8(b), with the open set.** Let `X` be a
proper integral scheme of dimension one over an algebraically closed field `k`, with normalization
`ν : X̃ ⟶ X`, and let `L` be very ample on `X̃` (relative to `k`). There are a nonempty open `U` of
nonsingular points of `X` over which `ν` is an isomorphism and an effective Cartier divisor `D` on
`X̃` with `𝒪(D) ≅ L` that is trivial near every point outside `ν⁻¹(U)`. -/
theorem exists_isIso_effective_divisor_of_isVeryAmpleRelative {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) {L : (Hartshorne.absoluteNormalization X).Modules}
    (hL : Hartshorne.IsVeryAmpleRelative (Hartshorne.absoluteNormalizationMap X ≫ p) L) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ (∀ x ∈ U, X.IsRegularAt x) ∧
      IsIso (Hartshorne.absoluteNormalizationMap X ∣_ U) ∧
      ∃ D : (Hartshorne.absoluteNormalization X).CartierDivisor, D.IsEffective ∧
        Nonempty (D.sheaf ≅ L) ∧
        ∀ x, x ∉ Hartshorne.absoluteNormalizationMap X ⁻¹ᵁ U →
          ∃ V : (Hartshorne.absoluteNormalization X).Opens, x ∈ V ∧ D.restrict V = 0 := by
  classical
  have hf : Hartshorne.FiniteType p := ⟨inferInstance, inferInstance⟩
  obtain ⟨U, hU, hreg, hiso, hS, hmain⟩ :=
    exists_finite_set_divisor_of_isUnit_trivGerm p hf hdim
  have hinv : L.IsInvertible := hL.1
  have hgg := isGloballyGenerated_of_isVeryAmpleRelative hL
  choose V hxV hψ using fun x ↦ Scheme.Modules.exists_over_iso_unit hinv x
  let ψ := fun x ↦ (hψ x).some
  let x₀ : Hartshorne.absoluteNormalization X := genericPoint _
  let S' := insert x₀ hS.toFinset
  have h : ∀ x ∈ S', ∃ t : L.val.obj (op ⊤), IsUnit (trivGerm (ψ x) (hxV x) t) := by
    intro x _
    obtain ⟨t, ht⟩ := exists_mem_nonvanishingLocus_of_isGloballyGenerated hinv hgg x
    exact ⟨t, isUnit_trivGerm_of_mem_nonvanishingLocus (ψ x) (hxV x) ht⟩
  obtain ⟨s, hs⟩ := exists_isUnit_trivGerm
    (Scheme.globalScalar (Hartshorne.absoluteNormalizationMap X ≫ p)) S' V hxV ψ h
  have hs0 : s ≠ 0 := by
    rintro rfl
    have := hs x₀ (Finset.mem_insert_self _ _)
    rw [trivGerm_zero] at this
    exact not_isUnit_zero this
  obtain ⟨D, hDeff, hDL, hDtriv⟩ := hmain L hinv s hs0 fun x hx ↦
    ⟨V x, ψ x, hxV x, hs x (Finset.mem_insert_of_mem (hS.mem_toFinset.mpr hx))⟩
  exact ⟨U, hU, hreg, hiso, D, hDeff, hDL, hDtriv⟩

open Scheme.CartierDivisor in
/-- **Hartshorne III, Exercise 5.8(b).** Let `X` be a proper integral scheme of dimension one over
an algebraically closed field `k`, with normalization `ν : X̃ ⟶ X`, and let `L` be very ample on
`X̃` (relative to `k`). There is an effective Cartier divisor `D` on `X̃` with `𝒪(D) ≅ L` all of
whose points lie over nonsingular points of `X` (`D` is trivial near every point of `X̃` lying over
a singular point). Consequently there is an invertible sheaf `L₀` on `X` with `ν^* L₀ ≅ L`: the
divisor `D` descends to a Cartier divisor `D₀` on `X` with `ν^* 𝒪(D₀) ≅ 𝒪(D)`. -/
theorem exists_pullback_iso_of_isVeryAmpleRelative {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) {L : (Hartshorne.absoluteNormalization X).Modules}
    (hL : Hartshorne.IsVeryAmpleRelative (Hartshorne.absoluteNormalizationMap X ≫ p) L) :
    ∃ D : (Hartshorne.absoluteNormalization X).CartierDivisor, D.IsEffective ∧
      Nonempty (D.sheaf ≅ L) ∧
      (∀ x, ¬ X.IsRegularAt (Hartshorne.absoluteNormalizationMap X x) →
        ∃ V : (Hartshorne.absoluteNormalization X).Opens, x ∈ V ∧ D.restrict V = 0) ∧
      ∃ L₀ : X.Modules, L₀.IsInvertible ∧
        Nonempty ((Scheme.Modules.pullback (Hartshorne.absoluteNormalizationMap X)).obj L₀ ≅ L) := by
  obtain ⟨U, hUne, hreg, hiso, D, hDeff, ⟨e⟩, hDtriv⟩ :=
    exists_isIso_effective_divisor_of_isVeryAmpleRelative p hdim hL
  have hf : Hartshorne.FiniteType p := ⟨inferInstance, inferInstance⟩
  have := Hartshorne.isFinite_absoluteNormalizationMap_of_finiteType_field k X p hf
  have := hiso
  have hν := map_genericPoint_of_isIso_morphismRestrict (Hartshorne.absoluteNormalizationMap X) hUne
  have hcl : IsClosedMap (Hartshorne.absoluteNormalizationMap X).base :=
    (Hartshorne.absoluteNormalizationMap X).isClosedMap
  have hsurj := surjective_genericFunctionFieldMap_of_isIso_morphismRestrict _ hν hcl
    (Scheme.genericPoint_mem_opens_of_mem hUne.some_mem)
  obtain ⟨D₀, hDE⟩ :=
    Scheme.exists_cartierPullbackData_of_isIso_morphismRestrict _ hν hcl hsurj D hDtriv
  have := Scheme.isIso_cartierPullbackMap hDE
  exact ⟨D, hDeff, ⟨e⟩, fun x hx ↦ hDtriv x fun hxU ↦ hx (hreg _ hxU), D₀.sheaf,
    D₀.isInvertible_sheaf, ⟨asIso (Scheme.cartierPullbackMap hDE) ≪≫ e⟩⟩

end

end AlgebraicGeometry
