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
with normalization `ν : X̃ ⟶ X`. There is a finite set `S` of points of `X̃` such that for every
invertible sheaf `L` on `X̃` and every nonzero global section `s` of `L` generating `L` at each
point of `S` (for some trivialization near the point), the divisor of zeros `D = (s)₀` is
effective, `𝒪(D) ≅ L`, and `D` is trivial near every point lying over a singular point of `X`. -/
theorem exists_finite_set_divisor_of_isUnit_trivGerm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) (hf : Hartshorne.FiniteType f)
    (hdim : topologicalKrullDim X = 1) :
    ∃ S : Set (Hartshorne.absoluteNormalization X), S.Finite ∧
      ∀ (L : (Hartshorne.absoluteNormalization X).Modules), L.IsInvertible →
        ∀ s : L.val.obj (op ⊤), s ≠ 0 →
          (∀ x ∈ S, ∃ (V : (Hartshorne.absoluteNormalization X).Opens)
            (ψ : L.over V ≅ SheafOfModules.unit _) (hx : x ∈ V), IsUnit (trivGerm ψ hx s)) →
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

open Scheme.CartierDivisor in
/-- **Hartshorne III, Exercise 5.8(b), the divisor.** Let `X` be a proper integral scheme of
dimension one over an algebraically closed field `k`, with normalization `ν : X̃ ⟶ X`, and let
`L` be very ample on `X̃` (relative to `k`). There is an effective Cartier divisor `D` on `X̃`
with `𝒪(D) ≅ L` all of whose points lie over nonsingular points of `X`: `D` is trivial near
every point of `X̃` lying over a singular point. -/
theorem exists_effective_divisor_of_isVeryAmpleRelative {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) {L : (Hartshorne.absoluteNormalization X).Modules}
    (hL : Hartshorne.IsVeryAmpleRelative (Hartshorne.absoluteNormalizationMap X ≫ p) L) :
    ∃ D : (Hartshorne.absoluteNormalization X).CartierDivisor, D.IsEffective ∧
      Nonempty (D.sheaf ≅ L) ∧
      ∀ x, ¬ X.IsRegularAt (Hartshorne.absoluteNormalizationMap X x) →
        ∃ V : (Hartshorne.absoluteNormalization X).Opens, x ∈ V ∧ D.restrict V = 0 := by
  classical
  have hf : Hartshorne.FiniteType p := ⟨inferInstance, inferInstance⟩
  obtain ⟨S, hS, hmain⟩ := exists_finite_set_divisor_of_isUnit_trivGerm p hf hdim
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
  exact hmain L hinv s hs0 fun x hx ↦
    ⟨V x, ψ x, hxV x, hs x (Finset.mem_insert_of_mem (hS.mem_toFinset.mpr hx))⟩

end

end AlgebraicGeometry
