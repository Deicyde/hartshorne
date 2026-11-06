/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FiniteType

/-!
# A generically finite morphism is finite over a dense open

Hartshorne, *Algebraic Geometry*, II, Exercise 3.7.

A morphism `f : X ⟶ Y` with `Y` irreducible is generically finite when the fibre
`f⁻¹(η)` over the generic point `η` of `Y` is a finite set. If `f` is dominant, generically
finite and of finite type (locally of finite type and quasi-compact), and `X` and `Y` are
integral, then `f` is finite over a dense open subset of `Y`.

Proof outline. Choose an affine open `V = Spec A` of `Y` and an affine open `W = Spec B`
of `X` inside `f⁻¹(V)`. Since the generic fibre is finite and `f` is of finite type, the
generic fibre is discrete, so it consists of the generic point of `X` alone and lies in `W`.
The complement of `W` in the quasi-compact open `f⁻¹(V)` therefore lies over a proper
closed subset of `V`, which is avoided by a basic open `D(r)`. Algebraically, `B ⊗ Frac A`
is of finite type over `Frac A` with finitely many primes, hence finite; clearing
denominators in integral equations for generators of `B` gives `c ≠ 0` with `B_c` finite
over `A_c`. Then `f` is finite over `D(rc)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

universe u

namespace Hartshorne

/-- If `B` is of finite type over a domain `A` and only finitely many primes of `B` lie over
the zero ideal of `A`, then every element of `B` becomes integral over `A` after
multiplication by a nonzero element of `A`. -/
theorem exists_isIntegral_smul_of_finite_genericFiber
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (hfib : {q : PrimeSpectrum B | ∀ a : A, a ≠ 0 → algebraMap A B a ∉ q.asIdeal}.Finite)
    (t : B) : ∃ m : A, m ≠ 0 ∧ IsIntegral A (m • t) := by
  let M : Submonoid A := A⁰
  let K := Localization M
  let L := Localization (Algebra.algebraMapSubmonoid B M)
  have : Finite (PrimeSpectrum L) := by
    have := hfib.to_subtype
    refine Finite.of_injective (β := {q : PrimeSpectrum B |
        ∀ a : A, a ≠ 0 → algebraMap A B a ∉ q.asIdeal})
      (fun P => ⟨PrimeSpectrum.comap (algebraMap B L) P, ?_⟩) ?_
    · intro a ha hmem
      have hu : IsUnit (algebraMap B L (algebraMap A B a)) :=
        IsLocalization.map_units L
          (⟨algebraMap A B a, a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩ :
            Algebra.algebraMapSubmonoid B M)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
    · intro P Q h
      exact PrimeSpectrum.localization_comap_injective L (Algebra.algebraMapSubmonoid B M)
        (congrArg Subtype.val h)
  have : Algebra.FiniteType K L := by
    have : IsLocalization (M.map (algebraMap A B)) L :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid B M) L)
    have h := RingHom.finiteType_localizationPreserves (algebraMap A B) M K L
      (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact h
  have : Algebra.QuasiFinite K L :=
    Algebra.QuasiFinite.iff_finite_comap_preimage_singleton.mpr fun _ => Set.toFinite _
  have : Module.Finite K L := .of_quasiFinite
  have hint : IsIntegral K (algebraMap B L t) := Algebra.IsIntegral.isIntegral _
  obtain ⟨⟨m, hm⟩, hmint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hint
  have hm' : IsIntegral A (algebraMap B L (m • t)) := by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B L, ← Algebra.smul_def]
    simpa [Submonoid.smul_def] using hmint
  obtain ⟨m', hm'M, h'⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map M hm'
  refine ⟨m' * m, mul_ne_zero (nonZeroDivisors.ne_zero hm'M) (nonZeroDivisors.ne_zero hm), ?_⟩
  rwa [mul_smul]

/-- If `φ : A →+* B` is of finite type, `A` is a domain, and only finitely many primes of `B`
lie over the zero ideal of `A`, then there is `c ≠ 0` in `A` such that `B_d` is finite over
`A_d` for every multiple `d` of `c`. -/
theorem exists_finite_awayMap_of_finite_genericFiber
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] (φ : A →+* B) (hφ : φ.FiniteType)
    (hfib : {q : PrimeSpectrum B | ∀ a : A, a ≠ 0 → φ a ∉ q.asIdeal}.Finite) :
    ∃ c : A, c ≠ 0 ∧ ∀ d : A, c ∣ d → ∀ (R' S' : Type u) [CommRing R'] [CommRing S']
      [Algebra A R'] [Algebra B S'] [IsLocalization.Away d R'] [IsLocalization.Away (φ d) S'],
      (IsLocalization.Away.map R' S' φ d).Finite := by
  classical
  algebraize [φ]
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  choose n hn0 hn using fun t : B => exists_isIntegral_smul_of_finite_genericFiber hfib t
  refine ⟨∏ t ∈ s, n t, Finset.prod_ne_zero_iff.mpr fun t _ => hn0 t, ?_⟩
  intro d hd R' S' _ _ _ _ _ _
  refine RingHom.finite_iff_isIntegral_and_finiteType.mpr
    ⟨?_, RingHom.finiteType_localizationPreserves.away φ d R' S' hφ⟩
  let ψ := IsLocalization.Away.map R' S' φ d
  let _ : Algebra R' S' := ψ.toAlgebra
  have hcomp : (algebraMap R' S').comp (algebraMap A R') = (algebraMap B S').comp φ :=
    RingHom.ext fun a => by
      simp [ψ, RingHom.algebraMap_toAlgebra, IsLocalization.Away.map]
  have hunit : ∀ a : A, a ∣ d → IsUnit (algebraMap A R' a) := fun a ha =>
    isUnit_of_dvd_unit (map_dvd _ ha) (IsLocalization.Away.algebraMap_isUnit d)
  have hB : ∀ b : B, IsIntegral R' (algebraMap B S' b) := by
    intro b
    have hb : b ∈ Algebra.adjoin A (s : Set B) := hs ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      have h1 : IsIntegral R' (algebraMap B S' (n x • x)) :=
        IsIntegral.map_of_comp_eq (algebraMap A R') (algebraMap B S') hcomp (hn x)
      obtain ⟨u, hu⟩ := hunit (n x) ((Finset.dvd_prod_of_mem n hx).trans hd)
      have h2 : algebraMap B S' x =
          algebraMap R' S' (↑u⁻¹ : R') * algebraMap B S' (n x • x) := by
        rw [Algebra.smul_def, map_mul, ← mul_assoc]
        have : algebraMap B S' (algebraMap A B (n x)) = algebraMap R' S' (algebraMap A R' (n x)) :=
          (congrArg (fun g => g (n x)) hcomp).symm
        rw [this, ← map_mul, ← hu, Units.inv_mul, map_one, one_mul]
      rw [h2]
      exact isIntegral_algebraMap.mul h1
    | algebraMap a =>
      have : algebraMap B S' (algebraMap A B a) = algebraMap R' S' (algebraMap A R' a) :=
        (congrArg (fun g => g a) hcomp).symm
      rw [this]
      exact isIntegral_algebraMap
    | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy
  intro y
  change IsIntegral R' y
  obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers (φ d)) y
  obtain ⟨u, hu⟩ : IsUnit (algebraMap A R' (d ^ k)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit d).pow k
  have hy' : y = algebraMap B S' b * algebraMap R' S' (↑u⁻¹ : R') := by
    simp only at hy
    rw [← hy]
    have : algebraMap B S' (φ d ^ k) = algebraMap R' S' (algebraMap A R' (d ^ k)) := by
      rw [← map_pow]; exact (congrArg (fun g => g (d ^ k)) hcomp).symm
    rw [this, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  rw [hy']
  exact (hB b).mul isIntegral_algebraMap

/-- Let `ψ : A →+* R` with `A` a domain, and let `C` be a closed subset of `Spec R` none of
whose points lies over the zero ideal of `A`. Then a single nonzero element of `A` maps into
every prime of `C`. -/
theorem exists_ne_zero_forall_mem_of_isClosed
    {A R : Type*} [CommRing A] [IsDomain A] [CommRing R] (ψ : A →+* R)
    {C : Set (PrimeSpectrum R)} (hC : IsClosed C)
    (h : ∀ q ∈ C, ∃ a : A, a ≠ 0 ∧ ψ a ∈ q.asIdeal) :
    ∃ a : A, a ≠ 0 ∧ ∀ q ∈ C, ψ a ∈ q.asIdeal := by
  by_contra hcon
  push Not at hcon
  let I := PrimeSpectrum.vanishingIdeal C
  let S : Submonoid R := (A⁰).map ψ
  have hdisj : Disjoint (S : Set R) (I : Set R) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haI
    obtain ⟨q, hq, hnot⟩ := hcon a (nonZeroDivisors.ne_zero ha)
    exact hnot ((PrimeSpectrum.mem_vanishingIdeal C _).mp haI q hq)
  obtain ⟨p, hp, hIp, hpS⟩ := Ideal.exists_le_prime_disjoint I S hdisj.symm
  have hq : (⟨p, hp⟩ : PrimeSpectrum R) ∈ C := by
    rw [← hC.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hIp
  obtain ⟨a, ha, hap⟩ := h _ hq
  have hmem : ψ a ∈ S := ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩
  exact Set.disjoint_left.mp hpS hap hmem

/-- In an integral scheme, a point of an affine open `V` lying in every basic open `D(a)` with
`a ≠ 0` is the generic point. -/
theorem eq_genericPoint_of_forall_mem_basicOpen {Y : Scheme.{u}} [IsIntegral Y]
    {V : Y.Opens} (hV : IsAffineOpen V) {y : Y} (hy : y ∈ V)
    (h : ∀ a : Γ(Y, V), a ≠ 0 → y ∈ Y.basicOpen a) : y = genericPoint Y := by
  by_contra hne
  have hns : ¬ y ⤳ genericPoint Y := fun hs =>
    hne (hs.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ y))).eq
  rw [specializes_iff_forall_open] at hns
  push Not at hns
  obtain ⟨s, hs, hηs, hys⟩ := hns
  have hηV : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr ⟨y, trivial, hy⟩
  obtain ⟨a, hle, hηa⟩ := hV.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨genericPoint Y, hηs⟩ hηV
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hηa
  exact hys (hle (h a ha))

/-- A dominant morphism of integral schemes maps the generic point to the generic point. -/
theorem map_genericPoint_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  have := (genericPoint_spec X).image f.continuous
  rwa [Set.image_univ, f.denseRange.closure_range] at this

/-- For a dominant morphism of integral schemes, locally of finite type, with finite generic
fibre, the generic fibre consists of the generic point alone. -/
theorem eq_genericPoint_of_finite_genericFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f]
    (hf : (f ⁻¹' {genericPoint Y}).Finite) {x : X} (hx : f x = genericPoint Y) :
    x = genericPoint X := by
  have hξ := map_genericPoint_of_isDominant f
  have : Finite (f.fiber (genericPoint Y)) := (f.fiberHomeo _).finite_iff.mpr hf
  have : DiscreteTopology (f ⁻¹' {genericPoint Y}) :=
    (f.fiberHomeo _).discreteTopology
  have hs : (⟨genericPoint X, hξ⟩ : f ⁻¹' {genericPoint Y}) ⤳ ⟨x, hx⟩ := by
    rw [subtype_specializes_iff]
    exact (genericPoint_spec X).specializes trivial
  exact (congrArg Subtype.val hs.eq).symm

/-- Points of an affine open `W ≤ f⁻¹(V)` lie over the basic open `D(a)` of `V` exactly when the
image of `a` in `Γ(X, W)` avoids the corresponding prime. -/
theorem mem_basicOpen_fromSpec_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens} {W : X.Opens}
    (hW : IsAffineOpen W) (e : W ≤ f ⁻¹ᵁ V) (q : PrimeSpectrum Γ(X, W)) (a : Γ(Y, V)) :
    f (hW.fromSpec q) ∈ Y.basicOpen a ↔ f.appLE V W e a ∉ q.asIdeal := by
  have h1 : hW.fromSpec q ∈ X.basicOpen (f.appLE V W e a) ↔
      q ∈ PrimeSpectrum.basicOpen (f.appLE V W e a) := by
    rw [← hW.fromSpec_preimage_basicOpen]; rfl
  have hq : hW.fromSpec q ∈ W := by
    rw [← SetLike.mem_coe, ← hW.range_fromSpec]; exact Set.mem_range_self q
  rw [Scheme.basicOpen_appLE] at h1
  simp only [TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage, hq, true_and,
    PrimeSpectrum.mem_basicOpen] at h1
  exact h1

set_option backward.isDefEq.respectTransparency false in
/-- If `f⁻¹(D(d))` lies in an affine open `W ≤ f⁻¹(V)` and the localized coordinate ring map
`Γ(Y, V)_d → Γ(X, W)_d` is finite, then `f` is finite over `D(d)`. -/
theorem isFinite_morphismRestrict_basicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens}
    (hV : IsAffineOpen V) {W : X.Opens} (hW : IsAffineOpen W) (e : W ≤ f ⁻¹ᵁ V) (d : Γ(Y, V))
    (hle : f ⁻¹ᵁ Y.basicOpen d ≤ W)
    (hfin : letI := hV.isLocalization_basicOpen d
      letI := hW.isLocalization_basicOpen (f.appLE V W e d)
      (IsLocalization.Away.map Γ(Y, Y.basicOpen d) Γ(X, X.basicOpen (f.appLE V W e d))
        (f.appLE V W e).hom d).Finite) :
    IsFinite (f ∣_ Y.basicOpen d) := by
  have hEq : X.basicOpen (f.appLE V W e d) = f ⁻¹ᵁ Y.basicOpen d := by
    rw [Scheme.basicOpen_appLE]; exact inf_eq_right.mpr hle
  have : IsAffine (Y.basicOpen d).toScheme := hV.basicOpen d
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
  refine ⟨?_, ?_⟩
  · change IsAffineOpen (f ⁻¹ᵁ Y.basicOpen d)
    rw [← hEq]; exact hW.basicOpen _
  · rw [morphismRestrict_appTop, CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_right_isIso]
    change (Scheme.Hom.app f ((Y.basicOpen d).ι ''ᵁ ⊤)).hom.Finite
    rw [Scheme.Opens.ι_image_top, ← Scheme.Hom.appLE_eq_app]
    rw [Scheme.Hom.appLE_congr f le_rfl rfl hEq.symm (fun g => g.hom.Finite)]
    rw [IsAffineOpen.appLE_eq_away_map f hV hW e d]
    exact hfin

/-- **Hartshorne II, Exercise 3.7.** Let `f : X ⟶ Y` be a dominant morphism of finite type
between integral schemes which is generically finite, that is, the fibre over the generic point
of `Y` is finite. Then there is a dense open `U ⊆ Y` such that `f⁻¹(U) ⟶ U` is finite. -/
theorem exists_dense_isFinite_morphismRestrict_of_genericallyFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : (f ⁻¹' {genericPoint Y}).Finite) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (f ∣_ U) := by
  have hξ := map_genericPoint_of_isDominant f
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have : Nonempty V := ⟨⟨genericPoint Y, hηV⟩⟩
  have hξV : genericPoint X ∈ (f ⁻¹ᵁ V : Set X) := by
    change f (genericPoint X) ∈ V
    rw [hξ]; exact hηV
  obtain ⟨_, ⟨W, hW, rfl⟩, hξW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hξV (f ⁻¹ᵁ V).2
  have hW' : IsAffineOpen W := hW
  have e : W ≤ f ⁻¹ᵁ V := hWV
  have hfibW : ∀ x, f x = genericPoint Y → x ∈ W := fun x hx =>
    (eq_genericPoint_of_finite_genericFiber f hf hx) ▸ hξW
  -- the complement of `W` in `f⁻¹ V` lies over a proper closed subset of `V`
  obtain ⟨R, p, hp⟩ := isCompact_iff_exists.mp (f.isCompact_preimage hV'.isCompact)
  have eT : (⊤ : (Spec R).Opens) ≤ (p ≫ f) ⁻¹ᵁ V := by
    intro z _
    have : p z ∈ (f ⁻¹ᵁ V : Set X) := hp ▸ Set.mem_range_self z
    exact this
  have hT := isAffineOpen_top (Spec R)
  let C : Set (PrimeSpectrum Γ(Spec R, ⊤)) := (fun q => p (hT.fromSpec q)) ⁻¹' (W : Set X)ᶜ
  have hC : IsClosed C :=
    W.isOpen.isClosed_compl.preimage (p.continuous.comp hT.fromSpec.continuous)
  obtain ⟨r, hr0, hr⟩ := exists_ne_zero_forall_mem_of_isClosed ((p ≫ f).appLE V ⊤ eT).hom hC (by
    intro q hq
    have hfx : (p ≫ f) (hT.fromSpec q) ∈ V := eT trivial
    have hne : (p ≫ f) (hT.fromSpec q) ≠ genericPoint Y := fun h => hq (hfibW _ h)
    by_contra hcon
    push Not at hcon
    exact hne (eq_genericPoint_of_forall_mem_basicOpen hV' hfx fun a ha =>
      (mem_basicOpen_fromSpec_iff (p ≫ f) hT eT q a).mpr (hcon a ha)))
  have hrW : f ⁻¹ᵁ Y.basicOpen r ≤ W := by
    intro x hx
    have hxV : x ∈ (f ⁻¹ᵁ V : Set X) := Y.basicOpen_le r hx
    rw [← hp] at hxV
    obtain ⟨z, rfl⟩ := hxV
    obtain ⟨q, rfl⟩ : z ∈ Set.range hT.fromSpec := by rw [hT.range_fromSpec]; trivial
    by_contra hxW
    exact ((mem_basicOpen_fromSpec_iff (p ≫ f) hT eT q r).mp hx) (hr q hxW)
  -- generic finiteness of the coordinate ring map of `W ⟶ V`
  obtain ⟨c, hc0, hc⟩ := exists_finite_awayMap_of_finite_genericFiber (f.appLE V W e).hom
    (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨V, hV⟩ ⟨W, hW⟩ e)
    (by
      refine (hf.preimage hW'.fromSpec.isOpenEmbedding.injective.injOn).subset ?_
      intro q hq
      have hqW : hW'.fromSpec q ∈ W := by
        rw [← SetLike.mem_coe, ← hW'.range_fromSpec]; exact Set.mem_range_self q
      exact eq_genericPoint_of_forall_mem_basicOpen hV' (e hqW) fun a ha =>
        (mem_basicOpen_fromSpec_iff f hW' e q a).mpr (hq a ha))
  refine ⟨Y.basicOpen (r * c), ?_, ?_⟩
  · refine (Y.basicOpen (r * c)).isOpen.dense ?_
    rw [Set.nonempty_iff_ne_empty, Ne, TopologicalSpace.Opens.coe_eq_empty,
      basicOpen_eq_bot_iff]
    exact mul_ne_zero hr0 hc0
  · let _ := hV'.isLocalization_basicOpen (r * c)
    let _ := hW'.isLocalization_basicOpen (f.appLE V W e (r * c))
    refine isFinite_morphismRestrict_basicOpen f hV' hW' e (r * c) ?_
      (hc (r * c) (dvd_mul_left c r) _ _)
    intro x hx
    have : f x ∈ Y.basicOpen (r * c) := hx
    rw [Scheme.basicOpen_mul] at this
    exact hrW this.1

end Hartshorne
