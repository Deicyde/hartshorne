/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.HomogeneousLocalizedModule
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Degree-zero localizations of a graded module away from an element

Let `S` be an `ℕ`-graded ring, `M` a `ℤ`-graded `S`-module and `f ∈ S_d` with `d > 0`.
This file proves the algebra behind the chart description of `M~` on `D₊(f) ⊆ Proj S`
(Hartshorne II.5.11(b), p. 117):

* for submonoids `T ≤ T'`, the natural map `M_(T) → M_(T')`, `m / s ↦ m / s`;
* for a homogeneous prime `𝔭` with `f ∉ 𝔭`, the map `M_(f) → M_(𝔭)` is the localization of the
  `S_(f)`-module `M_(f)` at the prime of `S_(f)` corresponding to `𝔭`;
* if `S` is Noetherian and `M` is finitely generated, then `M_(f)` is a finitely generated
  `S_(f)`-module.

## Main definitions and results

* `Hartshorne.HomogeneousLocalizedModule.mapOfLE`: the map `M_(T) → M_(T')` for `T ≤ T'`.
* `Hartshorne.HomogeneousLocalizedModule.isLocalizedModule_mapOfLE`: the localization lemma.
* `Hartshorne.HomogeneousLocalizedModule.finite_away`: finiteness of `M_(f)`.
-/

namespace Hartshorne

open HomogeneousLocalization DirectSum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {M σM : Type*} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
  {ℳ : ℤ → σM} [SetLike.GradedSMul 𝒜 ℳ]

section Decompose

variable [DirectSum.Decomposition ℳ]

/-- The homogeneous components of `c • m` for homogeneous `m ∈ M_i`: the component of degree
`n + i` is `c_n • m`. -/
theorem decompose_smul_of_mem_add {i : ℤ} {m : M} (hm : m ∈ ℳ i) (c : A) (n : ℕ) :
    (decompose ℳ (c • m) ((n : ℤ) + i) : M) = (decompose 𝒜 c n : A) • m := by
  classical
  induction c using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous k c =>
    obtain ⟨c, hc⟩ := c
    have hcm : c • m ∈ ℳ ((k : ℤ) + i) := smul_mem_graded_nat 𝒜 ℳ hc hm
    by_cases hkn : k = n
    · subst hkn
      rw [decompose_of_mem_same _ hcm, decompose_of_mem_same _ hc]
    · rw [decompose_of_mem_ne _ hcm (by omega), decompose_of_mem_ne _ hc hkn, zero_smul]
  | add a b ha hb => rw [add_smul, decompose_add, add_apply, AddMemClass.coe_add, ha, hb,
      decompose_add, add_apply, AddMemClass.coe_add, add_smul]

include 𝒜 in
/-- The homogeneous components of `c • m` for homogeneous `m ∈ M_i` vanish in degrees below
`i`. -/
theorem decompose_smul_of_mem_of_lt {i j : ℤ} {m : M} (hm : m ∈ ℳ i) (c : A) (hji : j < i) :
    (decompose ℳ (c • m) j : M) = 0 := by
  classical
  induction c using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous k c =>
    obtain ⟨c, hc⟩ := c
    rw [decompose_of_mem_ne _ (smul_mem_graded_nat 𝒜 ℳ hc hm) (by omega)]
  | add a b ha hb => rw [add_smul, decompose_add, add_apply, AddMemClass.coe_add, ha, hb, add_zero]

end Decompose

namespace HomogeneousLocalizedModule

variable {T T' : Submonoid A}

/-- The map `T⁻¹ M → T'⁻¹ M` for `T ≤ T'`. -/
noncomputable def localizedMapOfLE (h : T ≤ T') : LocalizedModule T M →+ LocalizedModule T' M where
  toFun y := y.liftOn (fun p => LocalizedModule.mk p.1 ⟨p.2.1, h p.2.2⟩) fun p p' e => by
    obtain ⟨u, hu⟩ := e
    exact LocalizedModule.mk_eq.2 ⟨⟨u, h u.2⟩, hu⟩
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.liftOn_mk, LocalizedModule.zero_mk]
  map_add' y z := by
    induction y, z using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk,
        LocalizedModule.liftOn_mk, LocalizedModule.mk_add_mk]
      rfl

@[simp]
theorem localizedMapOfLE_mk (h : T ≤ T') (m : M) (s : T) :
    localizedMapOfLE h (LocalizedModule.mk m s) = LocalizedModule.mk m ⟨s.1, h s.2⟩ := by
  rw [localizedMapOfLE, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LocalizedModule.liftOn_mk]

theorem localizedMapOfLE_smul (h : T ≤ T') (a : A) (s : T) (y : LocalizedModule T M) :
    localizedMapOfLE h (Localization.mk a s • y) =
      Localization.mk a ⟨s.1, h s.2⟩ • localizedMapOfLE h y := by
  induction y using LocalizedModule.induction_on with
  | h m t =>
    rw [LocalizedModule.mk_smul_mk, localizedMapOfLE_mk, localizedMapOfLE_mk,
      LocalizedModule.mk_smul_mk]
    rfl

variable (𝒜 ℳ) in
/-- The natural map `M_(T) → M_(T')` for `T ≤ T'`, sending `m / s` to `m / s`. -/
noncomputable def mapOfLE (h : T ≤ T') :
    HomogeneousLocalizedModule 𝒜 ℳ T →+ HomogeneousLocalizedModule 𝒜 ℳ T' where
  toFun y := ⟨localizedMapOfLE h y.val, by
    obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := mk_surjective y
    exact ⟨n, m, s, hm, hs, h hsx, by simp⟩⟩
  map_zero' := by
    ext
    exact map_zero (localizedMapOfLE h)
  map_add' y z := by
    ext
    exact map_add (localizedMapOfLE h) y.val z.val

theorem val_mapOfLE (h : T ≤ T') (y : HomogeneousLocalizedModule 𝒜 ℳ T) :
    (mapOfLE 𝒜 ℳ h y).val = localizedMapOfLE h y.val := rfl

@[simp]
theorem mapOfLE_mk (h : T ≤ T') (n : ℕ) (m : M) (hm : m ∈ ℳ n) (s : A) (hs : s ∈ 𝒜 n)
    (hsx : s ∈ T) : mapOfLE 𝒜 ℳ h (mk n m hm s hs hsx) = mk n m hm s hs (h hsx) := by
  ext
  exact localizedMapOfLE_mk h m ⟨s, hsx⟩

theorem _root_.Hartshorne.mapId_mk_val (h : T ≤ T') (z : NumDenSameDeg 𝒜 T) :
    (mapId 𝒜 h (HomogeneousLocalization.mk z)).val =
      Localization.mk (z.num : A) ⟨z.den, h z.den_mem⟩ := by
  rfl

theorem mapOfLE_smul (h : T ≤ T') (c : HomogeneousLocalization 𝒜 T)
    (y : HomogeneousLocalizedModule 𝒜 ℳ T) :
    mapOfLE 𝒜 ℳ h (c • y) = mapId 𝒜 h c • mapOfLE 𝒜 ℳ h y := by
  obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := mk_surjective y
  obtain ⟨⟨i, ⟨a, ha⟩, ⟨b, hb⟩, hbx⟩, rfl⟩ := HomogeneousLocalization.mk_surjective c
  ext
  rw [val_mapOfLE, val_smul, val_smul, val_mapOfLE, mapId_mk_val,
    HomogeneousLocalization.val_mk]
  exact localizedMapOfLE_smul h a ⟨b, hbx⟩ _

variable (𝒜 ℳ) in
/-- `M_(T')` as a module over `S_(T)` for `T ≤ T'`, by restricting scalars along
`S_(T) → S_(T')`. -/
noncomputable abbrev moduleOfLE (h : T ≤ T') :
    Module (HomogeneousLocalization 𝒜 T) (HomogeneousLocalizedModule 𝒜 ℳ T') :=
  Module.compHom _ (mapId 𝒜 h)

variable (𝒜 ℳ) in
/-- The natural map `M_(T) → M_(T')` as an `S_(T)`-linear map. -/
noncomputable def mapOfLELinear (h : T ≤ T') :
    letI := moduleOfLE 𝒜 ℳ h
    HomogeneousLocalizedModule 𝒜 ℳ T →ₗ[HomogeneousLocalization 𝒜 T]
      HomogeneousLocalizedModule 𝒜 ℳ T' :=
  letI := moduleOfLE 𝒜 ℳ h
  { mapOfLE 𝒜 ℳ h with map_smul' := mapOfLE_smul h }

section Away

variable [DirectSum.Decomposition ℳ]

theorem mapId_away_mk_mul_eq_one {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (P : Ideal A) [P.IsPrime]
    (hfP : f ∉ P) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) (haP : a ∉ P) :
    mapId 𝒜 (Submonoid.powers_le.mpr (show f ∈ P.primeCompl from hfP) : Submonoid.powers f ≤ P.primeCompl)
        (Away.mk 𝒜 f_deg n a ha) *
      HomogeneousLocalization.mk (𝒜 := 𝒜) (x := P.primeCompl)
        ⟨n • d, ⟨f ^ n, SetLike.pow_mem_graded n f_deg⟩, ⟨a, ha⟩, haP⟩ = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.mk, mapId_mk_val, HomogeneousLocalization.val_mk,
    Localization.mk_mul, mul_comm a, ← Localization.mk_one]
  exact Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2 ⟨1, by simp⟩)

/-- **The localization lemma** (Hartshorne II.5.11(b), proof). Let `f ∈ S_d` with `d > 0` and let
`𝔭` be a homogeneous prime with `f ∉ 𝔭`. Let `Q ⊆ S_(f)` be the complement of the prime of
`S_(f)` corresponding to `𝔭`, i.e. `a / f^n ∈ Q ↔ a ∉ 𝔭`. Then `M_(f) → M_(𝔭)` is the
localization of the `S_(f)`-module `M_(f)` at `Q`. -/
theorem isLocalizedModule_mapOfLE {f : A} {d : ℕ} (f_deg : f ∈ 𝒜 d) (hd : 0 < d)
    (P : Ideal A) [P.IsPrime] (hP : Ideal.IsHomogeneous 𝒜 P) (hfP : f ∉ P)
    (Q : Submonoid (Away 𝒜 f))
    (hQ : ∀ (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)), Away.mk 𝒜 f_deg n a ha ∈ Q ↔ a ∉ P) :
    letI := moduleOfLE 𝒜 ℳ (Submonoid.powers_le.mpr (show f ∈ P.primeCompl from hfP) : Submonoid.powers f ≤ P.primeCompl)
    IsLocalizedModule Q (mapOfLELinear 𝒜 ℳ (Submonoid.powers_le.mpr (show f ∈ P.primeCompl from hfP))) := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  set h : Submonoid.powers f ≤ P.primeCompl := Submonoid.powers_le.mpr (show f ∈ P.primeCompl from hfP)
  let _ := moduleOfLE 𝒜 ℳ h
  have hfn (n : ℕ) : f ^ n ∈ Submonoid.powers f := ⟨n, rfl⟩
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 f_deg z
    have haP : a ∉ P := (hQ n a ha).1 hz
    have huv := mapId_away_mk_mul_eq_one f_deg P hfP n a ha haP
    set v := HomogeneousLocalization.mk (𝒜 := 𝒜) (x := P.primeCompl)
        ⟨n • (d + 1), ⟨f ^ n, SetLike.pow_mem_graded n f_deg⟩, ⟨a, ha⟩, haP⟩
    rw [Module.End.isUnit_iff]
    constructor
    · intro y₁ y₂ e
      have e' : v • (mapId 𝒜 h (Away.mk 𝒜 f_deg n a ha) • y₁) =
          v • (mapId 𝒜 h (Away.mk 𝒜 f_deg n a ha) • y₂) := congrArg (v • ·) e
      rwa [smul_smul, smul_smul, mul_comm v, huv, one_smul, one_smul] at e'
    · intro y
      refine ⟨v • y, ?_⟩
      change mapId 𝒜 h (Away.mk 𝒜 f_deg n a ha) • v • y = y
      rw [smul_smul, huv, one_smul]
  · intro y
    obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := mk_surjective y
    have hsP : s ∉ P := hsx
    have hm' : s ^ d • m ∈ ℳ ((n • (d + 1) : ℕ) : ℤ) := by
      have := smul_mem_graded_nat 𝒜 ℳ (SetLike.pow_mem_graded d hs) hm
      convert this using 2
      push_cast [smul_eq_mul]
      ring
    have hsd : s ^ (d + 1) ∈ 𝒜 (n • (d + 1)) := by
      convert SetLike.pow_mem_graded (d + 1) hs using 2
      rw [smul_eq_mul, smul_eq_mul, mul_comm]
    have hsdQ : Away.mk 𝒜 f_deg n (s ^ (d + 1)) hsd ∈ Q :=
      (hQ n _ hsd).2 fun hmem => hsP (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hmem)
    refine ⟨⟨mk (n • (d + 1)) (s ^ d • m) hm' (f ^ n) (SetLike.pow_mem_graded n f_deg)
      (hfn n), ⟨_, hsdQ⟩⟩, ?_⟩
    change mapId 𝒜 h (Away.mk 𝒜 f_deg n (s ^ (d + 1)) hsd) • mk n m hm s hs hsx =
      mapOfLE 𝒜 ℳ h _
    ext
    rw [val_smul, mapOfLE_mk, val_mk, val_mk, HomogeneousLocalization.Away.mk, mapId_mk_val]
    change Localization.mk (s ^ (d + 1)) ⟨f ^ n, h (hfn n)⟩ • LocalizedModule.mk m ⟨s, hsx⟩ = _
    rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, one_mul, Submonoid.mk_smul, smul_smul]
    change (f ^ n * s ^ (d + 1)) • m = (f ^ n * s) • s ^ d • m
    rw [smul_smul]
    congr 1
    ring
  · intro y₁ y₂ e
    obtain ⟨n₁, m₁, hm₁, s₁, hs₁, hsx₁, rfl⟩ := mk_surjective y₁
    obtain ⟨n₂, m₂, hm₂, s₂, hs₂, hsx₂, rfl⟩ := mk_surjective y₂
    have e' := congrArg val e
    change (mapOfLE 𝒜 ℳ h _).val = (mapOfLE 𝒜 ℳ h _).val at e'
    rw [mapOfLE_mk, mapOfLE_mk, val_mk, val_mk, LocalizedModule.mk_eq] at e'
    obtain ⟨⟨u, huP⟩, hu⟩ := e'
    simp only [Submonoid.mk_smul] at hu
    set w : M := s₂ • m₁ - s₁ • m₂
    have hw : w ∈ ℳ (((n₂ + n₁ : ℕ) : ℤ)) := by
      refine sub_mem ?_ ?_
      · have := smul_mem_graded_nat 𝒜 ℳ hs₂ hm₁
        rwa [show ((n₂ : ℕ) : ℤ) + n₁ = ((n₂ + n₁ : ℕ) : ℤ) by push_cast; ring] at this
      · have := smul_mem_graded_nat 𝒜 ℳ hs₁ hm₂
        rwa [show ((n₁ : ℕ) : ℤ) + n₂ = ((n₂ + n₁ : ℕ) : ℤ) by push_cast; ring] at this
    have huw : u • w = 0 := by
      simp only [w, smul_sub, hu, sub_self]
    obtain ⟨e, he⟩ : ∃ e, (decompose 𝒜 u e : A) ∉ P := by
      by_contra! H
      exact huP ((hP.mem_iff).2 H)
    set ue : A := ((decompose 𝒜 u e : 𝒜 e) : A)
    have hue : ue ∈ 𝒜 e := (decompose 𝒜 u e).2
    have huew : ue • w = 0 := by
      rw [← decompose_smul_of_mem_add hw u e, huw, decompose_zero, zero_apply,
        ZeroMemClass.coe_zero]
    have hued : ue ^ (d + 1) ∈ 𝒜 (e • (d + 1)) := by
      convert SetLike.pow_mem_graded (d + 1) hue using 2
      rw [smul_eq_mul, smul_eq_mul, mul_comm]
    have huedQ : Away.mk 𝒜 f_deg e (ue ^ (d + 1)) hued ∈ Q :=
      (hQ e _ hued).2 fun hmem => he (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hmem)
    refine ⟨⟨_, huedQ⟩, ?_⟩
    change Away.mk 𝒜 f_deg e (ue ^ (d + 1)) hued • mk n₁ m₁ hm₁ s₁ hs₁ hsx₁ =
      Away.mk 𝒜 f_deg e (ue ^ (d + 1)) hued • mk n₂ m₂ hm₂ s₂ hs₂ hsx₂
    ext
    rw [val_smul, val_smul, val_mk, val_mk, HomogeneousLocalization.Away.val_mk,
      LocalizedModule.mk_smul_mk, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul]
    change (f ^ e * s₂) • ue ^ (d + 1) • m₁ = (f ^ e * s₁) • ue ^ (d + 1) • m₂
    have key : (f ^ e * s₂) • ue ^ (d + 1) • m₁ - (f ^ e * s₁) • ue ^ (d + 1) • m₂ =
        (f ^ e * ue ^ d) • (ue • w) := by
      simp only [w, smul_sub, smul_smul]
      congr 1 <;> congr 1 <;> ring
    rw [← sub_eq_zero, key, huew, smul_zero]

end Away

section Finite

variable (𝒜 ℳ) in
/-- For fixed homogeneous `s ∈ T` of degree `n`, the map `M_n → M_(T)`, `m ↦ m / s`. -/
noncomputable def mkHom (n : ℕ) (s : A) (hs : s ∈ 𝒜 n) (hsx : s ∈ T) :
    ℳ n →+ HomogeneousLocalizedModule 𝒜 ℳ T where
  toFun x := mk n (x : M) x.2 s hs hsx
  map_zero' := by
    ext
    rw [val_mk, val_zero, ZeroMemClass.coe_zero, LocalizedModule.zero_mk]
  map_add' x y := by
    ext
    rw [val_add, val_mk, val_mk, val_mk, LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, one_mul, Submonoid.mk_smul, AddMemClass.coe_add, smul_add, smul_smul]
    rfl

@[simp]
theorem mkHom_apply (n : ℕ) (s : A) (hs : s ∈ 𝒜 n) (hsx : s ∈ T) (x : ℳ n) :
    mkHom 𝒜 ℳ n s hs hsx x = mk n (x : M) x.2 s hs hsx := rfl

variable [DirectSum.Decomposition ℳ]

/-- **Finiteness of `M_(f)`** (Hartshorne II.5.11(c), proof). If `S` is Noetherian and `M` is a
finitely generated `S`-module, then `M_(f)` is a finitely generated `S_(f)`-module for every
homogeneous `f` of positive degree. -/
theorem finite_away [IsNoetherianRing A] [Module.Finite A M] {f : A} {d : ℕ}
    (f_deg : f ∈ 𝒜 d) (hd : 0 < d) :
    Module.Finite (Away 𝒜 f) (HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f)) := by
  classical
  set G : Set M := {m | ∃ k : ℕ, m ∈ ℳ ((k • d : ℕ) : ℤ)}
  have hfg : (Submodule.span A G).FG := IsNoetherian.noetherian _
  obtain ⟨t, htG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).1 hfg
  have ht : ∀ b : t, ∃ k : ℕ, b.1 ∈ ℳ ((k • d : ℕ) : ℤ) := fun b => htG b.2
  choose kb hkb using ht
  have hfn (n : ℕ) : f ^ n ∈ Submonoid.powers f := ⟨n, rfl⟩
  let g : t → HomogeneousLocalizedModule 𝒜 ℳ (Submonoid.powers f) := fun b =>
    mk (kb b • d) b.1 (hkb b) (f ^ kb b) (SetLike.pow_mem_graded _ f_deg) (hfn _)
  refine ⟨(Submodule.fg_def).2 ⟨Set.range g, Set.finite_range g, eq_top_iff.2 fun y _ => ?_⟩⟩
  obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := mk_surjective y
  obtain ⟨k, hk⟩ := id hsx
  beta_reduce at hk
  subst hk
  by_cases hfk : f ^ k = 0
  · convert zero_mem (Submodule.span (Away 𝒜 f) (Set.range g))
    ext
    rw [val_mk, val_zero, ← LocalizedModule.zero_mk ⟨f ^ k, hsx⟩, LocalizedModule.mk_eq]
    exact ⟨⟨f ^ k, hsx⟩, by simp [hfk]⟩
  obtain rfl : n = k • d :=
    DirectSum.degree_eq_of_mem_mem 𝒜 hs (SetLike.pow_mem_graded k f_deg) hfk
  have hmG : m ∈ Submodule.span A (t : Set M) := hspan ▸ Submodule.subset_span ⟨k, hm⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.1 hmG
  have hcomp : (⟨m, hm⟩ : ℳ ((k • d : ℕ) : ℤ)) =
      ∑ b : t, decompose ℳ (c b • b.1) ((k • d : ℕ) : ℤ) := by
    rw [← DFinsupp.finsetSum_apply, ← decompose_sum, hc, decompose_of_mem ℳ hm,
      DirectSum.of_eq_same]
  have hy : mk (k • d) m hm (f ^ k) hs hsx =
      mkHom 𝒜 ℳ (k • d) (f ^ k) hs hsx ⟨m, hm⟩ := rfl
  rw [hy, hcomp, map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hle : kb b ≤ k
  · have hcb : (decompose 𝒜 (c b) ((k - kb b) • d) : A) ∈ 𝒜 ((k - kb b) • d) :=
      (decompose 𝒜 (c b) ((k - kb b) • d)).2
    have hdeg : ((((k - kb b) • d : ℕ) : ℤ) + ((kb b • d : ℕ) : ℤ)) = ((k • d : ℕ) : ℤ) := by
      rw [← Nat.cast_add, ← add_smul, Nat.sub_add_cancel hle]
    have hval : (decompose ℳ (c b • b.1) ((k • d : ℕ) : ℤ) : M) =
        (decompose 𝒜 (c b) ((k - kb b) • d) : A) • b.1 := by
      rw [← hdeg, decompose_smul_of_mem_add (𝒜 := 𝒜) (hkb b)]
    have key : mkHom 𝒜 ℳ (k • d) (f ^ k) hs hsx (decompose ℳ (c b • b.1) ((k • d : ℕ) : ℤ)) =
        Away.mk 𝒜 f_deg (k - kb b) _ hcb • g b := by
      ext
      rw [mkHom_apply, val_mk, val_smul, val_mk, HomogeneousLocalization.Away.val_mk,
        LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      rw [hval]
      simp only [one_smul, Submonoid.mk_smul, Submonoid.mk_mul_mk]
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self b))
  · have hzero : decompose ℳ (c b • b.1) ((k • d : ℕ) : ℤ) = 0 := by
      ext
      rw [decompose_smul_of_mem_of_lt (𝒜 := 𝒜) (hkb b)]
      · rfl
      · have : k • d < kb b • d := Nat.mul_lt_mul_of_pos_right (not_le.1 hle) hd
        exact_mod_cast this
    rw [hzero, map_zero]
    exact zero_mem _

end Finite

end HomogeneousLocalizedModule

end Hartshorne
