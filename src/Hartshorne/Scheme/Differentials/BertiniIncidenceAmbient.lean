/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceOverSpec
import Hartshorne.Scheme.ProjGradedModuleSheafChart
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The ambient space of the Bertini incidence correspondence

Let `k` be a field and let `X` be a `k`-scheme with structure morphism `q : X ⟶ Spec k`. The
hyperplanes `∑ⱼ aⱼ xⱼ = 0` of `ℙⁿ_k` are parametrised by the dual projective space
`(ℙⁿ_k)^∨ = Proj k[a₀, …, aₙ]`, which we model by `projectiveSpaceScheme k n`: its homogeneous
coordinate `X j` is the coefficient `aⱼ` of the hyperplane. The incidence correspondence of
Bertini's theorem lives in the fibre product `X ×_k (ℙⁿ_k)^∨` (`incidenceAmbient`).

A point `H` of the dual projective space *represents* the coefficient vector `a`
(`Represents a H`) if all the linear forms `aⱼ X_l - a_l X_j` vanish at `H`. When `k` is
algebraically closed and `X` is locally of finite type over `k`, we set up the dictionary between
closed points of `X ×_k (ℙⁿ_k)^∨` and pairs (closed point of `X`, hyperplane):

* `incidenceAmbient_closedPoint`: a closed point `z` projects to closed points of both factors,
  and its second projection represents a nonzero vector;
* `incidenceAmbient_exists_closedPoint`: conversely every closed point `x` of `X` and every
  nonzero vector `a` come from a closed point `z`;
* `represents_mem_basicOpen_iff`: a point representing `a` lies in the chart `D₊(X β)` exactly
  when `a β ≠ 0`;
* `represents_exists_smul_eq`: the vector represented by a point is unique up to a nonzero
  scalar;
* `germ_dualChartRatio_sub_dualConst_mem_maximalIdeal`: at a point representing `a`, the chart
  function `x_j / x_β` takes the value `a j / a β`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BertiniIncidence

section Definitions

variable (k : Type u) [Field k] (n : ℕ)

/-- The structure morphism `(ℙⁿ_k)^∨ ⟶ Spec k` of the dual projective space: the structure
morphism of `Proj` followed by the identification of `k` with the degree-zero part of
`k[a₀, …, aₙ]`. -/
def dualProjectiveSpaceStructure : projectiveSpaceScheme k n ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (homogeneousSubmodule (Fin (n + 1)) k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule (Fin (n + 1)) k 0)))

private theorem bertiniAmbient_finiteType_degreeZero :
    Algebra.FiniteType (homogeneousSubmodule (Fin (n + 1)) k 0) (MvPolynomial (Fin (n + 1)) k) :=
  ⟨Subalgebra.fg_def.2 ⟨_, Set.finite_range (projectiveSpaceGenerators k n (Equiv.refl _)),
    adjoin_projectiveSpaceGenerators k n (Equiv.refl _)⟩⟩

attribute [local instance] bertiniAmbient_finiteType_degreeZero

/-- The dual projective space is proper over `k`. -/
instance isProper_dualProjectiveSpaceStructure : IsProper (dualProjectiveSpaceStructure k n) :=
  (inferInstance : IsProper (Proj.toSpecZero (homogeneousSubmodule (Fin (n + 1)) k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule (Fin (n + 1)) k 0)))))

/-- The dual projective space is locally of finite type over `k`. -/
instance locallyOfFiniteType_dualProjectiveSpaceStructure :
    LocallyOfFiniteType (dualProjectiveSpaceStructure k n) :=
  inferInstance

/-- The point `H` of the dual projective space is the point `[a]`: all the linear forms
`aⱼ X_l - a_l X_j` lie in the homogeneous prime ideal of `H`. -/
def Represents {k : Type u} [Field k] {n : ℕ} (a : Fin (n + 1) → k)
    (H : projectiveSpaceScheme k n) : Prop :=
  ∀ j l, C (a j) * X l - C (a l) * X j ∈
    ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := homogeneousSubmodule (Fin (n + 1)) k) H

/-- The ambient space `X ×_k (ℙⁿ_k)^∨` of the Bertini incidence correspondence. -/
abbrev incidenceAmbient {k : Type u} [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) : Scheme.{u} :=
  pullback q (dualProjectiveSpaceStructure k n)

/-- The chart function `x_j / x_β` on the chart `D₊(X β)` of the dual projective space. -/
def dualChartRatio (β j : Fin (n + 1)) :
    Γ(projectiveSpaceScheme k n, Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) k) (X β)) :=
  Proj.awayToSection (homogeneousSubmodule (Fin (n + 1)) k) (X β) (chartRatio k β j)

/-- The constant function `c` on the dual projective space, pulled back from `Spec k`. -/
def dualConst (c : k) : Γ(projectiveSpaceScheme k n, ⊤) :=
  (dualProjectiveSpaceStructure k n).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)

end Definitions

section Points

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝒮" => homogeneousSubmodule (Fin (n + 1)) k

/-- The homogeneous prime ideal of a point of the dual projective space, as an ideal. -/
private abbrev bertiniPtIdeal (H : projectiveSpaceScheme k n) :
    Ideal (MvPolynomial (Fin (n + 1)) k) :=
  (ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := 𝒮) H).toIdeal

private theorem bertiniAmbient_mem_of_C_mul_mem {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
    {r : k} (hr : r ≠ 0) {p : MvPolynomial (Fin (n + 1)) k} (h : C r * p ∈ I) : p ∈ I := by
  have := I.mul_mem_left (C r⁻¹) h
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hr, C_1, one_mul] at this

private theorem bertiniAmbient_exists_X_notMem (H : projectiveSpaceScheme k n) :
    ∃ β, X β ∉ bertiniPtIdeal H := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply ProjectiveSpectrum.not_irrelevant_le (𝒜 := 𝒮) H
  intro x hx
  exact ((irrelevant_le_span_range_X k).trans
    (Ideal.span_le.2 (Set.range_subset_iff.2 h))) hx

private theorem bertiniAmbient_represents_of_forall {c : Fin (n + 1) → k}
    {H : projectiveSpaceScheme k n} {β : Fin (n + 1)}
    (h : ∀ j, X j - C (c j) * X β ∈ bertiniPtIdeal H) : Represents c H := by
  intro j l
  change _ ∈ bertiniPtIdeal H
  have e : C (c j) * X l - C (c l) * X j =
      C (c j) * (X l - C (c l) * X β) - C (c l) * (X j - C (c j) * X β) := by ring
  rw [e]
  exact sub_mem (Ideal.mul_mem_left _ _ (h l)) (Ideal.mul_mem_left _ _ (h j))

/-- If `H` represents the nonzero vector `a`, then the coordinate `X β` vanishes at `H` exactly
when `a β = 0`. -/
theorem represents_X_mem_iff {a : Fin (n + 1) → k} {H : projectiveSpaceScheme k n}
    (hH : Represents a H) (ha : a ≠ 0) (β : Fin (n + 1)) :
    X β ∈ ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := 𝒮) H ↔ a β = 0 := by
  change X β ∈ bertiniPtIdeal H ↔ a β = 0
  constructor
  · intro hβ
    by_contra haβ
    obtain ⟨γ, hγ⟩ := bertiniAmbient_exists_X_notMem H
    apply hγ
    refine bertiniAmbient_mem_of_C_mul_mem haβ ?_
    have h1 : C (a β) * X γ - C (a γ) * X β ∈ bertiniPtIdeal H := hH β γ
    have h2 := Ideal.mul_mem_left _ (C (a γ)) hβ
    simpa using add_mem h1 h2
  · intro haβ
    obtain ⟨γ, hγ⟩ := Function.ne_iff.1 ha
    refine bertiniAmbient_mem_of_C_mul_mem hγ ?_
    have h1 : C (a γ) * X β - C (a β) * X γ ∈ bertiniPtIdeal H := hH γ β
    simpa [haβ] using h1

/-- A point representing the nonzero vector `a` lies in the chart `D₊(X β)` exactly when
`a β ≠ 0`. -/
theorem represents_mem_basicOpen_iff {a : Fin (n + 1) → k} {H : projectiveSpaceScheme k n}
    (hH : Represents a H) (ha : a ≠ 0) (β : Fin (n + 1)) :
    H ∈ Proj.basicOpen 𝒮 (X β) ↔ a β ≠ 0 :=
  not_congr (represents_X_mem_iff hH ha β)

/-- The nonzero vector represented by a point of the dual projective space is unique up
to a nonzero scalar. -/
theorem represents_exists_smul_eq {a b : Fin (n + 1) → k} {H : projectiveSpaceScheme k n}
    (ha : Represents a H) (hb : Represents b H) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ b = c • a := by
  obtain ⟨β, hβ⟩ := bertiniAmbient_exists_X_notMem H
  have haβ : a β ≠ 0 := fun h => hβ ((represents_X_mem_iff ha ha0 β).2 h)
  have hbβ : b β ≠ 0 := fun h => hβ ((represents_X_mem_iff hb hb0 β).2 h)
  refine ⟨b β / a β, div_ne_zero hbβ haβ, funext fun j => ?_⟩
  have key : a β * b j - b β * a j = 0 := by
    by_contra hne
    apply hβ
    refine bertiniAmbient_mem_of_C_mul_mem hne ?_
    have e : C (a β * b j - b β * a j) * X β =
        C (b β) * (C (a β) * X j - C (a j) * X β) -
          C (a β) * (C (b β) * X j - C (b j) * X β) := by
      simp only [C_sub, C_mul]
      ring
    rw [e]
    exact sub_mem (Ideal.mul_mem_left _ _ (ha β j)) (Ideal.mul_mem_left _ _ (hb β j))
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination key


/-! ### Points on the chart `D₊(X β)` -/

/-- The unique point of `Spec k`. -/
private def bertiniPt (k : Type u) [Field k] : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k

private theorem bertini_C_mul_X_mem (r : k) (j : Fin (n + 1)) : C r * X j ∈ 𝒮 1 := by
  rw [C_mul']
  exact Submodule.smul_mem _ _ (X_mem_homogeneousSubmodule_one k j)

/-- The degree-zero fraction `p / x_β` of a linear form `p`. -/
private def bertiniFrac (β : Fin (n + 1)) (p : MvPolynomial (Fin (n + 1)) k) (hp : p ∈ 𝒮 1) :
    Away 𝒮 (X β) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨p, hp⟩, ⟨X β, X_mem_homogeneousSubmodule_one k β⟩, ⟨1, pow_one _⟩⟩

private theorem bertiniFrac_val_mul (β : Fin (n + 1)) (p : MvPolynomial (Fin (n + 1)) k)
    (hp : p ∈ 𝒮 1) :
    (bertiniFrac β p hp).val *
        algebraMap _ (Localization.Away (X β : MvPolynomial (Fin (n + 1)) k))
          (X β : MvPolynomial (Fin (n + 1)) k) =
      algebraMap _ _ p := by
  rw [bertiniFrac, val_mk, Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec _ _ _

private theorem bertiniChartRatio_val_mul (β j : Fin (n + 1)) :
    (chartRatio k β j).val *
        algebraMap _ (Localization.Away (X β : MvPolynomial (Fin (n + 1)) k))
          (X β : MvPolynomial (Fin (n + 1)) k) =
      algebraMap _ _ (X j : MvPolynomial (Fin (n + 1)) k) := by
  rw [chartRatio_val, Localization.mk_eq_mk']
  simp

private theorem bertiniAway_ext (β : Fin (n + 1)) {x y : Away 𝒮 (X β)}
    (h : x.val * algebraMap _ (Localization.Away (X β : MvPolynomial (Fin (n + 1)) k))
        (X β : MvPolynomial (Fin (n + 1)) k) =
      y.val * algebraMap _ _ (X β : MvPolynomial (Fin (n + 1)) k)) : x = y := by
  apply HomogeneousLocalization.val_injective
  exact (IsLocalization.Away.algebraMap_isUnit
    (X β : MvPolynomial (Fin (n + 1)) k)).mul_right_cancel h

private theorem bertiniFrac_eq (β j l : Fin (n + 1)) (a b : k)
    (hp : C a * X l - C b * X j ∈ 𝒮 1) :
    bertiniFrac β _ hp =
      chartConst k β a * chartRatio k β l - chartConst k β b * chartRatio k β j := by
  apply bertiniAway_ext β
  rw [bertiniFrac_val_mul, val_sub, val_mul, val_mul, chartConst_val, chartConst_val, sub_mul,
    mul_assoc, mul_assoc, bertiniChartRatio_val_mul, bertiniChartRatio_val_mul]
  simp only [map_sub, map_mul]

private theorem bertiniFrac_eq' (β j : Fin (n + 1)) (c : k) (hp : X j - C c * X β ∈ 𝒮 1) :
    bertiniFrac β _ hp = chartRatio k β j - chartConst k β c := by
  have hp' : C 1 * X j - C c * X β ∈ 𝒮 1 := by simpa using hp
  have e := bertiniFrac_eq β β j 1 c hp'
  simpa [chartRatio_self] using e

/-- The chart `Spec k[x]_(x_β) ≅ D₊(X β)` of the dual projective space. -/
private def bertiniAwayι (β : Fin (n + 1)) :
    Spec (CommRingCat.of (Away 𝒮 (X β))) ⟶ projectiveSpaceScheme k n :=
  Proj.awayι 𝒮 (X β) (X_mem_homogeneousSubmodule_one k β) Nat.one_pos

private instance bertiniAwayι_isOpenImmersion (β : Fin (n + 1)) :
    IsOpenImmersion (bertiniAwayι (k := k) β) :=
  (inferInstance : IsOpenImmersion (Proj.awayι 𝒮 (X β) (X_mem_homogeneousSubmodule_one k β)
    Nat.one_pos))

private theorem bertiniAwayι_mem_range (β : Fin (n + 1)) (H : projectiveSpaceScheme k n)
    (h : X β ∉ bertiniPtIdeal H) : H ∈ Set.range (bertiniAwayι β) := by
  have : H ∈ (Proj.awayι 𝒮 (X β) (X_mem_homogeneousSubmodule_one k β) Nat.one_pos).opensRange := by
    rw [Proj.opensRange_awayι]
    exact h
  exact this

/-- The point of the chart `D₊(X β)` cut out by a ring homomorphism `ev : k[x]_(x_β) → k`. -/
private def bertiniChartPoint (β : Fin (n + 1)) (ev : Away 𝒮 (X β) →+* k) :
    projectiveSpaceScheme k n :=
  bertiniAwayι β (Spec.map (CommRingCat.ofHom ev) (bertiniPt k))

private theorem bertiniChartPoint_mem_iff (β : Fin (n + 1)) (ev : Away 𝒮 (X β) →+* k)
    (p : MvPolynomial (Fin (n + 1)) k) (hp : p ∈ 𝒮 1) :
    p ∈ bertiniPtIdeal (bertiniChartPoint β ev) ↔ ev (bertiniFrac β p hp) = 0 := by
  have h := ProjGradedModuleSheaf.awayι_mem_asIdeal_iff 𝒮 (X_mem_homogeneousSubmodule_one k β)
    Nat.one_pos (Spec.map (CommRingCat.ofHom ev) (bertiniPt k))
    ⟨1, ⟨p, hp⟩, ⟨X β, X_mem_homogeneousSubmodule_one k β⟩, ⟨1, pow_one _⟩⟩
  refine h.symm.trans ?_
  change ev (bertiniFrac β p hp) ∈ IsLocalRing.maximalIdeal k ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]

private theorem bertiniAwayι_comp_structure (β : Fin (n + 1)) :
    bertiniAwayι β ≫ dualProjectiveSpaceStructure k n =
      Spec.map (CommRingCat.ofHom (chartConst k β)) := by
  have h := Proj.awayι_toSpecZero_assoc 𝒮 (X β) (X_mem_homogeneousSubmodule_one k β) Nat.one_pos
    (Spec.map (CommRingCat.ofHom (algebraMap k (𝒮 0))))
  rw [← Spec.map_comp] at h
  exact h

private theorem bertiniAmbient_isClosed_of_section [IsAlgClosed k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (s : Spec (CommRingCat.of k) ⟶ Y)
    (hs : s ≫ f = 𝟙 _) (y : Spec (CommRingCat.of k)) : IsClosed {s y} := by
  have h := (pointEquivClosedPoint f ⟨s, hs⟩).2
  rw [Subsingleton.elim y (bertiniPt k)]
  exact h

/-- A closed point of the dual projective space over an algebraically closed field represents a
nonzero vector. -/
theorem exists_represents_of_isClosed [IsAlgClosed k] (H : projectiveSpaceScheme k n)
    (hH : IsClosed {H}) : ∃ a ≠ 0, Represents a H := by
  classical
  obtain ⟨β, hβ⟩ := bertiniAmbient_exists_X_notMem H
  let g := dualProjectiveSpaceStructure k n
  let s := pointOfClosedPoint g H hH
  let ι : Spec (CommRingCat.of (Away 𝒮 (X β))) ⟶ projectiveSpaceScheme k n := bertiniAwayι β
  have hrange : Set.range s ⊆ Set.range ι := by
    rintro _ ⟨y, rfl⟩
    rw [pointOfClosedPoint_apply]
    exact bertiniAwayι_mem_range β H hβ
  let t := IsOpenImmersion.lift ι s hrange
  let ev := (Spec.preimage t).hom
  have ht : Spec.map (CommRingCat.ofHom ev) = t := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hev : ∀ c, ev (chartConst k β c) = c := by
    have h1 : Spec.map (CommRingCat.ofHom ev) ≫ ι ≫ g = 𝟙 _ := by
      rw [ht, IsOpenImmersion.lift_fac_assoc, pointOfClosedPoint_comp]
    rw [bertiniAwayι_comp_structure, ← Spec.map_comp, ← Spec.map_id] at h1
    have h2 := Spec.map_injective h1
    intro c
    simpa using congrArg (fun f => f.hom c) h2
  have hpt : bertiniChartPoint β ev = H := by
    rw [bertiniChartPoint, ht, ← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac,
      pointOfClosedPoint_apply]
  refine ⟨fun j => ev (chartRatio k β j), ?_, ?_⟩
  · intro h
    have := congr_fun h β
    simp [chartRatio_self] at this
  · apply bertiniAmbient_represents_of_forall (β := β)
    intro j
    have hp : X j - C (ev (chartRatio k β j)) * X β ∈ 𝒮 1 :=
      sub_mem (X_mem_homogeneousSubmodule_one k j) (bertini_C_mul_X_mem _ β)
    rw [← hpt, bertiniChartPoint_mem_iff β ev _ hp, bertiniFrac_eq', map_sub, hev, sub_self]

/-- Every nonzero vector is represented by a closed point of the dual projective space. -/
theorem exists_isClosed_represents [IsAlgClosed k] {a : Fin (n + 1) → k} (ha : a ≠ 0) :
    ∃ H : projectiveSpaceScheme k n, IsClosed {H} ∧ Represents a H := by
  classical
  obtain ⟨β, hβ⟩ := Function.ne_iff.1 ha
  let ev : Away 𝒮 (X β) →+* k :=
    (MvPolynomial.eval fun j : {j // j ≠ β} => a j / a β).comp (chartToPoly k β)
  have hev : ∀ c, ev (chartConst k β c) = c := by
    intro c
    have h := RingHom.congr_fun (chartToPoly_comp_chartOfPoly k β) (C c)
    simp only [RingHom.comp_apply, RingHom.id_apply, chartOfPoly, coe_eval₂Hom, eval₂_C] at h
    simp [ev, h]
  have hev' : ∀ j, ev (chartRatio k β j) = a j / a β := by
    intro j
    simp only [ev, RingHom.comp_apply, chartRatio, chartToPoly_mk]
    by_cases hj : j = β
    · subst hj
      rw [chartDehomogenize_X_self, map_one, div_self hβ]
    · rw [chartDehomogenize_X_of_ne k hj, eval_X]
  let ι : Spec (CommRingCat.of (Away 𝒮 (X β))) ⟶ projectiveSpaceScheme k n := bertiniAwayι β
  have hs : (Spec.map (CommRingCat.ofHom ev) ≫ ι) ≫ dualProjectiveSpaceStructure k n = 𝟙 _ := by
    rw [Category.assoc, bertiniAwayι_comp_structure, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    simp [hev]
  refine ⟨bertiniChartPoint β ev, bertiniAmbient_isClosed_of_section _ _ hs _, ?_⟩
  intro j l
  have hp : C (a j) * X l - C (a l) * X j ∈ 𝒮 1 :=
    sub_mem (bertini_C_mul_X_mem _ l) (bertini_C_mul_X_mem _ j)
  change _ ∈ bertiniPtIdeal _
  rw [bertiniChartPoint_mem_iff β ev _ hp, bertiniFrac_eq, map_sub, map_mul, map_mul, hev, hev,
    hev', hev']
  ring


/-! ### Closed points of the incidence ambient space -/

/-- A closed point `z` of `X ×_k (ℙⁿ_k)^∨` projects to closed points of `X` and of
`(ℙⁿ_k)^∨`, and its image in `(ℙⁿ_k)^∨` represents a nonzero vector. -/
theorem incidenceAmbient_closedPoint [IsAlgClosed k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q] (z : incidenceAmbient q n)
    (hz : IsClosed {z}) :
    IsClosed {pullback.fst q (dualProjectiveSpaceStructure k n) z} ∧
      IsClosed {pullback.snd q (dualProjectiveSpaceStructure k n) z} ∧
      ∃ a ≠ 0, Represents a (pullback.snd q (dualProjectiveSpaceStructure k n) z) := by
  let g := dualProjectiveSpaceStructure k n
  let s := pointOfClosedPoint (pullback.fst q g ≫ q) z hz
  have hs : s ≫ pullback.fst q g ≫ q = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hz' : s (bertiniPt k) = z := pointOfClosedPoint_apply _ _ _ _
  have h1 : IsClosed {pullback.fst q g z} := by
    have := bertiniAmbient_isClosed_of_section q (s ≫ pullback.fst q g)
      (by rw [Category.assoc, hs]) (bertiniPt k)
    rwa [Scheme.Hom.comp_apply, hz'] at this
  have h2 : IsClosed {pullback.snd q g z} := by
    have := bertiniAmbient_isClosed_of_section g (s ≫ pullback.snd q g)
      (by rw [Category.assoc, ← pullback.condition, hs]) (bertiniPt k)
    rwa [Scheme.Hom.comp_apply, hz'] at this
  exact ⟨h1, h2, exists_represents_of_isClosed _ h2⟩

/-- Every closed point `x` of `X` and every nonzero vector `a` come from a closed point
`z` of `X ×_k (ℙⁿ_k)^∨` lying over `x` whose image in `(ℙⁿ_k)^∨` represents `a`. -/
theorem incidenceAmbient_exists_closedPoint [IsAlgClosed k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q] (x : X) (hx : IsClosed {x})
    {a : Fin (n + 1) → k} (ha : a ≠ 0) :
    ∃ z : incidenceAmbient q n, IsClosed {z} ∧
      pullback.fst q (dualProjectiveSpaceStructure k n) z = x ∧
      Represents a (pullback.snd q (dualProjectiveSpaceStructure k n) z) := by
  let g := dualProjectiveSpaceStructure k n
  obtain ⟨H, hH, hHa⟩ := exists_isClosed_represents (n := n) ha
  let sx := pointOfClosedPoint q x hx
  let sH := pointOfClosedPoint g H hH
  let s : Spec (CommRingCat.of k) ⟶ incidenceAmbient q n :=
    pullback.lift sx sH (by rw [pointOfClosedPoint_comp, pointOfClosedPoint_comp])
  refine ⟨s (bertiniPt k), bertiniAmbient_isClosed_of_section (pullback.fst q g ≫ q) s
    (by rw [pullback.lift_fst_assoc, pointOfClosedPoint_comp]) _, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.lift_fst, pointOfClosedPoint_apply]
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd, pointOfClosedPoint_apply]
    exact hHa

/-! ### Values of the chart functions -/

private theorem bertini_isUnit_mk_iff (P : Ideal (MvPolynomial (Fin (n + 1)) k)) [P.IsPrime]
    (p q : MvPolynomial (Fin (n + 1)) k) (hq : q ∈ P.primeCompl) :
    IsUnit (Localization.mk p ⟨q, hq⟩ : Localization.AtPrime P) ↔ p ∉ P := by
  rw [Localization.mk_eq_mk']
  exact IsLocalization.AtPrime.isUnit_mk'_iff _ _ _ _

private theorem bertiniGerm_frac_mem_iff (β : Fin (n + 1)) (H : Proj 𝒮)
    (hH : H ∈ Proj.basicOpen 𝒮 (X β)) (p : MvPolynomial (Fin (n + 1)) k) (hp : p ∈ 𝒮 1) :
    (Proj 𝒮).presheaf.germ _ H hH (Proj.awayToSection 𝒮 (X β) (bertiniFrac β p hp)) ∈
        IsLocalRing.maximalIdeal ((Proj 𝒮).presheaf.stalk H) ↔
      p ∈ H.asHomogeneousIdeal.toIdeal := by
  have e : (Proj 𝒮).presheaf.germ _ H hH (Proj.awayToSection 𝒮 (X β) (bertiniFrac β p hp)) =
      (Proj.stalkIso' 𝒮 H).symm
        (HomogeneousLocalization.mapId 𝒮 (Submonoid.powers_le.mpr hH) (bertiniFrac β p hp)) :=
    congr($(ProjectiveSpectrum.Proj.awayToSection_germ 𝒮 (X β) H hH) (bertiniFrac β p hp))
  rw [e]
  refine (IsLocalRing.mem_maximalIdeal _).trans <| mem_nonunits_iff.trans <|
    (not_congr ?_).trans not_not
  refine (MulEquiv.isUnit_map (Proj.stalkIso' 𝒮 H).symm.toMulEquiv).trans ?_
  have : H.asHomogeneousIdeal.toIdeal.IsPrime := ProjectiveSpectrum.isPrime (𝒜 := 𝒮) H
  refine (HomogeneousLocalization.isUnit_iff_isUnit_val 𝒮 _ _).symm.trans ?_
  exact bertini_isUnit_mk_iff _ p (X β) hH

private theorem bertiniStructure_appLE (β : Fin (n + 1)) (c : k) :
    (Proj.toSpecZero 𝒮 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒮 0)))).appLE ⊤
        (Proj.basicOpen 𝒮 (X β)) (show _ ≤ _ ⁻¹ᵁ ⊤ from le_top)
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) =
      Proj.awayToSection 𝒮 (X β) (chartConst k β c) := by
  have h1 := ι_comp_eq_toSpecΓ_SpecMap_of_Spec
    (Proj.toSpecZero 𝒮 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒮 0))))
    (Proj.basicOpen 𝒮 (X β)) (show _ ≤ _ ⁻¹ᵁ ⊤ from le_top)
  have h2 : (Proj.basicOpen 𝒮 (X β)).ι ≫ Proj.toSpecZero 𝒮 ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (𝒮 0))) =
      (Proj.basicOpen 𝒮 (X β)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (chartConst k β) ≫ Proj.awayToSection 𝒮 (X β)) := by
    rw [← Iso.hom_inv_id_assoc
      (Proj.basicOpenIsoSpec 𝒮 (X β) (X_mem_homogeneousSubmodule_one k β) Nat.one_pos)
      (Proj.basicOpen 𝒮 (X β)).ι, Proj.basicOpenIsoSpec_inv_ι, Category.assoc,
      Proj.awayι_toSpecZero_assoc, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec,
      Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [h1] at h2
  have h3 := congrArg Scheme.Hom.appTop h2
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc, cancel_epi, cancel_mono] at h3
  have h4 := congr($h3 c)
  simp only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom] at h4
  exact h4

private theorem bertiniGerm_dualConst (β : Fin (n + 1)) (H : Proj 𝒮)
    (hH : H ∈ Proj.basicOpen 𝒮 (X β)) (c : k) :
    (Proj 𝒮).presheaf.germ ⊤ H trivial
        ((Proj.toSpecZero 𝒮 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒮 0)))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      (Proj 𝒮).presheaf.germ _ H hH (Proj.awayToSection 𝒮 (X β) (chartConst k β c)) := by
  rw [← bertiniStructure_appLE β c]
  exact (TopCat.Presheaf.germ_res_apply _ (homOfLE le_top) H hH _).symm

/-- At a point `H` representing `a` with `a β ≠ 0`, the chart function `x_j / x_β` takes
the value `a j / a β`: their difference lies in the maximal ideal of the stalk at `H`. -/
theorem germ_dualChartRatio_sub_dualConst_mem_maximalIdeal {a : Fin (n + 1) → k}
    {H : projectiveSpaceScheme k n} (hH : Represents a H) {β : Fin (n + 1)} (haβ : a β ≠ 0)
    (hHβ : H ∈ Proj.basicOpen 𝒮 (X β)) (j : Fin (n + 1)) :
    (projectiveSpaceScheme k n).presheaf.germ _ H hHβ (dualChartRatio k n β j) -
        (projectiveSpaceScheme k n).presheaf.germ ⊤ H trivial (dualConst k n (a j / a β)) ∈
      IsLocalRing.maximalIdeal ((projectiveSpaceScheme k n).presheaf.stalk H) := by
  have hp : X j - C (a j / a β) * X β ∈ 𝒮 1 :=
    sub_mem (X_mem_homogeneousSubmodule_one k j) (bertini_C_mul_X_mem _ β)
  have hmem : X j - C (a j / a β) * X β ∈ bertiniPtIdeal H := by
    have h := Ideal.mul_mem_left (bertiniPtIdeal H) (C (a β)⁻¹) (hH β j)
    have e : C (a β)⁻¹ * (C (a β) * X j - C (a j) * X β) = X j - C (a j / a β) * X β := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, inv_mul_cancel₀ haβ, C_1, one_mul,
        div_eq_inv_mul]
    rwa [e] at h
  have key := (bertiniGerm_frac_mem_iff β H hHβ _ hp).2 hmem
  rw [bertiniFrac_eq', map_sub, map_sub, ← bertiniGerm_dualConst β H hHβ] at key
  exact key

end Points


end BertiniIncidence

end Hartshorne
