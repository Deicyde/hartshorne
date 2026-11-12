/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.LocalIntersectionMultiplicity
import Hartshorne.Scheme.RegularLocalInitialForm
import Hartshorne.Scheme.DimensionAtClosedPoint

/-!
# Multiplicity of a curve at a point

Hartshorne, *Algebraic Geometry*, V.3, before Proposition 3.6 (p. 389).

For a curve (effective divisor) `D` on a surface and a point `P` with local equation
`f ∈ 𝒪_{X,P}`, the multiplicity of `D` at `P` is `μ_P(D) = max {r | f ∈ 𝔪_P^r}`
(`Hartshorne.Surface.pointMultiplicity`).

* `pointMultiplicity_eq`, `pointMultiplicity_eq_iff`: `μ_P(D)` does not depend on the local
  equation; it is the `r` with `f ∈ 𝔪_P^r` and `f ∉ 𝔪_P^{r+1}`.
* `pointMultiplicity_add`: `μ_P(D + E) = μ_P(D) + μ_P(E)`.
* `pointMultiplicity_eq_iff_exists_initialForm`: at a closed point `P` with regular parameters
  `x, y` (generators of `𝔪_P`), `μ_P(D) = r` exactly when `f = F(x, y) + h` with `F` a nonzero
  form of degree `r` over `k` and `h ∈ 𝔪_P^{r+1}`; `F` is the initial homogeneous part of `f`.

The definition makes sense at every point; additivity holds at every point, since every local
ring of the surface is regular with residue field containing the infinite field `k`. Additivity
and the initial-form statement rest on `Hartshorne.RegularLocal.eval_notMem_pow_succ`: the classes
of a regular system of parameters in `gr_𝔪(𝒪_{X,P})` are algebraically independent (the
residue field being infinite).
-/

universe u

open AlgebraicGeometry IsLocalRing MvPolynomial

namespace Hartshorne

namespace Surface

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Surface k)

/-- The **multiplicity** `μ_P(D) = max {r | f ∈ 𝔪_P^r}` of a curve `D` at a point `P`, for a
local equation `f` of `D` at `P`. -/
def pointMultiplicity (D : S.Curve) (P : S.X) : ℕ :=
  sSup {r : ℕ | (exists_isLocalEquation D P).choose ∈ maximalIdeal (S.X.presheaf.stalk P) ^ r}

variable {S}

/-- In a Noetherian local ring a nonzero element has a largest power of `𝔪` containing it. -/
private theorem exists_mem_pow_notMem_pow_succ {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {f : A} (hf : f ≠ 0) :
    ∃ r, f ∈ maximalIdeal A ^ r ∧ f ∉ maximalIdeal A ^ (r + 1) := by
  classical
  have hex : ∃ n, f ∉ maximalIdeal A ^ n := by
    by_contra! h
    apply hf
    rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A)
      (maximalIdeal.isMaximal A).ne_top, Submodule.mem_iInf]
    exact h
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_zero, Ideal.one_eq_top] at this
    exact this Submodule.mem_top
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · by_contra h
    exact Nat.find_min hex (by omega) h
  · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h0)]
    exact Nat.find_spec hex

/-- If `f ∈ I^r` and `f ∉ I^{r+1}`, then `r = max {n | f ∈ I^n}`. -/
private theorem sSup_eq_of_mem_pow_of_notMem_pow_succ {A : Type*} [CommRing A] {I : Ideal A}
    {f : A} {r : ℕ} (h1 : f ∈ I ^ r) (h2 : f ∉ I ^ (r + 1)) :
    sSup {n : ℕ | f ∈ I ^ n} = r := by
  refine IsGreatest.csSup_eq ⟨h1, fun n hn ↦ ?_⟩
  by_contra hlt
  exact h2 (Ideal.pow_le_pow_right (by omega) hn)

/-- **Independence of the local equation.** For any local equation `f` of `D` at `P`,
`μ_P(D) = max {r | f ∈ 𝔪_P^r}`. -/
theorem pointMultiplicity_eq {D : S.Curve} {P : S.X} {f : S.X.presheaf.stalk P}
    (hf : S.IsLocalEquation D.1 P f) :
    S.pointMultiplicity D P = sSup {r : ℕ | f ∈ maximalIdeal (S.X.presheaf.stalk P) ^ r} := by
  obtain ⟨u, hu⟩ := (exists_isLocalEquation D P).choose_spec.associated hf
  rw [pointMultiplicity, ← hu]
  simp only [Ideal.mul_unit_mem_iff_mem _ u.isUnit]

/-- **The multiplicity is the maximum.** For a local equation `f` of `D` at `P`, `μ_P(D) = r`
exactly when `f ∈ 𝔪_P^r` and `f ∉ 𝔪_P^{r+1}`. -/
theorem pointMultiplicity_eq_iff {D : S.Curve} {P : S.X} {f : S.X.presheaf.stalk P}
    (hf : S.IsLocalEquation D.1 P f) (r : ℕ) :
    S.pointMultiplicity D P = r ↔ f ∈ maximalIdeal (S.X.presheaf.stalk P) ^ r ∧
      f ∉ maximalIdeal (S.X.presheaf.stalk P) ^ (r + 1) := by
  have : IsRegularLocalRing (S.X.presheaf.stalk P) := S.isRegular.2 P
  obtain ⟨n, hn1, hn2⟩ := exists_mem_pow_notMem_pow_succ hf.1
  rw [pointMultiplicity_eq hf, sSup_eq_of_mem_pow_of_notMem_pow_succ hn1 hn2]
  refine ⟨fun h ↦ h ▸ ⟨hn1, hn2⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  rw [← sSup_eq_of_mem_pow_of_notMem_pow_succ hn1 hn2, sSup_eq_of_mem_pow_of_notMem_pow_succ h1 h2]

/-- A product of local equations of `D` and `E` at `P` is a local equation of `D + E`. -/
theorem IsLocalEquation.mul {D E : S.X.WeilDivisor} {P : S.X} {f g : S.X.presheaf.stalk P}
    (hf : S.IsLocalEquation D P f) (hg : S.IsLocalEquation E P g) :
    S.IsLocalEquation (D + E) P (f * g) := by
  obtain ⟨hf0, U, hPU, hU⟩ := hf
  obtain ⟨hg0, V, hPV, hV⟩ := hg
  have hinj : Function.Injective (algebraMap (S.X.presheaf.stalk P) S.X.functionField) :=
    IsFractionRing.injective _ _
  refine ⟨mul_ne_zero hf0 hg0, U ⊓ V, ⟨hPU, hPV⟩, fun y hy hy1 ↦ ?_⟩
  rw [map_mul, Scheme.ord_mul ((map_ne_zero_iff _ hinj).2 hf0) ((map_ne_zero_iff _ hinj).2 hg0),
    hU y hy.1 hy1, hV y hy.2 hy1]
  rfl

/-- The residue field of a local ring of the surface contains `k`, so it is infinite. -/
private theorem infinite_residueField (P : S.X) :
    Infinite (ResidueField (S.X.presheaf.stalk P)) :=
  Infinite.of_injective _ ((residue _).comp (S.stalkStructureMap P)).injective

variable (S) in
/-- **Additivity.** For curves `D, E` and a point `P`, `μ_P(D + E) = μ_P(D) + μ_P(E)`. -/
theorem pointMultiplicity_add (D E : S.Curve) (P : S.X) :
    S.pointMultiplicity ⟨D.1 + E.1, fun x ↦ add_nonneg (D.2 x) (E.2 x)⟩ P =
      S.pointMultiplicity D P + S.pointMultiplicity E P := by
  have : IsRegularLocalRing (S.X.presheaf.stalk P) := S.isRegular.2 P
  have := infinite_residueField (S := S) P
  obtain ⟨f, hf⟩ := exists_isLocalEquation D P
  obtain ⟨g, hg⟩ := exists_isLocalEquation E P
  obtain ⟨hf1, hf2⟩ := (pointMultiplicity_eq_iff hf _).mp rfl
  obtain ⟨hg1, hg2⟩ := (pointMultiplicity_eq_iff hg _).mp rfl
  refine (pointMultiplicity_eq_iff (D := ⟨D.1 + E.1, _⟩) (hf.mul hg) _).mpr ⟨?_, ?_⟩
  · rw [pow_add]
    exact Ideal.mul_mem_mul hf1 hg1
  · exact RegularLocal.mul_notMem_pow_add_succ hf1 hf2 hg1 hg2

/-- **The initial form.** Let `P` be a closed point and let `x, y` be regular parameters at `P`
(generators of `𝔪_P`). For a local equation `f` of `D` at `P`, `μ_P(D) = r` exactly when
`f - F(x, y) ∈ 𝔪_P^{r+1}` for a nonzero homogeneous polynomial `F ∈ k[X, Y]` of degree `r`:
`μ_P(D)` is the degree of the initial homogeneous part `F` of `f` in `x, y`. -/
theorem pointMultiplicity_eq_iff_exists_initialForm {D : S.Curve} {P : S.X}
    (hP : IsClosed ({P} : Set S.X)) {f : S.X.presheaf.stalk P} (hf : S.IsLocalEquation D.1 P f)
    {x y : S.X.presheaf.stalk P} (hxy : Ideal.span {x, y} = maximalIdeal (S.X.presheaf.stalk P))
    (r : ℕ) :
    S.pointMultiplicity D P = r ↔ ∃ F : MvPolynomial (Fin 2) k, F.IsHomogeneous r ∧ F ≠ 0 ∧
      f - F.eval₂ (S.stalkStructureMap P) ![x, y] ∈
        maximalIdeal (S.X.presheaf.stalk P) ^ (r + 1) := by
  set φ := S.stalkStructureMap P
  have : IsRegularLocalRing (S.X.presheaf.stalk P) := S.isRegular.2 P
  have := infinite_residueField (S := S) P
  have hv : Ideal.span (Set.range ![x, y]) = maximalIdeal (S.X.presheaf.stalk P) := by
    rw [← hxy]
    congr 1
    ext z
    simp [eq_comm, or_comm]
  have hdim : ringKrullDim (S.X.presheaf.stalk P) = Fintype.card (Fin 2) := by
    rw [← dimension_at_closed_point S.hom S.finiteType P hP, S.dim_eq, Fintype.card_fin]
    rfl
  have hρ : Function.Bijective ((residue (S.X.presheaf.stalk P)).comp φ) :=
    ⟨((residue (S.X.presheaf.stalk P)).comp φ).injective,
      surjective_residue_comp_stalkStructureMap hP⟩
  have heval : ∀ F : MvPolynomial (Fin 2) k, F.eval₂ φ ![x, y] = (F.map φ).eval ![x, y] := by
    intro F
    rw [eval_map]
  rw [pointMultiplicity_eq_iff hf]
  constructor
  · rintro ⟨h1, h2⟩
    rw [← hv, Ideal.mem_span_pow_iff_exists_isHomogeneous] at h1
    obtain ⟨G, hG, hGf⟩ := h1
    let e := RingEquiv.ofBijective _ hρ
    set ψ : S.X.presheaf.stalk P →+* k := e.symm.toRingHom.comp (residue _)
    have hcomp :
        ((residue (S.X.presheaf.stalk P)).comp φ).comp ψ = residue (S.X.presheaf.stalk P) :=
      RingHom.ext fun z ↦ e.apply_symm_apply (residue (S.X.presheaf.stalk P) z)
    have hmapF : ((G.map ψ).map φ).map (residue (S.X.presheaf.stalk P)) =
        G.map (residue (S.X.presheaf.stalk P)) := by
      rw [map_map, map_map]
      exact congrArg (map · G) hcomp
    refine ⟨G.map ψ, hG.map _, fun h0 ↦ h2 ?_, ?_⟩
    · rw [← hGf]
      refine RegularLocal.eval_mem_pow_succ_of_map_eq_zero hv hG ?_
      rw [← hmapF, h0, map_zero, map_zero]
    · rw [heval, ← hGf, ← map_sub]
      refine RegularLocal.eval_mem_pow_succ_of_map_eq_zero hv (hG.sub ((hG.map ψ).map φ)) ?_
      rw [map_sub, hmapF, sub_self]
  · rintro ⟨F, hF, hF0, hfF⟩
    have hFA : (F.map φ).IsHomogeneous r := hF.map φ
    have hFA0 : (F.map φ).map (residue (S.X.presheaf.stalk P)) ≠ 0 := by
      rw [map_map]
      exact fun h ↦ hF0 (map_injective _ hρ.1 (h.trans (map_zero _).symm))
    have hmem : F.eval₂ φ ![x, y] ∈ maximalIdeal (S.X.presheaf.stalk P) ^ r := by
      rw [← hv, Ideal.mem_span_pow_iff_exists_isHomogeneous]
      exact ⟨F.map φ, hFA, (heval F).symm⟩
    have hnot := RegularLocal.eval_notMem_pow_succ hv hdim hFA hFA0
    rw [← heval] at hnot
    refine ⟨?_, fun h ↦ hnot ?_⟩
    · have := add_mem (Ideal.pow_le_pow_right (Nat.le_succ r) hfF) hmem
      rwa [sub_add_cancel] at this
    · have := sub_mem h hfF
      rwa [sub_sub_cancel] at this

end

end Surface

end Hartshorne
