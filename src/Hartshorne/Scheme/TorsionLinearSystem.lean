/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LinearSystem
import Hartshorne.Scheme.LocallyFactorialClassPicard
import Hartshorne.Scheme.ProjectiveSpaceProper

/-!
# Linear systems of torsion divisors

Hartshorne, *Algebraic Geometry*, II, Exercise 7.6(b) (p. 170).

Let `X` be an integral scheme, projective over an algebraically closed field `k`, and let `D` be a
divisor whose class in `Pic X` has finite order `r`. Then the complete linear system `|nD|` has
dimension `0` when `r ∣ n` and `-1` otherwise, so `n ↦ dim |nD|` is periodic of period `r`.

## Main results

* `Hartshorne.LinearSystem.dim_complete_of_orderOf_eq`: the invertible-sheaf form. If the class
  of `L` in `Pic X` has order `r`, then every invertible `M` whose class is the `n`-th power of
  that of `L` has `dim |M| = 0` for `r ∣ n` and `dim |M| = -1` otherwise.
* `Hartshorne.LinearSystem.dim_complete_nsmul_of_addOrderOf_eq`: the Cartier-divisor form, with
  `|nD|` the complete linear system of `𝒪_X(nD)`, and its periodicity
  `Hartshorne.LinearSystem.periodic_dim_complete_nsmul`.
* `Hartshorne.LinearSystem.dim_complete_weil_nsmul_of_addOrderOf_eq`: Hartshorne's form, for a
  Weil divisor `D` on a regular (nonsingular) integral projective scheme over `k`, with `|nD|` the
  complete linear system of `𝒪_X(nD)` and the class of `D` taken in `Pic X` through
  `Cl X ≅ Pic X`; and its periodicity `Hartshorne.LinearSystem.periodic_dim_complete_weil_nsmul`.

## Proof

Write `L ≅ 𝒪_X(D₀)`. A nonzero global section `s` has an effective divisor of zeros `E ~ D₀`
(Proposition 7.7). If `mD₀ ~ 0` with `m > 0`, then `mE` is effective and linearly equivalent to
`0`. An effective divisor `div h` is `0`: the effectivity makes `h` a global regular function,
hence a nonzero constant since `Γ(X, 𝒪_X) = k`, hence a unit. So `mE = 0`, and then `E` and
`-E = (m - 1)E` are both effective, which forces `E = 0`: the local equations of `E` are regular
with regular inverses. Hence `D₀ ~ E = 0`. Applied to `D₀ = nD`, a nonzero section of `𝒪_X(nD)`
exists only when `nD ~ 0`, that is `r ∣ n`; and when `nD ~ 0`, every nonzero section has divisor
`0`, so any two differ by a scalar (Proposition 7.7(c)) and `Γ(X, 𝒪_X(nD))` is a line.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Hartshorne.Ringed
open AlgebraicGeometry.Scheme.CartierDivisor

namespace AlgebraicGeometry.Scheme.CartierDivisor

variable {X : Scheme.{u}}

/-- A local equation that is a unit regular function defines the zero divisor. -/
private theorem toCartierDivisorSheaf_eq_zero_of_isUnit {V : X.Opens}
    (f : X.totalQuotientUnitsSheaf.obj.obj (op V)) {a : Γ(X, V)} (ha : IsUnit a)
    (haf : X.toK V a = kUnitVal f) :
    X.toCartierDivisorSheaf.hom.app (op V) (Additive.ofMul f) = 0 := by
  have h1 : X.toCartierDivisorSheaf.hom.app (op V)
      (Additive.ofMul (1 : X.totalQuotientUnitsSheaf.obj.obj (op V))) = 0 := map_zero _
  rw [← h1, toCartierDivisorSheaf_apply_eq_iff_ratio, div_one]
  exact ⟨(show Γ(X, V)ˣ from ha.unit), Units.ext haf⟩

/-- An effective divisor `E` has the section `1` of `𝒪_X(E)`. -/
private theorem isSection_one_of_isEffective {E : X.CartierDivisor} (hE : E.IsEffective) :
    E.IsSection (1 : X.totalQuotientSheaf.obj.obj (op ⊤)) := by
  have h0 : X.principalCartierDivisor 1 = 0 := map_zero X.principalCartierDivisorHom
  exact isSection_of_isEffective_add_principal E 1 (by rwa [h0, add_zero])

/-- A divisor `E` for which `1` is a section of `𝒪_X(E)` is effective. -/
private theorem isEffective_of_isSection_one {E : X.CartierDivisor}
    (h : E.IsSection (1 : X.totalQuotientSheaf.obj.obj (op ⊤))) : E.IsEffective := by
  intro x
  obtain ⟨V, f, hx, hf⟩ := E.exists_localEquation x
  obtain ⟨r, hr⟩ := h V le_top f hf
  refine ⟨V, f, hx, hf, r, ?_⟩
  rw [hr, map_one, one_mul]

private theorem isEffective_zero' : (0 : X.CartierDivisor).IsEffective := by
  intro x
  refine ⟨⊤, 1, trivial, ?_, 1, ?_⟩
  · rw [show (0 : X.CartierDivisor).restrict ⊤ = 0 from map_zero _]
    exact (map_zero _).symm
  · rw [map_one]
    rfl

private theorem isEffective_add' {E E' : X.CartierDivisor} (hE : E.IsEffective)
    (hE' : E'.IsEffective) : (E + E').IsEffective := by
  have h := isSection_mul (isSection_one_of_isEffective hE) (isSection_one_of_isEffective hE')
  rw [mul_one] at h
  exact isEffective_of_isSection_one h

private theorem isEffective_nsmul' {E : X.CartierDivisor} (hE : E.IsEffective) (m : ℕ) :
    (m • E).IsEffective := by
  induction m with
  | zero => rw [zero_smul]; exact isEffective_zero'
  | succ m ih => rw [succ_nsmul]; exact isEffective_add' ih hE

/-- A divisor `E` with `E` and `-E` both effective is zero. -/
private theorem eq_zero_of_isEffective_of_isEffective_neg {E : X.CartierDivisor}
    (hE : E.IsEffective) (hE' : (-E).IsEffective) : E = 0 := by
  have h1 := isSection_one_of_isEffective hE
  have h2 := isSection_one_of_isEffective hE'
  have hloc : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ E.restrict U = (0 : X.CartierDivisor).restrict U := by
    intro x
    obtain ⟨V, f, hx, hf⟩ := E.exists_localEquation x
    obtain ⟨a, ha⟩ := h1 V le_top f hf
    obtain ⟨b, hb⟩ := h2 V le_top f⁻¹ (restrict_neg_eq hf)
    rw [map_one, one_mul] at ha hb
    have hab : a * b = 1 := X.toK_injective V (by
      rw [map_mul, ha, hb, map_one]
      exact Units.mul_inv _)
    refine ⟨V, hx, ?_⟩
    rw [hf, show (0 : X.CartierDivisor).restrict V = 0 from map_zero _]
    exact toCartierDivisorSheaf_eq_zero_of_isUnit f (IsUnit.of_mul_eq_one b hab) ha
  choose W hxW hW using hloc
  exact X.cartierDivisorSheaf.eq_of_locally_eq' W ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩) E 0 hW

private theorem linearEquivalent_trans' {D E F : X.CartierDivisor} (h₁ : D.LinearEquivalent E)
    (h₂ : E.LinearEquivalent F) : D.LinearEquivalent F := by
  have h := add_mem h₁ h₂
  rwa [sub_add_sub_cancel] at h

private theorem linearEquivalent_symm' {D E : X.CartierDivisor} (h : D.LinearEquivalent E) :
    E.LinearEquivalent D := by
  have h' := neg_mem h
  rwa [neg_sub] at h'

private theorem linearEquivalent_nsmul' {D E : X.CartierDivisor} (h : D.LinearEquivalent E)
    (m : ℕ) : (m • D).LinearEquivalent (m • E) := by
  have h' := nsmul_mem h m
  rwa [smul_sub] at h'

variable {k : Type u} [Field k]

/-- On an integral scheme universally closed over an algebraically closed field `k`, an effective
divisor linearly equivalent to `0` is `0`. -/
private theorem eq_zero_of_isEffective_of_linearEquivalent_zero [IsAlgClosed k] [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [UniversallyClosed p] {E : X.CartierDivisor} (hE : E.IsEffective)
    (hlin : E.LinearEquivalent 0) : E = 0 := by
  obtain ⟨h', hh'⟩ := hlin
  set h : X.totalQuotientUnitsSheaf.obj.obj (op ⊤) := h'.toMul
  have hEq : E = X.principalCartierDivisor h := by
    rw [← sub_zero E]
    exact hh'.symm
  have hsec := isSection_of_isEffective_add_principal 0 h (by rwa [zero_add, ← hEq])
  obtain ⟨a, ha⟩ := exists_toK_eq_of_isSection_zero hsec
  obtain ⟨c, hc⟩ := (Scheme.globalScalar_bijective p).2 a
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := nontrivial_totalQuotient_top (X := X)
    rw [map_zero] at hc
    rw [← hc, map_zero] at ha
    exact (Units.ne_zero (show (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ from h)) ha.symm
  have ha' : IsUnit a := hc ▸ (isUnit_iff_ne_zero.2 hc0).map _
  rw [hEq]
  exact toCartierDivisorSheaf_eq_zero_of_isUnit h ha' ha

/-- On an integral scheme universally closed over an algebraically closed field `k`, an effective
divisor linearly equivalent to a divisor `D₀` of finite order in the class group is `0`. -/
private theorem eq_zero_of_isEffective_of_linearEquivalent_torsion [IsAlgClosed k] [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [UniversallyClosed p] {E D₀ : X.CartierDivisor} (hE : E.IsEffective)
    (hlin : E.LinearEquivalent D₀) {m : ℕ} (hm : 0 < m) (hD₀ : (m • D₀).LinearEquivalent 0) :
    E = 0 := by
  have hmE : m • E = 0 := eq_zero_of_isEffective_of_linearEquivalent_zero p
    (isEffective_nsmul' hE m) (linearEquivalent_trans' (linearEquivalent_nsmul' hlin m) hD₀)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [zero_add, succ_nsmul] at hmE
  refine eq_zero_of_isEffective_of_isEffective_neg hE ?_
  rw [← eq_neg_of_add_eq_zero_left hmE]
  exact isEffective_nsmul' hE m'

end AlgebraicGeometry.Scheme.CartierDivisor

namespace Hartshorne.LinearSystem

open AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- For `nD ~ 0`, the space of sections of `L ≅ 𝒪_X(D₀)`, `D₀ ~ 0`, is a line. -/
private theorem finrank_eq_one_of_linearEquivalent_zero [IsAlgClosed k] [IsIntegral X]
    {q : X ⟶ Spec (.of k)} [UniversallyClosed q] {M : X.Modules} (hM : M.IsInvertible)
    {D₀ : X.CartierDivisor} (φ : M ≅ D₀.sheaf) (hD₀ : D₀.LinearEquivalent 0) :
    Module.finrank k (globalSectionsOverField q M) = 1 := by
  obtain ⟨s₀', hs₀', hs₀D'⟩ := exists_section_isDivisorOfZeros φ isEffective_zero'
    (linearEquivalent_symm' hD₀)
  let s₀ : globalSectionsOverField q M := s₀'
  have hs₀ : s₀ ≠ 0 := hs₀'
  have hs₀D : IsDivisorOfZeros M (toSection s₀) 0 := hs₀D'
  have key : ∀ s : globalSectionsOverField q M, s ≠ 0 → IsDivisorOfZeros M (toSection s) 0 := by
    intro s hs
    obtain ⟨E, hE, hEeff, hElin⟩ := exists_isDivisorOfZeros φ hs
    rwa [eq_zero_of_isEffective_of_linearEquivalent_zero q hEeff
      (linearEquivalent_trans' hElin hD₀)] at hE
  refine (finrank_eq_one_iff_of_nonzero' (K := k) (V := globalSectionsOverField q M) s₀ hs₀).2
    fun w => ?_
  by_cases hw : w = 0
  · exact ⟨0, by rw [hw, zero_smul]⟩
  · obtain ⟨c, hc⟩ := (divisor_eq_iff hM hs₀ hw hs₀D (key w hw)).1 rfl
    exact ⟨c, hc.symm⟩

/-- If `D₀` is torsion in the class group but not linearly equivalent to `0`, then
`L ≅ 𝒪_X(D₀)` has no nonzero global section. -/
private theorem finrank_eq_zero_of_torsion [IsAlgClosed k] [IsIntegral X]
    {q : X ⟶ Spec (.of k)} [UniversallyClosed q] {M : X.Modules}
    {D₀ : X.CartierDivisor} (φ : M ≅ D₀.sheaf) {m : ℕ} (hm : 0 < m)
    (hmD₀ : (m • D₀).LinearEquivalent 0) (hD₀ : ¬ D₀.LinearEquivalent 0) :
    Module.finrank k (globalSectionsOverField q M) = 0 := by
  have : Subsingleton (globalSectionsOverField q M) := by
    refine ⟨fun s t => ?_⟩
    suffices h : ∀ s : globalSectionsOverField q M, s = 0 by rw [h s, h t]
    intro s
    by_contra hs
    obtain ⟨E, -, hEeff, hElin⟩ := exists_isDivisorOfZeros φ hs
    have hE0 := eq_zero_of_isEffective_of_linearEquivalent_torsion q hEeff hElin hm hmD₀
    rw [hE0] at hElin
    exact hD₀ (linearEquivalent_symm' hElin)
  exact Module.finrank_zero_of_subsingleton

/-- `m D ~ 0` exactly when the class of `D` in `Pic X` is killed by `m`. -/
private theorem nsmul_linearEquivalent_zero_iff (D : X.CartierDivisor) (m : ℕ) :
    (m • D).LinearEquivalent 0 ↔ m • X.cartierDivisorToPicard D = 0 := by
  rw [← map_nsmul, linearEquivalent_iff_nonempty_iso, ← map_zero X.cartierDivisorToPicard]
  constructor
  · rintro ⟨e⟩
    exact congrArg Additive.ofMul ((Pic.mk_eq_mk_iff _ _).2 ⟨e⟩)
  · intro h
    exact (Pic.mk_eq_mk_iff _ _).1 (Additive.ofMul.injective h)

/-- The core computation: for `M ≅ 𝒪_X(nD)` with the class of `D` in `Pic X` of order `r`. -/
private theorem dim_complete_of_iso_nsmul [IsAlgClosed k] [IsIntegral X]
    {q : X ⟶ Spec (.of k)} (hq : Projective q) (D : X.CartierDivisor) {r : ℕ} (hr0 : 0 < r)
    (hr : addOrderOf (X.cartierDivisorToPicard D) = r) (n : ℕ) {M : X.Modules}
    (hM : M.IsInvertible) (φ : M ≅ (n • D).sheaf) :
    (complete hq hM).dim = if r ∣ n then 0 else -1 := by
  have : IsProper q := Projective.isProper hq
  have hiff : ∀ m : ℕ, (m • D).LinearEquivalent 0 ↔ r ∣ m := fun m => by
    rw [nsmul_linearEquivalent_zero_iff, ← hr, addOrderOf_dvd_iff_nsmul_eq_zero]
  rw [dim_complete]
  split_ifs with hn
  · rw [finrank_eq_one_of_linearEquivalent_zero hM φ ((hiff n).2 hn)]
    norm_num
  · have hrn : (r • (n • D)).LinearEquivalent 0 := by
      rw [smul_smul, hiff]
      exact dvd_mul_right r n
    rw [finrank_eq_zero_of_torsion φ hr0 hrn (fun h => hn ((hiff n).1 h))]
    norm_num

/-- **Torsion linear systems** (Hartshorne II, Exercise 7.6(b)), invertible-sheaf form. Let `X`
be an integral scheme projective over an algebraically closed field `k` (more general than
Hartshorne's nonsingular projective variety), and let the class of the invertible sheaf `L` in
`Pic X` have finite order `r`. If `M` is an invertible sheaf whose class is the `n`-th power of
that of `L` (so `|M|` is the linear system `|nD|` for `L ≅ 𝒪_X(D)`), then `dim |M| = 0` when
`r ∣ n` and `dim |M| = -1` otherwise. -/
theorem dim_complete_of_orderOf_eq [IsAlgClosed k] [IsIntegral X] {q : X ⟶ Spec (.of k)}
    (hq : Projective q) {L : X.Modules} (hL : L.IsInvertible) {r : ℕ} (hr0 : 0 < r)
    (hr : orderOf (Pic.mk (R := X.sheaf) L ((Modules.isInvertible_iff_ringed L).1 hL)) = r)
    (n : ℕ) {M : X.Modules} (hM : M.IsInvertible)
    (hMn : Pic.mk (R := X.sheaf) M ((Modules.isInvertible_iff_ringed M).1 hM) =
      Pic.mk (R := X.sheaf) L ((Modules.isInvertible_iff_ringed L).1 hL) ^ n) :
    (complete hq hM).dim = if r ∣ n then 0 else -1 := by
  obtain ⟨D, ⟨χ⟩⟩ := exists_cartierDivisor_sheaf_iso hL
  have hD : X.cartierDivisorToPicard D =
      Additive.ofMul (Pic.mk (R := X.sheaf) L ((Modules.isInvertible_iff_ringed L).1 hL)) :=
    congrArg Additive.ofMul ((Pic.mk_eq_mk_iff _ _).2 ⟨χ⟩)
  have hnD : X.cartierDivisorToPicard (n • D) =
      Additive.ofMul (Pic.mk (R := X.sheaf) M ((Modules.isInvertible_iff_ringed M).1 hM)) := by
    rw [map_nsmul, hD, hMn, ofMul_pow]
  obtain ⟨φ⟩ := (Pic.mk_eq_mk_iff _ _).1 (Additive.ofMul.injective hnD)
  refine dim_complete_of_iso_nsmul hq D hr0 ?_ n hM φ.symm
  rw [hD, addOrderOf_ofMul_eq_orderOf, hr]

/-- **Torsion linear systems** (Hartshorne II, Exercise 7.6(b)), Cartier-divisor form. Let `X` be
an integral scheme projective over an algebraically closed field `k` (more general than
Hartshorne's nonsingular projective variety), and let `D` be a Cartier divisor whose class in
`Pic X` has finite order `r`.
Then the complete linear system `|nD|` of `𝒪_X(nD)` has dimension `0` when `r ∣ n` and `-1`
otherwise. -/
theorem dim_complete_nsmul_of_addOrderOf_eq [IsAlgClosed k] [IsIntegral X]
    {q : X ⟶ Spec (.of k)} (hq : Projective q) (D : X.CartierDivisor) {r : ℕ} (hr0 : 0 < r)
    (hr : addOrderOf (X.cartierDivisorToPicard D) = r) (n : ℕ) :
    (complete hq (n • D).isInvertible_sheaf).dim = if r ∣ n then 0 else -1 :=
  dim_complete_of_iso_nsmul hq D hr0 hr n _ (Iso.refl _)

/-- **Torsion linear systems are periodic** (Hartshorne II, Exercise 7.6(b)), Cartier-divisor
form: `n ↦ dim |nD|` is periodic of period `r`. -/
theorem periodic_dim_complete_nsmul [IsAlgClosed k] [IsIntegral X]
    {q : X ⟶ Spec (.of k)} (hq : Projective q) (D : X.CartierDivisor) {r : ℕ} (hr0 : 0 < r)
    (hr : addOrderOf (X.cartierDivisorToPicard D) = r) :
    Function.Periodic (fun n : ℕ => (complete hq (n • D).isInvertible_sheaf).dim) r := by
  intro n
  simp only [dim_complete_nsmul_of_addOrderOf_eq hq D hr0 hr, Nat.dvd_add_self_right]

/-- **Torsion linear systems** (Hartshorne II, Exercise 7.6(b)). Let `X` be a regular integral
scheme projective over an algebraically closed field `k` (a nonsingular projective variety), and
let `D` be a Weil divisor whose class in `Pic X ≅ Cl X` has finite order `r`. Then the complete
linear system `|nD|` of `𝒪_X(nD)` has dimension `0` when `r ∣ n` and `-1` otherwise. -/
theorem dim_complete_weil_nsmul_of_addOrderOf_eq [IsAlgClosed k] [IsIntegral X]
    {q : X ⟶ Spec (.of k)} (hq : Projective q) (hreg : X.IsRegular) :
    letI := isNoetherian_of_projective q hq
    letI := isSeparated_of_projective q hq
    ∀ (D : X.WeilDivisor) {r : ℕ}, 0 < r →
      addOrderOf (weilClassEquivPicard hreg.isLocallyFactorial
        (X.weilDivisorClassHom (satisfiesConditionStar_of_isLocallyFactorial
          hreg.isLocallyFactorial) D)) = r →
      ∀ n : ℕ,
        (complete hq (weilCartierEquiv hreg.isLocallyFactorial (n • D)).isInvertible_sheaf).dim =
          if r ∣ n then 0 else -1 := by
  let := isNoetherian_of_projective q hq
  let := isSeparated_of_projective q hq
  intro D r hr0 hr n
  exact dim_complete_of_iso_nsmul hq (weilCartierEquiv hreg.isLocallyFactorial D) hr0 hr n _
    (eqToIso (congrArg CartierDivisor.sheaf (map_nsmul _ n D)))

/-- **Torsion linear systems are periodic** (Hartshorne II, Exercise 7.6(b)): for a Weil divisor
`D` on a regular integral scheme projective over an algebraically closed field, whose class in
`Pic X ≅ Cl X` has finite order `r`, the function `n ↦ dim |nD|` is periodic of period `r`. -/
theorem periodic_dim_complete_weil_nsmul [IsAlgClosed k] [IsIntegral X]
    {q : X ⟶ Spec (.of k)} (hq : Projective q) (hreg : X.IsRegular) :
    letI := isNoetherian_of_projective q hq
    letI := isSeparated_of_projective q hq
    ∀ (D : X.WeilDivisor) {r : ℕ}, 0 < r →
      addOrderOf (weilClassEquivPicard hreg.isLocallyFactorial
        (X.weilDivisorClassHom (satisfiesConditionStar_of_isLocallyFactorial
          hreg.isLocallyFactorial) D)) = r →
      Function.Periodic (fun n : ℕ =>
        (complete hq (weilCartierEquiv hreg.isLocallyFactorial (n • D)).isInvertible_sheaf).dim)
        r := by
  let := isNoetherian_of_projective q hq
  let := isSeparated_of_projective q hq
  intro D r hr0 hr n
  simp only [dim_complete_weil_nsmul_of_addOrderOf_eq hq hreg D hr0 hr, Nat.dvd_add_self_right]

end Hartshorne.LinearSystem
