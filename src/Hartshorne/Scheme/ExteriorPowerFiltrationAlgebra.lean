/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.OrzechProperty
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The exterior-power filtration attached to a submodule

Module-level input for Hartshorne, *Algebraic Geometry*, II, Exercise 5.16(d).

Let `A` be a commutative ring and `i : M' → M` a linear map. For `p ≤ r` let
`α_p : ⋀^p M' ⊗ ⋀^{r-p} M → ⋀^r M` be `x ⊗ y ↦ (⋀^p i)(x) ∧ y` (`alpha`), and let
`F^p ⊆ ⋀^r M` be its image (`filt`; `F^p = 0` for `p > r`). This is a decreasing filtration
(`filt_antitone`) with `F^0 = ⋀^r M` (`filt_zero`).

Main result (`alpha_mem_filt_succ_iff`): suppose `0 → M' → M → M'' → 0` is exact (with maps `i`,
`q`) and split by `s : M'' → M`, and that `M'`, `M''` are finite free. Then for `p ≤ r` an element
`z` of `⋀^p M' ⊗ ⋀^{r-p} M` satisfies `α_p z ∈ F^{p+1}` if and only if `z` is killed by
`id ⊗ ⋀^{r-p} q : ⋀^p M' ⊗ ⋀^{r-p} M → ⋀^p M' ⊗ ⋀^{r-p} M''`. Since `α_p` maps onto `F^p` and
`id ⊗ ⋀^{r-p} q` is onto, this identifies `F^p / F^{p+1}` with `⋀^p M' ⊗ ⋀^{r-p} M''`.

The computations take place in the exterior algebra, with `P` the submodule spanned by the image
of `M'` and `Q` the one spanned by `M` (`F^p = P^p Q^{r-p}`); submodules of degree one commute
(`commute_of_le_range_ι`). The map `⨁_k ⋀^k M' ⊗ ⋀^{r-k} M'' → ⋀^r M` given by the splitting is
surjective, hence (the ranks agreeing by Vandermonde's identity) injective, which gives the
nontrivial implication.
-/

universe u

open ExteriorAlgebra TensorProduct

namespace Hartshorne

namespace ExteriorPowerFiltration

variable {A : Type u} [CommRing A]

section Wedge

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Submodules of the exterior algebra contained in the image of `M` commute with each other. -/
lemma commute_of_le_range_ι {X Y : Submodule A (ExteriorAlgebra A M)}
    (hX : X ≤ LinearMap.range (ι A)) (hY : Y ≤ LinearMap.range (ι A)) : Commute X Y := by
  have key : ∀ {X Y : Submodule A (ExteriorAlgebra A M)}, X ≤ LinearMap.range (ι A) →
      Y ≤ LinearMap.range (ι A) → X * Y ≤ Y * X := by
    intro X Y hX hY
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨a, rfl⟩ := hX hx
    obtain ⟨b, rfl⟩ := hY hy
    rw [eq_neg_of_add_eq_zero_left (ι_add_mul_swap (R := A) a b)]
    exact neg_mem (Submodule.mul_mem_mul hy hx)
  exact le_antisymm (key hX hY) (key hY hX)

/-- The exterior product `⋀^a M × ⋀^b M → ⋀^r M`, for `a + b = r`. -/
def wedge {a b r : ℕ} (h : a + b = r) : ⋀[A]^a M →ₗ[A] ⋀[A]^b M →ₗ[A] ⋀[A]^r M :=
  LinearMap.mk₂ A (fun x y => ⟨x * y, h ▸ SetLike.mul_mem_graded x.2 y.2⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _))
    (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

@[simp]
lemma coe_wedge {a b r : ℕ} (h : a + b = r) (x : ⋀[A]^a M) (y : ⋀[A]^b M) :
    (wedge h x y : ExteriorAlgebra A M) = x * y := rfl

variable {N N₁ N₂ : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N₁] [Module A N₁]
  [AddCommGroup N₂] [Module A N₂]

/-- The map of exterior powers is the restriction of the map of exterior algebras. -/
lemma coe_exteriorPower_map (f : N →ₗ[A] M) {n : ℕ} (x : ⋀[A]^n N) :
    (exteriorPower.map n f x : ExteriorAlgebra A M) = ExteriorAlgebra.map f x := by
  have : (⋀[A]^n M).subtype ∘ₗ exteriorPower.map n f =
      (ExteriorAlgebra.map f).toLinearMap ∘ₗ (⋀[A]^n N).subtype := by
    apply exteriorPower.linearMap_ext
    ext m
    simp [exteriorPower.map_apply_ιMulti, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun this x

/-- The image of `⋀^n N` in the exterior algebra of `M` is the `n`-th power of the image of
`N`. -/
lemma map_exteriorPower (f : N →ₗ[A] M) (n : ℕ) :
    (⋀[A]^n N).map (ExteriorAlgebra.map f).toLinearMap = LinearMap.range (ι A ∘ₗ f) ^ n := by
  change (LinearMap.range (ι A) ^ n).map (ExteriorAlgebra.map f).toLinearMap = _
  rw [Submodule.map_pow, ← LinearMap.range_comp, ExteriorAlgebra.map_comp_ι]

lemma map_mem_pow (f : N →ₗ[A] M) {n : ℕ} (x : ⋀[A]^n N) :
    ExteriorAlgebra.map f (x : ExteriorAlgebra A N) ∈ LinearMap.range (ι A ∘ₗ f) ^ n := by
  rw [← map_exteriorPower]
  exact Submodule.mem_map_of_mem x.2

/-- The map `⋀^a N₁ ⊗ ⋀^b N₂ → ⋀^r M`, `x ⊗ y ↦ (⋀^a f)(x) ∧ (⋀^b g)(y)`, for `a + b = r`. -/
noncomputable def wedgeMap (f : N₁ →ₗ[A] M) (g : N₂ →ₗ[A] M) {a b r : ℕ} (h : a + b = r) :
    ⋀[A]^a N₁ ⊗[A] ⋀[A]^b N₂ →ₗ[A] ⋀[A]^r M :=
  TensorProduct.lift (((wedge h).comp (exteriorPower.map a f)).compl₂ (exteriorPower.map b g))

lemma wedgeMap_tmul (f : N₁ →ₗ[A] M) (g : N₂ →ₗ[A] M) {a b r : ℕ} (h : a + b = r)
    (x : ⋀[A]^a N₁) (y : ⋀[A]^b N₂) :
    wedgeMap f g h (x ⊗ₜ y) = wedge h (exteriorPower.map a f x) (exteriorPower.map b g y) := rfl

lemma coe_wedgeMap_tmul (f : N₁ →ₗ[A] M) (g : N₂ →ₗ[A] M) {a b r : ℕ} (h : a + b = r)
    (x : ⋀[A]^a N₁) (y : ⋀[A]^b N₂) :
    (wedgeMap f g h (x ⊗ₜ y) : ExteriorAlgebra A M) =
      ExteriorAlgebra.map f (x : ExteriorAlgebra A N₁) *
        ExteriorAlgebra.map g (y : ExteriorAlgebra A N₂) := by
  rw [wedgeMap_tmul, coe_wedge, coe_exteriorPower_map, coe_exteriorPower_map]

/-- On wedges of vectors, `wedgeMap` is the wedge of the concatenated images. -/
lemma wedgeMap_ιMulti (f : N₁ →ₗ[A] M) (g : N₂ →ₗ[A] M) {a b r : ℕ} (h : a + b = r)
    (m₁ : Fin a → N₁) (m₂ : Fin b → N₂) :
    wedgeMap f g h (exteriorPower.ιMulti A a m₁ ⊗ₜ exteriorPower.ιMulti A b m₂) =
      exteriorPower.ιMulti A r (Fin.append (f ∘ m₁) (g ∘ m₂) ∘ Fin.cast h.symm) := by
  apply Subtype.ext
  rw [coe_wedgeMap_tmul, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti,
    ExteriorAlgebra.map_apply_ιMulti, ιMulti_mul_ιMulti]
  subst h
  rfl

/-- The image of `wedgeMap f g`, inside the exterior algebra. -/
lemma map_range_wedgeMap (f : N₁ →ₗ[A] M) (g : N₂ →ₗ[A] M) {a b r : ℕ} (h : a + b = r) :
    (LinearMap.range (wedgeMap f g h)).map (⋀[A]^r M).subtype =
      LinearMap.range (ι A ∘ₗ f) ^ a * LinearMap.range (ι A ∘ₗ g) ^ b := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Submodule.subtype_apply, coe_wedgeMap_tmul]
      exact Submodule.mul_mem_mul (map_mem_pow f x) (map_mem_pow g y)
    | add w w' hw hw' =>
      rw [map_add, map_add]
      exact add_mem hw hw'
  · refine Submodule.mul_le.2 fun u hu v hv => ?_
    rw [← map_exteriorPower] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨wedgeMap f g h (⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩), LinearMap.mem_range_self _ _,
      coe_wedgeMap_tmul f g h _ _⟩

lemma mem_of_coe_mem_map {r : ℕ} {L : Submodule A (⋀[A]^r M)} {x : ⋀[A]^r M}
    (hx : (x : ExteriorAlgebra A M) ∈ L.map (⋀[A]^r M).subtype) : x ∈ L := by
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← Subtype.ext hyx]

end Wedge

section Filtration

variable {M' M : Type*} [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
  (i : M' →ₗ[A] M)

/-- The map `⋀^p M' ⊗ ⋀^{r-p} M → ⋀^r M`, `x ⊗ y ↦ (⋀^p i)(x) ∧ y`, for `p ≤ r`. -/
noncomputable def alpha {p r : ℕ} (hp : p ≤ r) : ⋀[A]^p M' ⊗[A] ⋀[A]^(r - p) M →ₗ[A] ⋀[A]^r M :=
  wedgeMap i LinearMap.id (Nat.add_sub_cancel' hp)

/-- The standard filtration of `⋀^r M` attached to `i : M' → M`: `F^p` is the image of
`⋀^p M' ⊗ ⋀^{r-p} M → ⋀^r M` for `p ≤ r`, and `F^p = 0` for `p > r`. -/
noncomputable def filt (r p : ℕ) : Submodule A (⋀[A]^r M) :=
  if hp : p ≤ r then LinearMap.range (alpha i hp) else ⊥

lemma filt_of_le {r p : ℕ} (hp : p ≤ r) : filt i r p = LinearMap.range (alpha i hp) :=
  dif_pos hp

lemma filt_of_lt {r p : ℕ} (hp : r < p) : filt i r p = ⊥ :=
  dif_neg (Nat.not_le.2 hp)

lemma alpha_mem_filt {p r : ℕ} (hp : p ≤ r) (z : ⋀[A]^p M' ⊗[A] ⋀[A]^(r - p) M) :
    alpha i hp z ∈ filt i r p := by
  rw [filt_of_le i hp]
  exact LinearMap.mem_range_self _ _

lemma map_filt {r p : ℕ} (hp : p ≤ r) :
    (filt i r p).map (⋀[A]^r M).subtype =
      LinearMap.range (ι A ∘ₗ i) ^ p * LinearMap.range (ι A) ^ (r - p) := by
  rw [filt_of_le i hp, alpha, map_range_wedgeMap, LinearMap.comp_id]

lemma range_ι_comp_le (f : M' →ₗ[A] M) :
    LinearMap.range (ι A ∘ₗ f) ≤ LinearMap.range (ι A) :=
  LinearMap.range_comp_le_range _ _

/-- `F^0 = ⋀^r M`. -/
lemma filt_zero (r : ℕ) : filt i r 0 = ⊤ := by
  apply Submodule.map_injective_of_injective (⋀[A]^r M).injective_subtype
  rw [map_filt i (Nat.zero_le r), pow_zero, one_mul, Nat.sub_zero, Submodule.map_top,
    Submodule.range_subtype]

lemma filt_succ_le (r p : ℕ) : filt i r (p + 1) ≤ filt i r p := by
  rcases Nat.lt_or_ge r (p + 1) with h | h
  · rw [filt_of_lt i h]
    exact bot_le
  · rw [← Submodule.map_le_map_iff_of_injective (⋀[A]^r M).injective_subtype,
      map_filt i h, map_filt i (Nat.le_of_succ_le h)]
    have hr : r - p = (r - (p + 1)) + 1 := by omega
    rw [hr, pow_succ, pow_succ', mul_assoc]
    exact mul_le_mul' le_rfl (mul_le_mul' (range_ι_comp_le i) le_rfl)

/-- The filtration is decreasing. -/
lemma filt_antitone (r : ℕ) : Antitone (filt i r) :=
  antitone_nat_of_succ_le (filt_succ_le i r)

end Filtration

section Split

variable {M' M M'' : Type*} [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
  [AddCommGroup M''] [Module A M'']
  {i : M' →ₗ[A] M} {q : M →ₗ[A] M''} {s : M'' →ₗ[A] M}

local notation "P" => LinearMap.range (ι A ∘ₗ i)
local notation "Q" => LinearMap.range (ι A (M := M))
local notation "S" => LinearMap.range (ι A ∘ₗ s)

lemma sub_mem_range (hiq : LinearMap.range i = LinearMap.ker q) (hqs : q ∘ₗ s = LinearMap.id)
    (m : M) : m - s (q m) ∈ LinearMap.range i := by
  rw [hiq, LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply q s, hqs, LinearMap.id_apply,
    sub_self]

lemma range_ι_le_sup (hiq : LinearMap.range i = LinearMap.ker q) (hqs : q ∘ₗ s = LinearMap.id) :
    Q ≤ P ⊔ S := by
  rintro _ ⟨m, rfl⟩
  obtain ⟨x, hx⟩ := sub_mem_range hiq hqs m
  have : ι A m = ι A (i x) + ι A (s (q m)) := by rw [← map_add, hx, sub_add_cancel]
  rw [this]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨q m, rfl⟩

/-- `y - (⋀ (s ∘ q))(y) ∈ P Q^n` for `y ∈ Q^{n+1}`. -/
lemma sub_map_mem (hiq : LinearMap.range i = LinearMap.ker q) (hqs : q ∘ₗ s = LinearMap.id)
    (n : ℕ) {y : ExteriorAlgebra A M} (hy : y ∈ Q ^ (n + 1)) :
    y - ExteriorAlgebra.map (s ∘ₗ q) y ∈ P * Q ^ n := by
  let L : ExteriorAlgebra A M →ₗ[A] ExteriorAlgebra A M :=
    LinearMap.id - (ExteriorAlgebra.map (s ∘ₗ q)).toLinearMap
  change L y ∈ _
  change y ∈ ⋀[A]^(n + 1) M at hy
  rw [← ιMulti_span_fixedDegree] at hy
  induction hy using Submodule.span_induction with
  | zero => simp
  | add y y' _ _ hy hy' => rw [map_add]; exact add_mem hy hy'
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    induction n with
    | zero =>
      simp only [L, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply,
        ιMulti_succ_apply, ιMulti_zero_apply, mul_one,
        pow_zero, ExteriorAlgebra.map_apply_ι]
      obtain ⟨x, hx⟩ := sub_mem_range hiq hqs (m 0)
      rw [← map_sub, LinearMap.comp_apply, ← hx]
      exact ⟨x, rfl⟩
    | succ n ih =>
      simp only [L, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply,
        ExteriorAlgebra.map_apply_ιMulti] at ih ⊢
      rw [ιMulti_succ_apply (v := m), ιMulti_succ_apply (v := ⇑(s ∘ₗ q) ∘ m)]
      have hsplit : ι A (m 0) * ιMulti A (n + 1) (Matrix.vecTail m) -
          ι A ((s ∘ₗ q) (m 0)) * ιMulti A (n + 1) (Matrix.vecTail (⇑(s ∘ₗ q) ∘ m)) =
          ι A (m 0 - (s ∘ₗ q) (m 0)) * ιMulti A (n + 1) (Matrix.vecTail m) +
            ι A ((s ∘ₗ q) (m 0)) * (ιMulti A (n + 1) (Matrix.vecTail m) -
              ιMulti A (n + 1) (⇑(s ∘ₗ q) ∘ Matrix.vecTail m)) := by
        have ht : Matrix.vecTail (⇑(s ∘ₗ q) ∘ m) = ⇑(s ∘ₗ q) ∘ Matrix.vecTail m := rfl
        rw [ht, map_sub, sub_mul, mul_sub]
        abel
      rw [Function.comp_apply, hsplit]
      refine add_mem ?_ ?_
      · obtain ⟨x, hx⟩ := sub_mem_range hiq hqs (m 0)
        refine Submodule.mul_mem_mul ⟨x, by rw [LinearMap.comp_apply, hx]; rfl⟩ ?_
        exact ιMulti_range A (M := M) (n + 1) ⟨Matrix.vecTail m, rfl⟩
      · have h1 := Submodule.mul_mem_mul (LinearMap.mem_range_self (ι A) ((s ∘ₗ q) (m 0)))
          (ih (Matrix.vecTail m))
        have h2 : Q * (P * Q ^ n) ≤ P * Q ^ (n + 1) := by
          rw [← mul_assoc, (commute_of_le_range_ι (le_refl Q) (range_ι_comp_le i)).eq,
            mul_assoc, ← pow_succ']
        exact h2 h1

/-- `P^p (P + S)^n ≤ ∑_{k ≤ n} P^{p+k} S^{n-k}`. -/
lemma pow_mul_sup_pow_le (p n : ℕ) :
    P ^ p * (P ⊔ S) ^ n ≤ ⨆ (k : ℕ) (_ : k ≤ n), P ^ (p + k) * S ^ (n - k) := by
  induction n generalizing p with
  | zero =>
    refine le_trans ?_ (le_iSup₂_of_le 0 (le_refl 0) le_rfl)
    simp
  | succ n ih =>
    have hcomm : Commute S ((P ⊔ S) ^ n) := by
      refine Commute.pow_right ?_ n
      exact (commute_of_le_range_ι (range_ι_comp_le s) (sup_le (range_ι_comp_le i)
        (range_ι_comp_le s)))
    rw [pow_succ', ← mul_assoc, Submodule.mul_sup, Submodule.sup_mul]
    refine sup_le ?_ ?_
    · rw [← pow_succ]
      refine (ih (p + 1)).trans (iSup₂_le fun k hk => ?_)
      refine le_trans ?_ (le_iSup₂_of_le (k + 1) (by omega) le_rfl)
      rw [show p + 1 + k = p + (k + 1) by omega, show n - k = n + 1 - (k + 1) by omega]
    · rw [mul_assoc, hcomm.eq, ← mul_assoc]
      refine (mul_le_mul' (ih p) le_rfl).trans ?_
      rw [Submodule.iSup_mul]
      refine iSup_le fun k => ?_
      rw [Submodule.iSup_mul]
      refine iSup_le fun hk => ?_
      refine le_trans ?_ (le_iSup₂_of_le k (by omega) le_rfl)
      rw [mul_assoc, ← pow_succ, show n - k + 1 = n + 1 - k by omega]

variable (i s) in
/-- The map `⋀^k M' ⊗ ⋀^{r-k} M'' → ⋀^r M`, `x ⊗ y ↦ (⋀^k i)(x) ∧ (⋀^{r-k} s)(y)`. -/
noncomputable def phi (r : ℕ) (k : Fin (r + 1)) :
    ⋀[A]^(k : ℕ) M' ⊗[A] ⋀[A]^(r - k) M'' →ₗ[A] ⋀[A]^r M :=
  wedgeMap i s (Nat.add_sub_cancel' (Nat.lt_succ_iff.1 k.2))

variable (i s) in
/-- The sum `⨁_{k ≤ r} ⋀^k M' ⊗ ⋀^{r-k} M'' → ⋀^r M` of the maps `phi`. -/
noncomputable def phiSum (r : ℕ) :
    ((k : Fin (r + 1)) → ⋀[A]^(k : ℕ) M' ⊗[A] ⋀[A]^(r - k) M'') →ₗ[A] ⋀[A]^r M :=
  LinearMap.lsum A (fun k : Fin (r + 1) => ⋀[A]^(k : ℕ) M' ⊗[A] ⋀[A]^(r - k) M'') A (phi i s r)

lemma phiSum_single (r : ℕ) (k : Fin (r + 1))
    (z : ⋀[A]^(k : ℕ) M' ⊗[A] ⋀[A]^(r - k) M'') : phiSum i s r (Pi.single k z) = phi i s r k z :=
  LinearMap.lsum_piSingle _ _ _ _ _ _

lemma map_range_phi (r : ℕ) (k : Fin (r + 1)) :
    (LinearMap.range (phi i s r k)).map (⋀[A]^r M).subtype = P ^ (k : ℕ) * S ^ (r - k) :=
  map_range_wedgeMap _ _ _

variable (hiq : LinearMap.range i = LinearMap.ker q) (hqs : q ∘ₗ s = LinearMap.id)
include hiq hqs

/-- `⋀^r M` is spanned by the images of the maps `phi`. -/
lemma phiSum_surjective (r : ℕ) : Function.Surjective (phiSum i s r) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.map_injective_of_injective (⋀[A]^r M).injective_subtype
  apply le_antisymm (Submodule.map_mono le_top)
  rw [Submodule.map_top, Submodule.range_subtype]
  change Q ^ r ≤ _
  have h1 : Q ^ r ≤ P ^ 0 * (P ⊔ S) ^ r := by
    rw [pow_zero, one_mul]
    exact pow_le_pow_left' (range_ι_le_sup hiq hqs) r
  refine h1.trans ((pow_mul_sup_pow_le 0 r).trans (iSup₂_le fun k hk => ?_))
  rw [Nat.zero_add]
  have := map_range_phi (i := i) (s := s) r ⟨k, Nat.lt_succ_of_le hk⟩
  simp only at this
  rw [← this]
  refine Submodule.map_mono ?_
  rintro _ ⟨z, rfl⟩
  rw [← phiSum_single]
  exact LinearMap.mem_range_self _ _

/-- The splitting identifies `M` with `M' × M''`. -/
noncomputable def splitEquiv (hi : Function.Injective i) : (M' × M'') ≃ₗ[A] M :=
  LinearEquiv.ofBijective (LinearMap.coprod i s) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨x, y⟩ h
      rw [LinearMap.coprod_apply] at h
      have hq := congrArg q h
      have hx : q (i x) = 0 := by
        rw [← LinearMap.mem_ker, ← hiq]
        exact LinearMap.mem_range_self i x
      rw [map_add, hx, zero_add, ← LinearMap.comp_apply q s, hqs, LinearMap.id_apply,
        map_zero] at hq
      subst hq
      rw [map_zero, add_zero] at h
      have hx0 : x = 0 := hi (h.trans (map_zero i).symm)
      subst hx0
      rfl
    · intro m
      obtain ⟨x, hx⟩ := sub_mem_range hiq hqs m
      exact ⟨(x, q m), by rw [LinearMap.coprod_apply, hx, sub_add_cancel]⟩

variable [Module.Free A M'] [Module.Finite A M'] [Module.Free A M''] [Module.Finite A M'']

/-- The source and target of `phiSum` have the same rank (Vandermonde's identity). -/
lemma finrank_phiSum [Nontrivial A] (hi : Function.Injective i) (r : ℕ) :
    Module.finrank A ((k : Fin (r + 1)) → ⋀[A]^(k : ℕ) M' ⊗[A] ⋀[A]^(r - k) M'') =
      Module.finrank A (⋀[A]^r M) := by
  have e := splitEquiv hiq hqs hi
  have : Module.Free A M := Module.Free.of_equiv e
  have : Module.Finite A M := Module.Finite.equiv e
  rw [Module.finrank_pi_fintype, exteriorPower.finrank_eq, ← e.finrank_eq, Module.finrank_prod,
    Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => (Module.finrank A M').choose a * (Module.finrank A M'').choose b),
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.finrank_tensorProduct, exteriorPower.finrank_eq, exteriorPower.finrank_eq]

/-- `phiSum` is injective: a surjection between free modules of the same finite rank. -/
lemma phiSum_injective (hi : Function.Injective i) (r : ℕ) :
    Function.Injective (phiSum i s r) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := Module.subsingleton A ((k : Fin (r + 1)) → ⋀[A]^(k : ℕ) M' ⊗[A] ⋀[A]^(r - k) M'')
    exact Function.injective_of_subsingleton _
  · have e := splitEquiv hiq hqs hi
    have : Module.Free A M := Module.Free.of_equiv e
    have : Module.Finite A M := Module.Finite.equiv e
    let f := LinearEquiv.ofFinrankEq _ _ (finrank_phiSum hiq hqs hi r).symm
    have hinj := OrzechProperty.injective_of_surjective_endomorphism (f.toLinearMap ∘ₗ phiSum i s r)
      (f.surjective.comp (phiSum_surjective hiq hqs r))
    intro a b hab
    apply hinj
    simp only [LinearMap.comp_apply, hab]

/-- If `(⋀^p i)(x) ∧ (⋀^{r-p} s)(y)` (summed over a tensor) lies in `F^{p+1}`, it vanishes. -/
lemma eq_zero_of_phi_mem_filt (hi : Function.Injective i) {p r : ℕ} (hp : p ≤ r)
    (w : ⋀[A]^p M' ⊗[A] ⋀[A]^(r - p) M'')
    (h : phi i s r ⟨p, Nat.lt_succ_of_le hp⟩ w ∈ filt i r (p + 1)) : w = 0 := by
  classical
  let p' : Fin (r + 1) := ⟨p, Nat.lt_succ_of_le hp⟩
  let K : Submodule A (⋀[A]^r M) :=
    (LinearMap.ker (LinearMap.proj (R := A)
      (φ := fun k : Fin (r + 1) => ⋀[A]^(k : ℕ) M' ⊗[A] ⋀[A]^(r - k) M'') p')).map
      (phiSum i s r)
  have hK : filt i r (p + 1) ≤ K := by
    rcases Nat.lt_or_ge r (p + 1) with h' | h'
    · rw [filt_of_lt i h']
      exact bot_le
    · rw [← Submodule.map_le_map_iff_of_injective (⋀[A]^r M).injective_subtype, map_filt i h']
      have h1 : P ^ (p + 1) * Q ^ (r - (p + 1)) ≤ P ^ (p + 1) * (P ⊔ S) ^ (r - (p + 1)) :=
        mul_le_mul' le_rfl (pow_le_pow_left' (range_ι_le_sup hiq hqs) _)
      refine h1.trans ((pow_mul_sup_pow_le _ _).trans (iSup₂_le fun k hk => ?_))
      have hk' : p + 1 + k < r + 1 := by omega
      have := map_range_phi (i := i) (s := s) r ⟨p + 1 + k, hk'⟩
      simp only at this
      rw [show r - (p + 1) - k = r - (p + 1 + k) by omega, ← this]
      refine Submodule.map_mono ?_
      rintro _ ⟨z, rfl⟩
      rw [← phiSum_single]
      refine ⟨_, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_of_ne]
      intro hne
      have := congrArg Fin.val hne
      simp only [p'] at this
      omega
  obtain ⟨v, hv, hvw⟩ := hK h
  rw [← phiSum_single r p'] at hvw
  have := phiSum_injective hiq hqs hi r hvw
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, this,
    Pi.single_eq_same] at hv
  exact hv

omit [Module.Free A M'] [Module.Finite A M'] [Module.Free A M''] [Module.Finite A M''] in
/-- `α_p(z) ≡ α_p((id ⊗ ⋀(s ∘ q))(z))` modulo `F^{p+1}`. -/
lemma alpha_sub_mem_filt {p r : ℕ} (hp : p ≤ r) (z : ⋀[A]^p M' ⊗[A] ⋀[A]^(r - p) M) :
    alpha i hp z - alpha i hp (LinearMap.lTensor _ (exteriorPower.map (r - p) (s ∘ₗ q)) z) ∈
      filt i r (p + 1) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
    rw [map_add, map_add, map_add, add_sub_add_comm]
    exact add_mem hz hz'
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, ← map_sub, ← TensorProduct.tmul_sub]
    apply mem_of_coe_mem_map
    rw [alpha, coe_wedgeMap_tmul, ExteriorAlgebra.map_id, AlgHom.id_apply, Submodule.coe_sub,
      coe_exteriorPower_map]
    have key : ∀ (n : ℕ) (e : ExteriorAlgebra A M), e ∈ Q ^ (r - p) → r - p = n → e ∈ Q ^ n := by
      rintro n e he rfl
      exact he
    rcases Nat.lt_or_ge p r with h | h
    · rw [map_filt i h]
      have hy := key (r - (p + 1) + 1) _ y.2 (by omega)
      rw [pow_succ, mul_assoc]
      exact Submodule.mul_mem_mul (map_mem_pow i x) (sub_map_mem hiq hqs _ hy)
    · have hy := key 0 _ y.2 (by omega)
      rw [pow_zero] at hy
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 hy
      rw [← hc, AlgHom.commutes, sub_self, mul_zero]
      exact zero_mem _

omit hiq hqs [Module.Free A M'] [Module.Finite A M'] [Module.Free A M''] [Module.Finite A M''] in
lemma alpha_lTensor_map {p r : ℕ} (hp : p ≤ r) (u : ⋀[A]^p M' ⊗[A] ⋀[A]^(r - p) M'') :
    alpha i hp (LinearMap.lTensor _ (exteriorPower.map (r - p) s) u) =
      phi i s r ⟨p, Nat.lt_succ_of_le hp⟩ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' => rw [map_add, map_add, map_add, hu, hu']
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, alpha, wedgeMap_tmul, exteriorPower.map_id, LinearMap.id_apply]
    rfl

/-- **The graded pieces of the exterior-power filtration of a split exact sequence.** For
`0 → M' → M → M'' → 0` exact and split, with `M'` and `M''` finite free, and `p ≤ r`, an element
`z ∈ ⋀^p M' ⊗ ⋀^{r-p} M` has `α_p(z) ∈ F^{p+1}` if and only if `(id ⊗ ⋀^{r-p} q)(z) = 0`. -/
theorem alpha_mem_filt_succ_iff (hi : Function.Injective i) {p r : ℕ} (hp : p ≤ r)
    (z : ⋀[A]^p M' ⊗[A] ⋀[A]^(r - p) M) :
    alpha i hp z ∈ filt i r (p + 1) ↔
      LinearMap.lTensor _ (exteriorPower.map (r - p) q) z = 0 := by
  have hcomp : LinearMap.lTensor _ (exteriorPower.map (r - p) (s ∘ₗ q)) z =
      LinearMap.lTensor _ (exteriorPower.map (r - p) s)
        (LinearMap.lTensor _ (exteriorPower.map (r - p) q) z) := by
    rw [exteriorPower.map_comp, LinearMap.lTensor_comp_apply]
  have hD := alpha_sub_mem_filt hiq hqs hp z
  constructor
  · intro h
    have h2 := sub_mem h hD
    rw [sub_sub_cancel, hcomp, alpha_lTensor_map] at h2
    exact eq_zero_of_phi_mem_filt hiq hqs hi hp _ h2
  · intro h
    rw [hcomp, h, map_zero, map_zero, sub_zero] at hD
    exact hD

omit hiq [Module.Free A M''] [Module.Finite A M''] in
lemma lTensor_map_surjective (N : Type*) [AddCommGroup N] [Module A N] (n : ℕ) :
    Function.Surjective (LinearMap.lTensor N (exteriorPower.map n q)) :=
  LinearMap.lTensor_surjective _ (exteriorPower.map_surjective fun y =>
    ⟨s y, by rw [← LinearMap.comp_apply, hqs, LinearMap.id_apply]⟩)

end Split

section Rank

variable {M' M M'' : Type*} [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
  [AddCommGroup M''] [Module A M'']

/-- Exterior powers of a free module above its rank vanish. -/
lemma exteriorPower_subsingleton_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι A M)
    {k : ℕ} (hk : Fintype.card ι < k) : Subsingleton (⋀[A]^k M) := by
  let B := (b.reindex (Fintype.equivFin ι)).exteriorPower k
  have : IsEmpty (Set.powersetCard (Fin (Fintype.card ι)) k) := ⟨fun s => by
    have h1 := Set.powersetCard.card_eq s
    have h2 := Finset.card_le_univ (s : Finset (Fin (Fintype.card ι)))
    rw [Fintype.card_fin] at h2
    omega⟩
  exact B.repr.toEquiv.subsingleton

/-- If `⋀^p M'` vanishes, so does `F^p`. -/
lemma filt_eq_bot_of_subsingleton (i : M' →ₗ[A] M) {r p : ℕ} (h : Subsingleton (⋀[A]^p M')) :
    filt i r p = ⊥ := by
  rcases Nat.lt_or_ge r p with hp | hp
  · exact filt_of_lt i hp
  · rw [filt_of_le i hp, eq_bot_iff]
    rintro _ ⟨z, rfl⟩
    have hz : z = 0 := by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
      | add z z' hz hz' => rw [hz, hz', add_zero]
    rw [hz, map_zero]
    exact Submodule.zero_mem _

variable {i : M' →ₗ[A] M} {q : M →ₗ[A] M''} {s : M'' →ₗ[A] M}
  [Module.Free A M'] [Module.Finite A M'] [Module.Free A M''] [Module.Finite A M'']

/-- If the exterior powers `⋀^{r-k} M''` vanish for all `k < p`, then `F^p = ⋀^r M`. -/
lemma filt_eq_top_of_subsingleton (hi : Function.Injective i)
    (hiq : LinearMap.range i = LinearMap.ker q) (hqs : q ∘ₗ s = LinearMap.id) {r : ℕ} :
    ∀ p ≤ r, (∀ k < p, Subsingleton (⋀[A]^(r - k) M'')) → filt i r p = ⊤ := by
  intro p
  induction p with
  | zero => exact fun _ _ => filt_zero i r
  | succ p ih =>
    intro hp h
    have hp' : p ≤ r := Nat.le_of_succ_le hp
    rw [eq_top_iff, ← ih hp' fun k hk => h k (Nat.lt_succ_of_lt hk), filt_of_le i hp']
    rintro _ ⟨z, rfl⟩
    have := h p (Nat.lt_succ_self p)
    refine (alpha_mem_filt_succ_iff hiq hqs hi hp' z).2 ?_
    have hsub : ∀ w : ⋀[A]^p M' ⊗[A] ⋀[A]^(r - p) M'', w = 0 := fun w => by
      induction w using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
      | add w w' hw hw' => rw [hw, hw', add_zero]
    exact hsub _

end Rank

end ExteriorPowerFiltration

end Hartshorne
