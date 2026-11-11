/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.CanonicalRingFunctionFieldEmbedding
import Hartshorne.Scheme.Differentials.CanonicalDivisorClass

/-!
# The Kodaira dimension

Hartshorne, *Algebraic Geometry*, V.6, definition of the Kodaira dimension (pp. 421–422).

For an integral scheme `X` over a field `k` whose canonical sheaf `ω_X` is invertible (for
instance a nonsingular variety), the Kodaira dimension is the integer
`κ(X) = trdeg_k R(X, K) - 1`, where `R(X, K) = ⨁_{n ≥ 0} H⁰(X, ω_X^{⊗ n})` is the canonical section
ring (`Hartshorne.kodairaDimension`).

* When `X` is moreover of finite type and of dimension `d`, the transcendence degree of `R(X, K)`
  is finite and equals `κ(X) + 1` (`Hartshorne.trdeg_canonicalSectionRing_eq`).
* Always `-1 ≤ κ(X)` (`Hartshorne.neg_one_le_kodairaDimension`). Over an algebraically closed
  field, for `X` also universally closed (for instance proper), `κ(X) = -1` exactly when every
  positive-degree piece `H⁰(X, ω_X^{⊗ n})`, `n > 0`, is zero
  (`Hartshorne.kodairaDimension_eq_neg_one_iff`), and otherwise `κ(X) ≥ 0`
  (`Hartshorne.kodairaDimension_nonneg_iff`).
* The value does not depend on the representative of the canonical divisor: for every Cartier
  divisor `K` in the canonical divisor class, the ring `⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))` has the same
  transcendence degree over `k` as `R(X, K)`
  (`Hartshorne.trdeg_divisorMultipleSectionRing_eq`,
  `Hartshorne.kodairaDimension_eq_of_canonicalDivisorClass`).
-/

open CategoryTheory Opposite
open scoped DirectSum

namespace Hartshorne

open AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

/-! ### The section ring of the multiples of a Cartier divisor as a `k`-algebra -/

section DivisorMultipleSectionRing

variable {X : Scheme.{u}}

/-- The ring `⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))` is commutative: its multiplication is transported from
`⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n})`, which is commutative because `𝒪_X(K)` is invertible. -/
noncomputable instance DivisorMultipleSectionRing.instCommRing (K : X.CartierDivisor) :
    CommRing (DivisorMultipleSectionRing K) :=
  letI := TensorPowerSectionRing.commRing (R := X.sheaf) K.sheaf (op ⊤)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 K.isInvertible_sheaf)
  (divisorMultipleSectionsAddEquiv K).toEquiv.commRing

variable [IsIntegral X] {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-- The `k`-algebra structure of `⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))` on an integral scheme over `k`: a
scalar `c ∈ k` is the constant section `c` of `𝒪_X = 𝒪_X(0 · K)` in degree `0`. -/
@[instance_reducible]
noncomputable def DivisorMultipleSectionRing.algebra (K : X.CartierDivisor) :
    Algebra k (DivisorMultipleSectionRing K) :=
  ((divisorMultipleSectionRingEquiv K).symm.toRingHom.comp
    (TensorPowerSectionRing.scalarRingHom f K.isInvertible_sheaf)).toAlgebra

end DivisorMultipleSectionRing

/-! ### The Kodaira dimension -/

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
  (hω : (canonicalSheaf f).IsInvertible)

/-- **The Kodaira dimension** `κ(X) = trdeg_k R(X, K) - 1` (Hartshorne V.6, pp. 421–422), for an
integral scheme `X` over `k` with invertible canonical sheaf `ω_X` (for instance a nonsingular
variety; see `Hartshorne.canonicalSheaf_isInvertible`), where `R(X, K) = ⨁_{n ≥ 0} H⁰(X, ω_X^{⊗ n})`
is the canonical section ring with its `k`-algebra structure. It is an integer; the transcendence
degree is finite when `X` is of finite type and finite-dimensional
(`Hartshorne.trdeg_canonicalSectionRing_eq`). -/
noncomputable def kodairaDimension : ℤ :=
  letI := TensorPowerSectionRing.commRing (R := X.sheaf) (canonicalSheaf f) (op ⊤)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 hω)
  letI := TensorPowerSectionRing.sectionRingAlgebra f hω
  ((Algebra.trdeg k (CanonicalSectionRing f)).toNat : ℤ) - 1

/-- **The Kodaira dimension is at least `-1`.** -/
theorem neg_one_le_kodairaDimension : -1 ≤ kodairaDimension f hω := by
  rw [kodairaDimension]
  omega

/-- **`trdeg_k R(X, K) = κ(X) + 1`.** For `X` integral, of finite type and of dimension `d` over
`k`, with `ω_X` invertible, the transcendence degree of the canonical section ring over `k` is
finite and equals `κ(X) + 1`. -/
theorem trdeg_canonicalSectionRing_eq (hf : FiniteType f) {d : ℕ}
    (hd : topologicalKrullDim X = d) :
    letI := TensorPowerSectionRing.commRing (R := X.sheaf) (canonicalSheaf f) (op ⊤)
      ((Scheme.Modules.isInvertible_iff_ringed _).1 hω)
    letI := TensorPowerSectionRing.sectionRingAlgebra f hω
    Algebra.trdeg k (CanonicalSectionRing f) = ((kodairaDimension f hω + 1).toNat : Cardinal) := by
  let _ := TensorPowerSectionRing.commRing (R := X.sheaf) (canonicalSheaf f) (op ⊤)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 hω)
  let _ := TensorPowerSectionRing.sectionRingAlgebra f hω
  have h2 : ((d + 1 : ℕ) : Cardinal) < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  push_cast at h2
  have hlt : Algebra.trdeg k (CanonicalSectionRing f) < Cardinal.aleph0 :=
    (TensorPowerSectionRing.trdeg_le f hf hω hd).trans_lt h2
  rw [kodairaDimension, sub_add_cancel, Int.toNat_natCast, Cardinal.cast_toNat_of_lt_aleph0 hlt]

/-- **`κ(X) = -1` exactly when every positive pluricanonical space vanishes.** For `X` integral,
universally closed (for instance proper), of finite type and of dimension `d` over an
algebraically closed field `k`, with `ω_X` invertible, `κ(X) = -1` if and only if
`H⁰(X, ω_X^{⊗ m}) = 0` for every `m > 0`. -/
theorem kodairaDimension_eq_neg_one_iff [IsAlgClosed k] [UniversallyClosed f] (hf : FiniteType f)
    {d : ℕ} (hd : topologicalKrullDim X = d) :
    kodairaDimension f hω = -1 ↔
      ∀ m : ℕ, 0 < m → ∀ s : CanonicalSectionRing.Component f m, s = 0 := by
  let _ := TensorPowerSectionRing.commRing (R := X.sheaf) (canonicalSheaf f) (op ⊤)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 hω)
  let _ := TensorPowerSectionRing.sectionRingAlgebra f hω
  have _ : IsDomain (CanonicalSectionRing f) := TensorPowerSectionRing.isDomain_of_isInvertible hω
  have htr := trdeg_canonicalSectionRing_eq f hω hf hd
  have h1 : kodairaDimension f hω = -1 ↔ Algebra.trdeg k (CanonicalSectionRing f) = 0 := by
    rw [htr]
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      have h' : (kodairaDimension f hω + 1).toNat = 0 := by exact_mod_cast h
      have := neg_one_le_kodairaDimension f hω
      omega
  rw [h1, trdeg_eq_zero_iff]
  constructor
  · intro halg m hm s
    have _ : Algebra.IsIntegral k (CanonicalSectionRing f) := inferInstance
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
      (K := CanonicalSectionRing f)).2 (DirectSum.of _ m s)
    have hm' := congrArg (fun x : CanonicalSectionRing f => x m) hc
    change (DirectSum.of _ 0 _ : CanonicalSectionRing f) m = (DirectSum.of _ m s) m at hm'
    rwa [DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ (Nat.pos_iff_ne_zero.1 hm),
      eq_comm] at hm'
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨c, hc⟩ := (canonicalSectionRing_degreeZero_bijective f).2 (x 0)
    have hx : algebraMap k (CanonicalSectionRing f) c = x := by
      refine DirectSum.ext fun i => ?_
      change (DirectSum.of _ 0 _ : CanonicalSectionRing f) i = x i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [DirectSum.of_eq_same]
        exact hc
      · rw [DirectSum.of_eq_of_ne _ _ _ (Nat.pos_iff_ne_zero.1 hi), h i hi (x i)]
    rw [← hx]
    exact isAlgebraic_algebraMap c

/-- **`κ(X) ≥ 0` exactly when some positive pluricanonical space is nonzero.** Under the
hypotheses of `Hartshorne.kodairaDimension_eq_neg_one_iff`, `κ(X)` is a nonnegative integer if
and only if `H⁰(X, ω_X^{⊗ m}) ≠ 0` for some `m > 0`. -/
theorem kodairaDimension_nonneg_iff [IsAlgClosed k] [UniversallyClosed f] (hf : FiniteType f)
    {d : ℕ} (hd : topologicalKrullDim X = d) :
    0 ≤ kodairaDimension f hω ↔
      ∃ m : ℕ, 0 < m ∧ ∃ s : CanonicalSectionRing.Component f m, s ≠ 0 := by
  have h := kodairaDimension_eq_neg_one_iff f hω hf hd
  have h' := neg_one_le_kodairaDimension f hω
  by_cases hk : kodairaDimension f hω = -1
  · have := h.1 hk
    simp only [hk, Int.reduceNeg, Left.nonneg_neg_iff, Int.reduceLE, false_iff, not_exists,
      not_and, ne_eq, not_not]
    exact this
  · have := mt h.2 hk
    push Not at this
    exact iff_of_true (by omega) this

/-- **Independence of the canonical divisor, on rings.** For a Cartier divisor `K` with
`φ : 𝒪_X(K) ≅ ω_X`, the ring `⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))` and the canonical section ring
`R(X, K) = ⨁_{n ≥ 0} H⁰(X, ω_X^{⊗ n})` have the same transcendence degree over `k`. -/
theorem trdeg_divisorMultipleSectionRing_eq {K : X.CartierDivisor}
    (φ : K.sheaf ≅ canonicalSheaf f) :
    letI := DivisorMultipleSectionRing.algebra f K
    letI := TensorPowerSectionRing.commRing (R := X.sheaf) (canonicalSheaf f) (op ⊤)
      ((Scheme.Modules.isInvertible_iff_ringed _).1 hω)
    letI := TensorPowerSectionRing.sectionRingAlgebra f hω
    Algebra.trdeg k (DivisorMultipleSectionRing K) = Algebra.trdeg k (CanonicalSectionRing f) := by
  let _ := DivisorMultipleSectionRing.algebra f K
  let _ := TensorPowerSectionRing.commRing (R := X.sheaf) (canonicalSheaf f) (op ⊤)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 hω)
  let _ := TensorPowerSectionRing.sectionRingAlgebra f hω
  refine (AlgEquiv.ofRingEquiv (f := canonicalSectionRingEquivOfDivisor f φ) fun c => ?_).trdeg_eq
  set r : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c
  change canonicalSectionRingEquivOfIso f φ ((divisorMultipleSectionRingEquiv K)
    ((divisorMultipleSectionRingEquiv K).symm (TensorPowerSectionRing.scalar f K.sheaf c))) =
      TensorPowerSectionRing.scalar f (canonicalSheaf f) c
  rw [RingEquiv.apply_symm_apply, TensorPowerSectionRing.scalar, canonicalSectionRingEquivOfIso_of,
    TensorPowerSectionRing.scalar]
  congr 1
  change (TensorPowerSectionRing.powMap φ.hom 0).val.app (op ⊤)
    (r • TensorPowerSectionRing.oneSec (R := X.sheaf) K.sheaf (op ⊤)) = _
  rw [map_smul]
  exact congrArg (r • ·) (TensorPowerSectionRing.powMap_oneSec φ.hom (op ⊤))

/-- **The Kodaira dimension does not depend on the representative of the canonical divisor**
(Hartshorne V.6, pp. 421–422). For every Cartier divisor `K` in the canonical divisor class,
`trdeg_k (⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))) - 1 = κ(X)`. -/
theorem kodairaDimension_eq_of_canonicalDivisorClass {K : X.CartierDivisor}
    (hK : X.cartierDivisorClassHom K = canonicalDivisorClass f hω) :
    letI := DivisorMultipleSectionRing.algebra f K
    ((Algebra.trdeg k (DivisorMultipleSectionRing K)).toNat : ℤ) - 1 = kodairaDimension f hω := by
  obtain ⟨φ⟩ := (cartierDivisorClassHom_eq_canonicalDivisorClass_iff f hω K).1 hK
  rw [trdeg_divisorMultipleSectionRing_eq f hω φ, kodairaDimension]

end Hartshorne
