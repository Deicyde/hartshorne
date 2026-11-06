/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FrobeniusTwist
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Hartshorne's finite-field `q`-power Frobenius

Hartshorne, *Algebraic Geometry*, Appendix C, §4 (p. 454).

Let `k = 𝔽_q` be a finite field of characteristic `p`, let `X` be a `k`-scheme and let
`X̄ = X ×_{Spec k} Spec k̄` be its base change to the fixed algebraic closure `k̄`.
The `q`-power absolute Frobenius of `X` is `k`-linear, because `q`-th powers fix `k`.
Its base change is the `k̄`-endomorphism `F : X̄ ⟶ X̄`.

* `F` followed by the first projection is the first projection followed by the `q`-power absolute
  Frobenius of `X`. Hence on a geometric point with coordinates `aᵢ` it gives the point with
  coordinates `aᵢ ^ q`.
* The descent identification `σ = id_X × Frob_q(Spec k̄)` is an automorphism of the scheme `X̄`.
  It identifies the `q`-Frobenius twist `X̄^{(q)}` with `X̄` over `k̄`. The `q`-power absolute
  Frobenius `F' : X̄^{(q)} ⟶ X̄` is `k̄`-linear, and `F = σ⁻¹ ≫ F'`.
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

namespace Scheme

variable {p : ℕ}

/-- A scheme over the spectrum of a field of characteristic `p` has characteristic `p`. -/
theorem isCharP_of_hom_spec {X : Scheme.{u}} {K : Type u} [Field K] [CharP K p]
    (f : X ⟶ Spec (.of K)) : X.IsCharP p where
  charP_stalk x := by
    let φ : K →+* X.presheaf.stalk x :=
      (X.presheaf.germ ⊤ x trivial).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    let _ := φ.toAlgebra
    exact charP_of_injective_algebraMap' K p

instance isCharP_spec (K : Type u) [Field K] [CharP K p] : (Spec (.of K)).IsCharP p :=
  isCharP_of_hom_spec (𝟙 _)

instance isCharP_over_left {K : Type u} [Field K] [CharP K p] (X : Over (Spec (.of K))) :
    X.left.IsCharP p :=
  isCharP_of_hom_spec X.hom

variable [Fact p.Prime]

/-- Absolute Frobenius commutes with every morphism of schemes of characteristic `p`. -/
theorem comp_absoluteFrobenius {X Y : Scheme.{u}} [X.IsCharP p] [Y.IsCharP p] (f : X ⟶ Y) :
    f ≫ Y.absoluteFrobenius p = X.absoluteFrobenius p ≫ f := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext s
  change X.presheaf.map (eqToHom rfl).op (f.app U (s ^ p)) = (f.app U s) ^ p
  simp

/-- The `n`-th iterate of the absolute Frobenius, raising local sections to `p ^ n`-th powers. -/
def iterateAbsoluteFrobenius (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] [X.IsCharP p] :
    ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => iterateAbsoluteFrobenius X p n ≫ X.absoluteFrobenius p

@[simp]
theorem iterateAbsoluteFrobenius_zero (X : Scheme.{u}) [X.IsCharP p] :
    X.iterateAbsoluteFrobenius p 0 = 𝟙 X := rfl

theorem iterateAbsoluteFrobenius_succ (X : Scheme.{u}) [X.IsCharP p] (n : ℕ) :
    X.iterateAbsoluteFrobenius p (n + 1) =
      X.iterateAbsoluteFrobenius p n ≫ X.absoluteFrobenius p := rfl

@[simp]
theorem iterateAbsoluteFrobenius_appTop (X : Scheme.{u}) [X.IsCharP p] (n : ℕ)
    (s : Γ(X, ⊤)) :
    (X.iterateAbsoluteFrobenius p n).appTop s = s ^ p ^ n := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [iterateAbsoluteFrobenius_succ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    change (X.iterateAbsoluteFrobenius p n).appTop (s ^ p) = s ^ p ^ (n + 1)
    rw [ih, ← pow_mul, ← pow_succ']

/-- Iterated absolute Frobenius commutes with every morphism of schemes of characteristic `p`. -/
theorem comp_iterateAbsoluteFrobenius {X Y : Scheme.{u}} [X.IsCharP p] [Y.IsCharP p]
    (f : X ⟶ Y) (n : ℕ) :
    f ≫ Y.iterateAbsoluteFrobenius p n = X.iterateAbsoluteFrobenius p n ≫ f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterateAbsoluteFrobenius_succ, iterateAbsoluteFrobenius_succ, ← Category.assoc, ih,
      Category.assoc, comp_absoluteFrobenius, Category.assoc]

/-- On the spectrum of a field, iterated absolute Frobenius is induced by any ring endomorphism
raising elements to their `p ^ n`-th powers. -/
theorem iterateAbsoluteFrobenius_spec (K : Type u) [Field K] [CharP K p] (n : ℕ)
    (φ : K →+* K) (hφ : ∀ a, φ a = a ^ p ^ n) :
    (Spec (.of K)).iterateAbsoluteFrobenius p n = Spec.map (CommRingCat.ofHom φ) := by
  apply ext_to_Spec
  ext a
  have hspec := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) a
  change (Scheme.ΓSpecIso (.of K)).inv (φ a) =
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of K)).inv a) at hspec
  change ((Spec (.of K)).iterateAbsoluteFrobenius p n).appTop
      ((Scheme.ΓSpecIso (.of K)).inv a) =
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of K)).inv a)
  rw [← hspec, hφ, map_pow]
  exact iterateAbsoluteFrobenius_appTop _ n _

end Scheme

namespace FiniteFieldFrobenius

open Scheme

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Finite k] [CharP k p]

/-- The exponent `n` with `q = p ^ n` for the finite field `k = 𝔽_q`. -/
abbrev exponent : ℕ :=
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  Module.finrank (ZMod p) k

theorem pow_exponent : p ^ exponent p k = Nat.card k := by
  let _ : Algebra (ZMod p) k := ZMod.algebra k p
  exact FiniteField.pow_finrank_eq_natCard p k

theorem pow_card_eq_self (a : k) : a ^ Nat.card k = a := by
  let _ := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card a

end FiniteFieldFrobenius

open Scheme FiniteFieldFrobenius

variable {p : ℕ} [Fact p.Prime] (k : Type u) [Field k] [Finite k] [CharP k p]

/-- The morphism `Spec 𝔽̄_q ⟶ Spec 𝔽_q` induced by the inclusion into the algebraic closure. -/
abbrev finiteFieldClosureSpecMap : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- The base change `X̄ = X ×_{Spec 𝔽_q} Spec 𝔽̄_q` of a scheme over a finite field to the
fixed algebraic closure, as a scheme over `Spec 𝔽̄_q`. -/
def finiteFieldBaseChange (X : Over (Spec (.of k))) : Over (Spec (.of (AlgebraicClosure k))) :=
  (Over.pullback (finiteFieldClosureSpecMap k)).obj X

/-- The `q`-power absolute Frobenius of a scheme over `𝔽_q` is `𝔽_q`-linear. -/
theorem iterateAbsoluteFrobenius_exponent_comp_hom (X : Over (Spec (.of k))) :
    X.left.iterateAbsoluteFrobenius p (exponent p k) ≫ X.hom = X.hom := by
  rw [← comp_iterateAbsoluteFrobenius,
    iterateAbsoluteFrobenius_spec k (exponent p k) (RingHom.id k)
      (fun a ↦ by rw [pow_exponent, RingHom.id_apply, pow_card_eq_self]),
    CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

/-- The `q`-power absolute Frobenius of a scheme over `𝔽_q`, as an `𝔽_q`-endomorphism. -/
def finiteFieldAbsoluteFrobeniusOver (X : Over (Spec (.of k))) : X ⟶ X :=
  Over.homMk (X.left.iterateAbsoluteFrobenius p (exponent p k))
    (iterateAbsoluteFrobenius_exponent_comp_hom k X)

/-- **Hartshorne's `q`-power Frobenius** `F : X̄ ⟶ X̄`, the `𝔽̄_q`-endomorphism of the base change
of an `𝔽_q`-scheme obtained by base-changing the `q`-power absolute Frobenius of `X`. On
geometric points it raises coordinates to their `q`-th powers. -/
def finiteFieldQFrobenius (X : Over (Spec (.of k))) :
    finiteFieldBaseChange k X ⟶ finiteFieldBaseChange k X :=
  (Over.pullback (finiteFieldClosureSpecMap k)).map (finiteFieldAbsoluteFrobeniusOver (p := p) k X)

/-- The projection `X̄ ⟶ X`. -/
def finiteFieldBaseChangeFst (X : Over (Spec (.of k))) : (finiteFieldBaseChange k X).left ⟶ X.left :=
  pullback.fst X.hom (finiteFieldClosureSpecMap k)

/-- `F` is the base change of the `q`-power absolute Frobenius of `X`. -/
theorem finiteFieldQFrobenius_left_fst (X : Over (Spec (.of k))) :
    (finiteFieldQFrobenius (p := p) k X).left ≫ finiteFieldBaseChangeFst k X =
      finiteFieldBaseChangeFst k X ≫ X.left.iterateAbsoluteFrobenius p (exponent p k) :=
  pullback.lift_fst _ _ _

/-- `F` is `𝔽̄_q`-linear. -/
theorem finiteFieldQFrobenius_left_hom (X : Over (Spec (.of k))) :
    (finiteFieldQFrobenius (p := p) k X).left ≫ (finiteFieldBaseChange k X).hom =
      (finiteFieldBaseChange k X).hom :=
  Over.w (finiteFieldQFrobenius (p := p) k X)

/-- **Action of `F` on geometric points.** If a point of `X̄` with values in a field `K` of
characteristic `p` has coordinates `aᵢ` (its image in `X`), then its image under `F` has
coordinates `aᵢ ^ q`: the point is precomposed with the `q`-th power map of `K`. -/
theorem finiteFieldQFrobenius_point (X : Over (Spec (.of k))) {K : Type u} [Field K] [CharP K p]
    (φ : K →+* K) (hφ : ∀ a, φ a = a ^ Nat.card k)
    (x : Spec (.of K) ⟶ (finiteFieldBaseChange k X).left) :
    x ≫ (finiteFieldQFrobenius (p := p) k X).left ≫ finiteFieldBaseChangeFst k X =
      Spec.map (CommRingCat.ofHom φ) ≫ x ≫ finiteFieldBaseChangeFst k X := by
  rw [finiteFieldQFrobenius_left_fst, ← Category.assoc, comp_iterateAbsoluteFrobenius,
    iterateAbsoluteFrobenius_spec K _ φ (fun a ↦ by rw [hφ, pow_exponent])]

/-- The `q`-power Frobenius automorphism `a ↦ a ^ q` of `𝔽̄_q`. -/
abbrev finiteFieldClosureQFrobenius : AlgebraicClosure k ≃+* AlgebraicClosure k :=
  iterateFrobeniusEquiv (AlgebraicClosure k) p (exponent p k)

theorem finiteFieldClosureQFrobenius_apply (a : AlgebraicClosure k) :
    finiteFieldClosureQFrobenius (p := p) k a = a ^ Nat.card k := by
  rw [iterateFrobeniusEquiv_def, pow_exponent]

/-- The `q`-power Frobenius of `Spec 𝔽̄_q`. -/
def finiteFieldClosureSpecQFrobenius :
    Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of (AlgebraicClosure k)) :=
  Spec.map (finiteFieldClosureQFrobenius (p := p) k).toCommRingCatIso.hom

instance : IsIso (finiteFieldClosureSpecQFrobenius (p := p) k) := by
  unfold finiteFieldClosureSpecQFrobenius
  infer_instance

omit [Finite k] in
/-- The `q`-power Frobenius of `Spec 𝔽̄_q` is the `q`-power absolute Frobenius. -/
theorem iterateAbsoluteFrobenius_closureSpec :
    (Spec (.of (AlgebraicClosure k))).iterateAbsoluteFrobenius p (exponent p k) =
      finiteFieldClosureSpecQFrobenius (p := p) k :=
  iterateAbsoluteFrobenius_spec _ _ _ fun _ ↦ rfl

/-- The `q`-power Frobenius of `Spec 𝔽̄_q` is a morphism over `Spec 𝔽_q`. -/
theorem finiteFieldClosureSpecQFrobenius_comp :
    finiteFieldClosureSpecQFrobenius (p := p) k ≫ finiteFieldClosureSpecMap k =
      finiteFieldClosureSpecMap k := by
  rw [finiteFieldClosureSpecQFrobenius, RingEquiv.toCommRingCatIso_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, finiteFieldClosureQFrobenius_apply,
    ← map_pow, pow_card_eq_self]

/-- Hartshorne's `q`-Frobenius twist of `X̄`: the same scheme, with structure morphism followed by
the `q`-power Frobenius of `Spec 𝔽̄_q`. -/
def finiteFieldBaseChangeQTwist (X : Over (Spec (.of k))) :
    Over (Spec (.of (AlgebraicClosure k))) :=
  Over.mk ((finiteFieldBaseChange k X).hom ≫ finiteFieldClosureSpecQFrobenius (p := p) k)

/-- The `q`-power absolute Frobenius of `X̄`, as Hartshorne's `𝔽̄_q`-morphism `X̄^{(q)} ⟶ X̄` from
the `q`-twist. -/
def finiteFieldQFrobeniusTwistTo (X : Over (Spec (.of k))) :
    finiteFieldBaseChangeQTwist (p := p) k X ⟶ finiteFieldBaseChange k X :=
  Over.homMk ((finiteFieldBaseChange k X).left.iterateAbsoluteFrobenius p (exponent p k)) <| by
    change _ ≫ (finiteFieldBaseChange k X).hom =
      (finiteFieldBaseChange k X).hom ≫ finiteFieldClosureSpecQFrobenius (p := p) k
    rw [← comp_iterateAbsoluteFrobenius, iterateAbsoluteFrobenius_closureSpec]

/-- The underlying scheme map of the descent identification `id_X × Frob_q(Spec 𝔽̄_q)`. -/
def finiteFieldDescentHom (X : Over (Spec (.of k))) :
    (finiteFieldBaseChange k X).left ⟶ (finiteFieldBaseChange k X).left :=
  pullback.map X.hom (finiteFieldClosureSpecMap k) X.hom (finiteFieldClosureSpecMap k) (𝟙 _)
    (finiteFieldClosureSpecQFrobenius (p := p) k) (𝟙 _)
    (by simp) (by rw [Category.comp_id, finiteFieldClosureSpecQFrobenius_comp])

instance (X : Over (Spec (.of k))) : IsIso (finiteFieldDescentHom (p := p) k X) := by
  unfold finiteFieldDescentHom
  exact pullback.map_isIso _ _ _ _ _ _ _ _ _

theorem finiteFieldDescentHom_fst (X : Over (Spec (.of k))) :
    finiteFieldDescentHom (p := p) k X ≫ finiteFieldBaseChangeFst k X =
      finiteFieldBaseChangeFst k X :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem finiteFieldDescentHom_hom (X : Over (Spec (.of k))) :
    finiteFieldDescentHom (p := p) k X ≫ (finiteFieldBaseChange k X).hom =
      (finiteFieldBaseChange k X).hom ≫ finiteFieldClosureSpecQFrobenius (p := p) k :=
  pullback.lift_snd _ _ _

/-- The descent identification `id_X × Frob_q(Spec 𝔽̄_q)` as an automorphism of the scheme `X̄`. -/
def finiteFieldDescentSchemeIso (X : Over (Spec (.of k))) :
    (finiteFieldBaseChange k X).left ≅ (finiteFieldBaseChange k X).left :=
  asIso (finiteFieldDescentHom (p := p) k X)

/-- **Descent identification.** The `q`-Frobenius twist of `X̄` is identified with `X̄` over
`𝔽̄_q` by `id_X × Frob_q(Spec 𝔽̄_q)`. -/
def finiteFieldDescentIso (X : Over (Spec (.of k))) :
    finiteFieldBaseChangeQTwist (p := p) k X ≅ finiteFieldBaseChange k X :=
  Over.isoMk (finiteFieldDescentSchemeIso (p := p) k X) (finiteFieldDescentHom_hom k X)

/-- **Hartshorne's definition of `F`.** Under the descent identification of the `q`-twist with
`X̄`, `F` is the `q`-power absolute Frobenius `X̄^{(q)} ⟶ X̄`. -/
theorem finiteFieldQFrobenius_eq_descentIso_inv_comp (X : Over (Spec (.of k))) :
    finiteFieldQFrobenius (p := p) k X =
      (finiteFieldDescentIso (p := p) k X).inv ≫ finiteFieldQFrobeniusTwistTo k X := by
  rw [Iso.eq_inv_comp]
  ext1
  rw [Over.comp_left]
  change finiteFieldDescentHom (p := p) k X ≫ (finiteFieldQFrobenius (p := p) k X).left =
    (finiteFieldBaseChange k X).left.iterateAbsoluteFrobenius p (exponent p k)
  apply pullback.hom_ext
  · change _ ≫ finiteFieldBaseChangeFst k X = _ ≫ finiteFieldBaseChangeFst k X
    rw [Category.assoc, finiteFieldQFrobenius_left_fst, ← Category.assoc,
      finiteFieldDescentHom_fst, comp_iterateAbsoluteFrobenius]
  · change _ ≫ (finiteFieldBaseChange k X).hom = _ ≫ (finiteFieldBaseChange k X).hom
    rw [Category.assoc, finiteFieldQFrobenius_left_hom, finiteFieldDescentHom_hom,
      ← comp_iterateAbsoluteFrobenius, iterateAbsoluteFrobenius_closureSpec]

end AlgebraicGeometry
