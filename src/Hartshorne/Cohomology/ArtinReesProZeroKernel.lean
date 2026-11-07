/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ArtinReesInducedTopology
import Hartshorne.Scheme.InverseSystemMittagLeffler
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# The Artin–Rees kernel system is pro-zero

Hartshorne, *Algebraic Geometry*, III.11, final Artin–Rees step in the proof of Theorem 11.1
(p. 279).

Let `A` be a Noetherian ring, `a` an ideal of `A`, `E` a finite `A`-module and `R` a submodule
of `E`. For every `n` put `K n = (R ∩ a ^ (n + 1) E) / a ^ (n + 1) R`. Inclusions of submodules
make `K` a sequential inverse system of abelian groups. By the Artin–Rees lemma, for every `n`
there is `n' ≥ n` such that the transition map `K n' → K n` is zero; consequently the inverse
limit of the system, represented by its compatible sections, is trivial.

The index `n'` can be chosen once for all localizations of the data at multiplicative subsets of
`A`, since localization commutes with intersections and with products by powers of `a`. This is
the algebraic form of the uniformity of `n'` over the basic opens and stalks of an affine chart.

Stage `n` uses the power `a ^ (n + 1)`, following the natural-number indexing convention of the
project's inverse systems.
-/

noncomputable section

open CategoryTheory

namespace Hartshorne

namespace ArtinReesKernel

universe u v u' v'

variable {A : Type u} {E : Type v} [CommRing A] [AddCommGroup E] [Module A E]

/-- The numerator `R ∩ a ^ (n + 1) E` of the `n`-th Artin–Rees kernel. -/
def numerator (a : Ideal A) (R : Submodule A E) (n : ℕ) : Submodule A E :=
  R ⊓ a ^ (n + 1) • (⊤ : Submodule A E)

/-- The denominator `a ^ (n + 1) R`, viewed as a submodule of the numerator. -/
def denominator (a : Ideal A) (R : Submodule A E) (n : ℕ) :
    Submodule A (numerator a R n) :=
  (a ^ (n + 1) • R).comap (numerator a R n).subtype

/-- The `n`-th Artin–Rees kernel `K n = (R ∩ a ^ (n + 1) E) / a ^ (n + 1) R`. -/
abbrev Kernel (a : Ideal A) (R : Submodule A E) (n : ℕ) : Type v :=
  numerator a R n ⧸ denominator a R n

lemma numerator_antitone (a : Ideal A) (R : Submodule A E) {n m : ℕ} (h : n ≤ m) :
    numerator a R m ≤ numerator a R n :=
  inf_le_inf_left R
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.succ_le_succ h)))

/-- The inclusion `R ∩ a ^ (m + 1) E ⊆ R ∩ a ^ (n + 1) E` for `n ≤ m`. -/
def numeratorInclusion (a : Ideal A) (R : Submodule A E) {n m : ℕ} (h : n ≤ m) :
    numerator a R m →ₗ[A] numerator a R n :=
  Submodule.inclusion (numerator_antitone a R h)

@[simp]
lemma coe_numeratorInclusion (a : Ideal A) (R : Submodule A E) {n m : ℕ} (h : n ≤ m)
    (x : numerator a R m) :
    (numeratorInclusion a R h x : E) = x :=
  Submodule.coe_inclusion (numerator_antitone a R h) x

lemma numeratorInclusion_trans (a : Ideal A) (R : Submodule A E) {n m k : ℕ} (hnm : n ≤ m)
    (hmk : m ≤ k) :
    numeratorInclusion a R (hnm.trans hmk) =
      numeratorInclusion a R hnm ∘ₗ numeratorInclusion a R hmk :=
  LinearMap.ext fun x => Subtype.ext (by simp)

lemma denominator_le_comap (a : Ideal A) (R : Submodule A E) {n m : ℕ} (h : n ≤ m) :
    denominator a R m ≤ (denominator a R n).comap (numeratorInclusion a R h) := by
  intro x hx
  rw [denominator, Submodule.mem_comap, Submodule.subtype_apply] at hx
  rw [Submodule.mem_comap, denominator, Submodule.mem_comap, Submodule.subtype_apply,
    coe_numeratorInclusion]
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) hx

/-- The transition map `K m → K n` for `n ≤ m`, induced by inclusion of submodules. -/
def transition (a : Ideal A) (R : Submodule A E) {n m : ℕ} (h : n ≤ m) :
    Kernel a R m →ₗ[A] Kernel a R n :=
  (denominator a R m).mapQ (denominator a R n) (numeratorInclusion a R h)
    (denominator_le_comap a R h)

@[simp]
lemma transition_mk (a : Ideal A) (R : Submodule A E) {n m : ℕ} (h : n ≤ m)
    (x : numerator a R m) :
    transition a R h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (numeratorInclusion a R h x) :=
  rfl

lemma transition_refl (a : Ideal A) (R : Submodule A E) (n : ℕ) :
    transition a R (le_refl n) = LinearMap.id := by
  ext x
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

lemma transition_trans (a : Ideal A) (R : Submodule A E) {n m k : ℕ} (hnm : n ≤ m)
    (hmk : m ≤ k) :
    transition a R (hnm.trans hmk) = transition a R hnm ∘ₗ transition a R hmk := by
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, transition_mk]
  rw [numeratorInclusion_trans, LinearMap.comp_apply]

/-- The Artin–Rees kernels `K n = (R ∩ a ^ (n + 1) E) / a ^ (n + 1) R` as a sequential inverse
system of abelian groups, with transition maps induced by inclusion. -/
def system (a : Ideal A) (R : Submodule A E) : ℕᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj n := AddCommGrpCat.of (Kernel a R n.unop)
  map f := AddCommGrpCat.ofHom (transition a R (leOfHom f.unop)).toAddMonoidHom
  map_id n := by
    ext x
    exact LinearMap.congr_fun (transition_refl a R n.unop) x
  map_comp f g := by
    ext x
    exact LinearMap.congr_fun
      (transition_trans a R (leOfHom g.unop) (leOfHom f.unop)) x

lemma system_map_apply (a : Ideal A) (R : Submodule A E) {i j : ℕᵒᵖ} (f : i ⟶ j)
    (x : Kernel a R i.unop) :
    (system a R).map f x = transition a R (leOfHom f.unop) x :=
  rfl

/-- The transition map `K m → K n` vanishes exactly when `R ∩ a ^ (m + 1) E ⊆ a ^ (n + 1) R`. -/
lemma transition_eq_zero_iff (a : Ideal A) (R : Submodule A E) {n m : ℕ} (h : n ≤ m) :
    transition a R h = 0 ↔ numerator a R m ≤ a ^ (n + 1) • R := by
  constructor
  · intro hz x hx
    have := LinearMap.congr_fun hz (Submodule.Quotient.mk ⟨x, hx⟩)
    rw [transition_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, denominator,
      Submodule.mem_comap, Submodule.subtype_apply, coe_numeratorInclusion] at this
    exact this
  · intro hle
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, transition_mk, LinearMap.zero_comp,
      LinearMap.zero_apply]
    rw [Submodule.Quotient.mk_eq_zero, denominator, Submodule.mem_comap,
      Submodule.subtype_apply, coe_numeratorInclusion]
    exact hle x.2

section Localization

variable {A' : Type u'} {E' : Type v'} [CommRing A'] [Algebra A A'] (p : Submonoid A)
  [IsLocalization p A'] [AddCommGroup E'] [Module A E'] [Module A' E'] [IsScalarTower A A' E']
  (f : E →ₗ[A] E') [IsLocalizedModule p f]

/-- Localization commutes with the product of a submodule by a power of an ideal. -/
lemma localized'_pow_smul (a : Ideal A) (N : Submodule A E) (k : ℕ) :
    (a ^ k • N).localized' A' p f = a.map (algebraMap A A') ^ k • N.localized' A' p f := by
  rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Ideal.map_pow]

/-- The localization of the numerator `R ∩ a ^ (n + 1) E` is the numerator of the localized
data. -/
lemma localized'_numerator (a : Ideal A) (R : Submodule A E) (n : ℕ) :
    (numerator a R n).localized' A' p f =
      numerator (a.map (algebraMap A A')) (R.localized' A' p f) n := by
  rw [numerator, numerator, Submodule.localized'_inf, localized'_pow_smul,
    Submodule.localized'_top]

end Localization

variable [IsNoetherianRing A] [Module.Finite A E]

/-- Artin–Rees for the kernel system: for every `n` there is `n' ≥ n` with
`R ∩ a ^ (n' + 1) E ⊆ a ^ (n + 1) R`, so that the transition map `K n' → K n` is zero. -/
theorem exists_transition_eq_zero (a : Ideal A) (R : Submodule A E) (n : ℕ) :
    ∃ (n' : ℕ) (h : n ≤ n'), transition a R h = 0 := by
  obtain ⟨k, hk, hle⟩ := artinRees_inducedTopology a R (n + 1)
  obtain ⟨n', rfl⟩ : ∃ n', k = n' + 1 := ⟨k - 1, by omega⟩
  refine ⟨n', by omega, ?_⟩
  ext x
  change Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero, denominator, Submodule.mem_comap,
    Submodule.subtype_apply, coe_numeratorInclusion]
  exact hle x.2

/-- **The Artin–Rees kernel system is pro-zero** (Hartshorne III.11, proof of Theorem 11.1,
p. 279). Let `A` be Noetherian, `a` an ideal, `E` a finite `A`-module and `R ⊆ E` a submodule,
and let `K n = (R ∩ a ^ (n + 1) E) / a ^ (n + 1) R`. For every `n` there is `n' ≥ n` such that
the transition map `K n' → K n` of the inverse system is zero. -/
theorem system_isProZero (a : Ideal A) (R : Submodule A E) (n : ℕ) :
    ∃ (n' : ℕ) (h : n ≤ n'),
      (system a R).map (homOfLE h).op = 0 := by
  obtain ⟨n', h, hzero⟩ := exists_transition_eq_zero a R n
  refine ⟨n', h, ?_⟩
  ext x
  change transition a R h x = 0
  rw [hzero]
  rfl

/-- **The inverse limit of the Artin–Rees kernel system vanishes.** Every compatible section of
the inverse system `K n = (R ∩ a ^ (n + 1) E) / a ^ (n + 1) R` is zero, so `lim K n = 0`. -/
theorem system_sections_eq_zero (a : Ideal A) (R : Submodule A E)
    (s : (system a R ⋙ forget AddCommGrpCat).sections) (j : ℕᵒᵖ) :
    s.1 j = (0 : (system a R).obj j) := by
  obtain ⟨n', h, hzero⟩ := system_isProZero a R j.unop
  have hs := s.2 (homOfLE h).op
  change (system a R).map (homOfLE h).op (s.1 (Opposite.op n')) = s.1 j at hs
  rw [← hs, hzero]
  simp

/-- The inverse limit of the Artin–Rees kernel system, represented by compatible sections, has
exactly one element. -/
theorem system_sections_subsingleton (a : Ideal A) (R : Submodule A E) :
    Subsingleton (system a R ⋙ forget AddCommGrpCat).sections :=
  ⟨fun s t => Subtype.ext (funext fun j =>
    (system_sections_eq_zero a R s j).trans (system_sections_eq_zero a R t j).symm)⟩

/-- **Uniformity under localization.** For every `n` there is `n' ≥ n` such that, after
localizing `A`, `E`, `R` and `a` at any multiplicative subset of `A`, the transition map
`K n' → K n` of the localized Artin–Rees kernel system is zero. -/
theorem exists_transition_localized_eq_zero (a : Ideal A) (R : Submodule A E) (n : ℕ) :
    ∃ (n' : ℕ) (h : n ≤ n'), ∀ (p : Submonoid A) (A' : Type u') [CommRing A'] [Algebra A A']
      [IsLocalization p A'] (E' : Type v') [AddCommGroup E'] [Module A E'] [Module A' E']
      [IsScalarTower A A' E'] (f : E →ₗ[A] E') [IsLocalizedModule p f],
      transition (a.map (algebraMap A A')) (R.localized' A' p f) h = 0 := by
  obtain ⟨n', h, hz⟩ := exists_transition_eq_zero a R n
  refine ⟨n', h, fun p A' _ _ _ E' _ _ _ _ f _ => ?_⟩
  rw [transition_eq_zero_iff] at hz ⊢
  rw [← localized'_numerator, ← localized'_pow_smul]
  exact (Submodule.localized'gi A' p f).gc.monotone_l hz

end ArtinReesKernel

end Hartshorne
