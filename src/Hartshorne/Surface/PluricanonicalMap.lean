/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LinearSystemRationalMap
import Hartshorne.Scheme.AmpleSectionsAffineBasis
import Hartshorne.Surface.CanonicalSectionRing

/-!
# Pluricanonical rational maps and the dimensions of their images

Hartshorne, *Algebraic Geometry*, V.6, pluricanonical maps (pp. 421–422).

Let `X` be an integral scheme, projective over a field `k` (structure morphism `f`), whose
canonical sheaf `ω_X` is invertible, for instance a nonsingular projective variety. For `n ≥ 0`
let `|nK|` be the complete linear system of `ω_X^{⊗ n}`, with space of sections
`H⁰(X, ω_X^{⊗ n})`, the degree-`n` part of the canonical section ring.

## Conventions

The projective space `P(H⁰(X, ω_X^{⊗ n}))` is identified with `ℙᴺ_k`, `N + 1 = dim H⁰`, through a
basis `s₀, …, s_N` of `H⁰(X, ω_X^{⊗ n})` (`pluricanonicalBasis`, chosen once and for all): the
morphism defined by the `sᵢ` is the one with `xᵢ ↦ sᵢ`, i.e. the sections define a surjection
`𝒪ᴺ⁺¹ → ω_X^{⊗ n}` off the base locus (Theorem II.7.1). Another basis changes the map by a
linear automorphism of `ℙᴺ_k` (not formalized). The constructions are made for every `n`; the
case of interest is `n > 0`.

## Main definitions and results

* `pluricanonicalSheaf f n = ω_X^{⊗ n}` and `pluricanonicalSystem f hf hω n = |nK|`.
* `pluricanonicalMap f hf hω n h : X ⇢ ℙᴺ_k`, for `H⁰(X, ω_X^{⊗ n}) ≠ 0`: the pluricanonical
  rational map `φ_n`, represented by the morphism defined by the basis on the complement
  `pluricanonicalDomain` of the base locus of `|nK|` (`mem_pluricanonicalDomain_iff`).
* `pluricanonicalImage`: the image `\overline{φ_n(X - B)}`, a closed subset of `ℙᴺ_k`, and
  `pluricanonicalImageDim`: its dimension.
* **Empty systems.** If `H⁰(X, ω_X^{⊗ n}) = 0` then `|nK|` has no divisors and dimension `-1`
  (`pluricanonicalSystem_divisors_eq_empty_iff`, `pluricanonicalSystem_dim_eq_neg_one_iff`);
  no map is defined in that case.
* **One-dimensional systems.** If `dim H⁰(X, ω_X^{⊗ n}) = 1` the image has dimension `0`
  (`pluricanonicalImageDim_eq_zero`).
* **Removing a fixed part.** If the basis sections are `sᵢ = m(s'ᵢ)` for a morphism
  `m : L' ⟶ ω_X^{⊗ n}` from an invertible sheaf (for instance multiplication by a section whose
  divisor of zeros is a fixed part `F` of `|nK|`, so `L' = 𝒪(nK - F)`), the rational map and the
  image are those defined by the `s'ᵢ` (`pluricanonicalMap_eq_of_fixedPart`,
  `pluricanonicalImage_eq_of_fixedPart`).
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **The pluricanonical sheaf** `ω_X^{⊗ n}`, the `n`-th tensor power of the canonical sheaf. -/
abbrev pluricanonicalSheaf (n : ℕ) : X.Modules :=
  moduleSheafTensorPower (R := X.sheaf) n (canonicalSheaf f)

variable (hf : Projective f) (hω : (canonicalSheaf f).IsInvertible)

include hω in
/-- `ω_X^{⊗ n}` is invertible when `ω_X` is. -/
theorem isInvertible_pluricanonicalSheaf (n : ℕ) : (pluricanonicalSheaf f n).IsInvertible :=
  isInvertible_moduleSheafTensorPower hω n

/-- **The pluricanonical system** `|nK|`: the complete linear system of `ω_X^{⊗ n}`, whose space
of sections is `H⁰(X, ω_X^{⊗ n})`. -/
def pluricanonicalSystem (n : ℕ) : LinearSystem f (pluricanonicalSheaf f n) :=
  LinearSystem.complete hf (isInvertible_pluricanonicalSheaf f hω n)

include hf hω in
/-- `H⁰(X, ω_X^{⊗ n})` is finite-dimensional over `k`. -/
theorem finiteDimensional_pluricanonical (n : ℕ) :
    FiniteDimensional k (globalSectionsOverField f (pluricanonicalSheaf f n)) :=
  have : FiniteDimensional k (⊤ : Submodule k
      (globalSectionsOverField f (pluricanonicalSheaf f n))) :=
    (pluricanonicalSystem f hf hω n).finiteDimensional
  LinearEquiv.finiteDimensional (Submodule.topEquiv (R := k))

/-- The projective dimension `N = dim_k H⁰(X, ω_X^{⊗ n}) - 1` of `P(H⁰(X, ω_X^{⊗ n})) ≅ ℙᴺ_k`. -/
abbrev pluricanonicalProjDim (n : ℕ) : ℕ :=
  Module.finrank k (globalSectionsOverField f (pluricanonicalSheaf f n)) - 1

/-- **A basis of `H⁰(X, ω_X^{⊗ n})`**, when this space is nonzero: it identifies
`P(H⁰(X, ω_X^{⊗ n}))` with `ℙᴺ_k`. -/
def pluricanonicalBasis (n : ℕ) (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) :
    Module.Basis (Fin (pluricanonicalProjDim f n + 1)) k
      (globalSectionsOverField f (pluricanonicalSheaf f n)) :=
  have := finiteDimensional_pluricanonical f hf hω n
  have : Nontrivial (globalSectionsOverField f (pluricanonicalSheaf f n)) :=
    ⟨h.choose, 0, h.choose_spec⟩
  Module.finBasisOfFinrankEq k _ (Nat.sub_add_cancel Module.finrank_pos).symm

/-- The basis sections `s₀, …, s_N` of `ω_X^{⊗ n}`. -/
abbrev pluricanonicalSections (n : ℕ) (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) :
    Fin (pluricanonicalProjDim f n + 1) → Γ(pluricanonicalSheaf f n, ⊤) :=
  fun i => LinearSystem.toSection (pluricanonicalBasis f hf hω n h i)

/-- The basis sections span `H⁰(X, ω_X^{⊗ n})`, the space of sections of `|nK|`. -/
theorem span_pluricanonicalBasis (n : ℕ) (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) :
    Submodule.span k (Set.range (pluricanonicalBasis f hf hω n h)) =
      (pluricanonicalSystem f hf hω n).sections :=
  (pluricanonicalBasis f hf hω n h).span_eq

/-- The basis sections are not all zero. -/
theorem pluricanonicalSections_ne_zero (n : ℕ)
    (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) :
    pluricanonicalSections f hf hω n h ≠ 0 :=
  LinearSystem.toSection_ne_zero_of_span_eq _ _ (span_pluricanonicalBasis f hf hω n h)
    (by
      rw [pluricanonicalSystem, LinearSystem.complete_sections]
      have : Nontrivial (globalSectionsOverField f (pluricanonicalSheaf f n)) :=
        ⟨h.choose, 0, h.choose_spec⟩
      exact bot_ne_top.symm)

/-- **The domain of `φ_n`**: the complement `X - B` of the base locus of `|nK|`, the open set on
which the basis sections generate `ω_X^{⊗ n}`. -/
def pluricanonicalDomain (n : ℕ) (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) :
    X.Opens :=
  linearSystemDomain (isInvertible_pluricanonicalSheaf f hω n) (pluricanonicalSections f hf hω n h)

/-- A point lies in the domain of `φ_n` exactly when it is not a base point of `|nK|`. -/
theorem mem_pluricanonicalDomain_iff (n : ℕ)
    (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) (x : X) :
    x ∈ pluricanonicalDomain f hf hω n h ↔ ¬ (pluricanonicalSystem f hf hω n).IsBasePoint x :=
  LinearSystem.mem_linearSystemDomain_iff_not_isBasePoint _ _
    (span_pluricanonicalBasis f hf hω n h) x

/-- **The pluricanonical rational map** `φ_n : X ⇢ P(H⁰(X, ω_X^{⊗ n})) ≅ ℙᴺ_k` (Hartshorne V.6,
pp. 421–422), for `H⁰(X, ω_X^{⊗ n}) ≠ 0` on an integral scheme: the class of the morphism
`X - B ⟶ ℙᴺ_k` defined by the basis sections on the complement of the base locus of `|nK|`. -/
def pluricanonicalMap [IsIntegral X] (n : ℕ)
    (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) :
    X ⤏ projectiveSpaceOverScheme (pluricanonicalProjDim f n) (Spec (CommRingCat.of k)) :=
  linearSystemRationalMap f (isInvertible_pluricanonicalSheaf f hω n)
    (pluricanonicalSections f hf hω n h) (pluricanonicalSections_ne_zero f hf hω n h)

/-- `φ_n` is represented by the morphism defined by the basis sections on the complement of the
base locus of `|nK|`. -/
theorem pluricanonicalMap_eq [IsIntegral X] (n : ℕ)
    (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) :
    pluricanonicalMap f hf hω n h =
      (linearSystemPartialMap f (isInvertible_pluricanonicalSheaf f hω n)
        (pluricanonicalSections f hf hω n h)
        (pluricanonicalSections_ne_zero f hf hω n h)).toRationalMap :=
  rfl

/-- **The image of `φ_n`**: the closure `\overline{φ_n(X - B)}` in `ℙᴺ_k` of the image of the
complement of the base locus of `|nK|`. -/
def pluricanonicalImage (n : ℕ) (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) :
    Closeds (projectiveSpaceOverScheme (pluricanonicalProjDim f n) (Spec (CommRingCat.of k))) :=
  linearSystemImage f (isInvertible_pluricanonicalSheaf f hω n)
    (pluricanonicalSections f hf hω n h)

/-- **The dimension of the image of `φ_n`**: the topological Krull dimension of
`\overline{φ_n(X - B)}`. -/
def pluricanonicalImageDim (n : ℕ) (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) :
    WithBot ℕ∞ :=
  linearSystemImageDim f (isInvertible_pluricanonicalSheaf f hω n)
    (pluricanonicalSections f hf hω n h)

/-- **An empty pluricanonical system.** On an integral scheme, `|nK|` has no divisors exactly
when `H⁰(X, ω_X^{⊗ n}) = 0`. -/
theorem pluricanonicalSystem_divisors_eq_empty_iff [IsIntegral X] (n : ℕ) :
    (pluricanonicalSystem f hf hω n).divisors = ∅ ↔
      ∀ s : CanonicalSectionRing.Component f n, s = 0 := by
  rw [LinearSystem.divisors_eq_empty_iff, pluricanonicalSystem, LinearSystem.complete_sections,
    Submodule.eq_bot_iff]
  exact ⟨fun h s => h s Submodule.mem_top, fun h s _ => h s⟩

/-- `|nK|` has dimension `-1` exactly when `H⁰(X, ω_X^{⊗ n}) = 0`. -/
theorem pluricanonicalSystem_dim_eq_neg_one_iff (n : ℕ) :
    (pluricanonicalSystem f hf hω n).dim = -1 ↔
      ∀ s : CanonicalSectionRing.Component f n, s = 0 := by
  rw [LinearSystem.dim_eq_neg_one_iff, pluricanonicalSystem, LinearSystem.complete_sections,
    Submodule.eq_bot_iff]
  exact ⟨fun h s => h s Submodule.mem_top, fun h s _ => h s⟩

/-- **A one-dimensional pluricanonical system has a zero-dimensional image.** If
`dim_k H⁰(X, ω_X^{⊗ n}) = 1` on an integral scheme, the image of `φ_n` has dimension `0`. -/
theorem pluricanonicalImageDim_eq_zero [IsIntegral X] (n : ℕ)
    (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0)
    (h1 : Module.finrank k (globalSectionsOverField f (pluricanonicalSheaf f n)) = 1) :
    pluricanonicalImageDim f hf hω n h = 0 := by
  have key : ∀ (N : ℕ), N = 0 → ∀ s : Fin (N + 1) → Γ(pluricanonicalSheaf f n, ⊤), s ≠ 0 →
      linearSystemImageDim f (isInvertible_pluricanonicalSheaf f hω n) s = 0 := by
    rintro N rfl s hs
    exact linearSystemImageDim_eq_zero f _ hs
  exact key _ (by rw [pluricanonicalProjDim, h1]) _ (pluricanonicalSections_ne_zero f hf hω n h)

/-- **Removing a fixed part does not change `φ_n`.** If the basis sections are `sᵢ = m(s'ᵢ)` for a
morphism `m : L' ⟶ ω_X^{⊗ n}` from an invertible sheaf `L'` (for instance multiplication by a
section whose divisor of zeros is a fixed part `F` of `|nK|`), then `φ_n` is the rational map
defined by the `s'ᵢ`. -/
theorem pluricanonicalMap_eq_of_fixedPart [IsIntegral X] (n : ℕ)
    (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) {L' : X.Modules}
    (hL' : L'.IsInvertible) (m : L' ⟶ pluricanonicalSheaf f n)
    (s' : Fin (pluricanonicalProjDim f n + 1) → Γ(L', ⊤))
    (hs' : ∀ i, m.app ⊤ (s' i) = pluricanonicalSections f hf hω n h i) (hs'0 : s' ≠ 0) :
    pluricanonicalMap f hf hω n h = linearSystemRationalMap f hL' s' hs'0 := by
  have he : pluricanonicalSections f hf hω n h = fun i => m.app ⊤ (s' i) := (funext hs').symm
  have hne : (fun i => m.app ⊤ (s' i)) ≠ 0 := he ▸ pluricanonicalSections_ne_zero f hf hω n h
  rw [← linearSystemRationalMap_map f (isInvertible_pluricanonicalSheaf f hω n) hL' m s' hne]
  exact linearSystemRationalMap_congr f _ he _ _

/-- **Removing a fixed part does not change the image of `φ_n`**: in the situation of
`pluricanonicalMap_eq_of_fixedPart`, the image of `φ_n` is the image of the map defined by the
`s'ᵢ`; in particular the two images have the same dimension. -/
theorem pluricanonicalImage_eq_of_fixedPart [IsIntegral X] (n : ℕ)
    (h : ∃ s : CanonicalSectionRing.Component f n, s ≠ 0) {L' : X.Modules}
    (hL' : L'.IsInvertible) (m : L' ⟶ pluricanonicalSheaf f n)
    (s' : Fin (pluricanonicalProjDim f n + 1) → Γ(L', ⊤))
    (hs' : ∀ i, m.app ⊤ (s' i) = pluricanonicalSections f hf hω n h i) :
    pluricanonicalImage f hf hω n h = linearSystemImage f hL' s' := by
  have he : pluricanonicalSections f hf hω n h = fun i => m.app ⊤ (s' i) := (funext hs').symm
  have hne : (fun i => m.app ⊤ (s' i)) ≠ 0 := he ▸ pluricanonicalSections_ne_zero f hf hω n h
  rw [pluricanonicalImage, he]
  exact linearSystemImage_map f _ hL' m s'
    (linearSystemDomain_nonempty (isInvertible_pluricanonicalSheaf f hω n) hne)

end Hartshorne
