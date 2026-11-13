/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LinearSystem
import Hartshorne.Scheme.SeparatesPointsTangentVectors

/-!
# Base-point-freeness and global generation

Hartshorne, *Algebraic Geometry*, II, Lemma 7.8 and Remarks 7.8.1–7.8.2 (p. 158).

Let `X` be a scheme over a field `k` (structure morphism `q`), `L` an invertible sheaf on `X` and
`𝔡` a linear system of `L`, given by a finite-dimensional subspace `V ⊆ Γ(X, L)`.

## Main definitions and results

* `LinearSystem.IsBasePointFree`: `𝔡` has no base points.
* `LinearSystem.isBasePoint_iff_forall_germ_mem`,
  `LinearSystem.forall_mem_support_iff_forall_germ_mem`: Lemma 7.8, first part: `x` is a base
  point exactly when `s_x ∈ 𝔪_x L_x` for every `s ∈ V` (in the second form, with Hartshorne's
  definition of base points through the divisors of the system, on an integral scheme).
* `LinearSystem.isBasePointFree_iff_isGeneratedBySections`: Lemma 7.8, second part: `𝔡` is
  base-point-free exactly when the sections in `V` generate `L`.
* `LinearSystem.isBasePointFree_iff_isGeneratedBySections_of_span_eq`: the same for a spanning
  family `s₀, …, sₙ` of `V` (for instance a basis).
* `LinearSystem.existsUnique_morphism_of_isBasePointFree`, `LinearSystem.morphism`: Remark 7.8.1:
  a base-point-free `𝔡` with a family `s₀, …, sₙ` spanning `V`
  determines a unique `k`-morphism `φ : X ⟶ ℙⁿ_k` with `φ^* 𝒪(1) ≅ L` carrying `φ^* xᵢ` to `sᵢ`
  (Theorem 7.1). Conversely the coordinate sections `φ^* xᵢ` of any `φ : X ⟶ ℙⁿ_k` span a
  base-point-free linear system of `φ^* 𝒪(1)` (`LinearSystem.isBasePointFree_ofFamily_pullback`).
* `LinearSystem.isClosedImmersion_morphism_iff`: Proposition 7.3, in its section form, for the
  morphism of Remark 7.8.1: for `X` projective over an algebraically closed field, this morphism
  is a closed immersion exactly when `V` separates points and tangent vectors. Remark 7.8.2
  rephrases this criterion in terms of the divisors of `𝔡`.

## Proof

A family of global sections of an invertible sheaf generates it exactly when at every point one
of them does not vanish: a nonvanishing section trivializes `L` near the point, and conversely
if all of them vanish at `x` their germs span a submodule of `𝔪_x L_x ≠ L_x`, the stalk being
free of rank one on the germ of a local trivializing section. A combination `∑ aᵢ sᵢ` vanishes
wherever all the `sᵢ` vanish, so the base points of `V` are the common zeros of a spanning
family.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

section Generation

variable {X : Scheme.{u}} {L : X.Modules}

/-- The germ of a local trivializing section of `L` at `x` does not lie in `𝔪_x L_x`. -/
private theorem germ_notMem_maximalIdeal_smul_top {U : X.Opens} {e : Γ(L, U)}
    (he : IsTrivializingSection L U e) {x : X} (hx : x ∈ U) :
    L.presheaf.germ U x hx e ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) := by
  intro hmem
  have htop : (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) =
      Submodule.span (X.presheaf.stalk x) {L.presheaf.germ U x hx e} := by
    refine (Submodule.eq_top_iff'.mpr fun z => ?_).symm
    obtain ⟨b, rfl⟩ := he.exists_smul_germ_eq hx z
    exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self _)
  rw [htop, Submodule.mem_smul_span_singleton] at hmem
  obtain ⟨c, hc, hce⟩ := hmem
  have hsub : (c - 1) • L.presheaf.germ U x hx e = 0 := by
    rw [sub_smul, hce, one_smul, sub_self]
  have hc1 := sub_eq_zero.mp (he.eq_zero_of_smul_germ_eq_zero hx _ hsub)
  exact (IsLocalRing.mem_maximalIdeal _).mp (hc1 ▸ hc) isUnit_one

/-- A family of global sections of an invertible sheaf generates it exactly when at every point
one of the sections does not vanish. -/
private theorem isGeneratedBySections_iff_forall_exists_mem_nonvanishingLocus
    (hL : L.IsInvertible) {ι : Type u} (t : ι → Γ(L, ⊤)) :
    L.IsGeneratedBySections t ↔ ∀ x, ∃ i, x ∈ nonvanishingLocus L (t i) := by
  constructor
  · intro hgen x
    by_contra hno
    push Not at hno
    have hle : Submodule.span (X.presheaf.stalk x)
        (Set.range fun i => L.presheaf.germ ⊤ x trivial (t i)) ≤
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
            (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact not_not.mp (hno i)
    obtain ⟨U, e, hxU, he⟩ := exists_isTrivializingSection hL x
    exact germ_notMem_maximalIdeal_smul_top he hxU (hle (hgen x ▸ Submodule.mem_top))
  · intro h
    refine isGeneratedBySections_of_forall_isTrivializingSection t fun x => ?_
    obtain ⟨i, hi⟩ := h x
    exact ⟨i, nonvanishingLocusOpens hL (t i), hi,
      isTrivializingSection_nonvanishingLocusOpens hL (t i)⟩

end Generation

namespace LinearSystem

variable {k : Type u} [Field k] {X : Scheme.{u}} {q : X ⟶ Spec (.of k)} {L : X.Modules}

/-- A linear system is **base-point-free** (Hartshorne II.7, p.158) if it has no base points. -/
def IsBasePointFree (𝔡 : LinearSystem q L) : Prop :=
  ∀ x, ¬ 𝔡.IsBasePoint x

/-- **Hartshorne II, Lemma 7.8, first part.** A point `x` is a base point of `𝔡` exactly when
`s_x ∈ 𝔪_x L_x` for every section `s` of `V`. (Base points are defined by this criterion here;
see `LinearSystem.forall_mem_support_iff_forall_germ_mem` for Hartshorne's definition.) -/
theorem isBasePoint_iff_forall_germ_mem (𝔡 : LinearSystem q L) (x : X) :
    𝔡.IsBasePoint x ↔ ∀ s ∈ 𝔡.sections,
      L.presheaf.germ ⊤ x trivial (toSection s) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
          (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) :=
  forall₂_congr fun s _ => (germ_mem_maximalIdeal_smul_top_iff (toSection s) x).symm

/-- **Hartshorne II, Lemma 7.8, first part, with Hartshorne's definition of base points.** On an
integral scheme, a point lies in the support of every divisor of `𝔡` exactly when `s_x ∈ 𝔪_x L_x`
for every section `s` of `V`. (Hartshorne works on a nonsingular projective variety over an
algebraically closed field; only integrality is used.) -/
theorem forall_mem_support_iff_forall_germ_mem [IsIntegral X] (𝔡 : LinearSystem q L) (x : X) :
    (∀ D ∈ 𝔡.divisors, ∀ hD : D.IsEffective,
        x ∈ (Scheme.CartierDivisor.idealSheafData hD).support) ↔
      ∀ s ∈ 𝔡.sections,
        L.presheaf.germ ⊤ x trivial (toSection s) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
            (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) :=
  (𝔡.isBasePoint_iff x).symm.trans (𝔡.isBasePoint_iff_forall_germ_mem x)

/-- **Hartshorne II, Lemma 7.8, second part.** A linear system `𝔡` with subspace `V` is
base-point-free exactly when `L` is generated by the global sections in `V`. (Hartshorne works on
a nonsingular projective variety over an algebraically closed field; this holds on any scheme over
a field.) -/
theorem isBasePointFree_iff_isGeneratedBySections (𝔡 : LinearSystem q L) :
    𝔡.IsBasePointFree ↔
      L.IsGeneratedBySections
        (fun s : 𝔡.sections => toSection (s : globalSectionsOverField q L)) := by
  rw [isGeneratedBySections_iff_forall_exists_mem_nonvanishingLocus 𝔡.isInvertible]
  simp only [IsBasePointFree, IsBasePoint, not_forall, not_not, Subtype.exists, exists_prop]

/-- If `s₀, …, sₙ` span `V`, the base points of `𝔡` are the common zeros of the `sᵢ`. -/
theorem isBasePoint_iff_of_span_eq (𝔡 : LinearSystem q L) {n : ℕ}
    (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections) (x : X) :
    𝔡.IsBasePoint x ↔ ∀ i, x ∉ nonvanishingLocus L (toSection (s i)) := by
  constructor
  · intro h i
    exact h (s i) (hs ▸ Submodule.subset_span ⟨i, rfl⟩)
  · intro h t ht hx
    rw [← hs] at ht
    obtain ⟨a, ha⟩ := (mem_ofFamily_sections_iff 𝔡.isInvertible s t).mp ht
    rw [← ha] at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (nonvanishingLocus_linearSystemSection_subset q _ a hx)
    exact h i hi

/-- **Hartshorne II, Lemma 7.8, for a spanning family.** If `s₀, …, sₙ` span `V` (for instance a
basis of `V`), then `𝔡` is base-point-free exactly when `s₀, …, sₙ` generate `L`. -/
theorem isBasePointFree_iff_isGeneratedBySections_of_span_eq (𝔡 : LinearSystem q L) {n : ℕ}
    (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections) :
    𝔡.IsBasePointFree ↔
      L.IsGeneratedBySections (fun i : ULift.{u} (Fin (n + 1)) => toSection (s i.down)) := by
  rw [isGeneratedBySections_iff_forall_exists_mem_nonvanishingLocus 𝔡.isInvertible]
  simp only [IsBasePointFree, 𝔡.isBasePoint_iff_of_span_eq s hs, not_forall, not_not,
    ULift.exists]

/-- **Hartshorne II, Remark 7.8.1.** A base-point-free linear system `𝔡` together with a family
`s₀, …, sₙ` spanning its subspace `V` determines a unique
`k`-morphism `φ : X ⟶ ℙⁿ_k` with an isomorphism `φ^* 𝒪(1) ≅ L` carrying each `φ^* xᵢ` to `sᵢ`
(Theorem 7.1). -/
theorem existsUnique_morphism_of_isBasePointFree (𝔡 : LinearSystem q L)
    (h𝔡 : 𝔡.IsBasePointFree) {n : ℕ} (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections) :
    ∃! φ : X ⟶ projectiveSpaceOverScheme n (Spec (.of k)),
      φ ≫ projectiveSpaceOverSchemeProjection n _ = q ∧
      ∃ e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) =
          toSection (s i) :=
  existsUnique_morphism_of_isGeneratedBySections q 𝔡.isInvertible (fun i => toSection (s i))
    ((𝔡.isBasePointFree_iff_isGeneratedBySections_of_span_eq s hs).mp h𝔡)

/-- **The morphism determined by a base-point-free linear system** and a family
`s₀, …, sₙ` spanning its subspace (Hartshorne II, Remark 7.8.1). -/
def morphism (𝔡 : LinearSystem q L) (h𝔡 : 𝔡.IsBasePointFree) {n : ℕ}
    (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections) :
    X ⟶ projectiveSpaceOverScheme n (Spec (.of k)) :=
  (𝔡.existsUnique_morphism_of_isBasePointFree h𝔡 s hs).exists.choose

/-- The defining property of `LinearSystem.morphism`. -/
theorem morphism_spec (𝔡 : LinearSystem q L) (h𝔡 : 𝔡.IsBasePointFree) {n : ℕ}
    (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections) :
    𝔡.morphism h𝔡 s hs ≫ projectiveSpaceOverSchemeProjection n _ = q ∧
      ∃ e : (Scheme.Modules.pullback (𝔡.morphism h𝔡 s hs)).obj
          (projectiveSpaceTwistingSheaf n _ 1) ≅ L,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection (𝔡.morphism h𝔡 s hs)
          (projectiveSpaceCoordinate n _ i)) = toSection (s i) :=
  (𝔡.existsUnique_morphism_of_isBasePointFree h𝔡 s hs).exists.choose_spec

/-- **Hartshorne II, Remark 7.8.1, converse.** For a `k`-morphism `φ : X ⟶ ℙⁿ_k`, the coordinate
sections `φ^* x₀, …, φ^* xₙ` span a base-point-free linear system of `φ^* 𝒪(1)`. -/
theorem isBasePointFree_ofFamily_pullback {n : ℕ}
    (φ : X ⟶ projectiveSpaceOverScheme n (Spec (.of k))) :
    IsBasePointFree (ofFamily (q := φ ≫ projectiveSpaceOverSchemeProjection n _)
      (isInvertible_pullback_projectiveSpaceTwistingSheaf φ)
      (fun i => (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i) :
        globalSectionsOverField (φ ≫ projectiveSpaceOverSchemeProjection n _)
          ((Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1))))) := by
  rw [isBasePointFree_iff_isGeneratedBySections_of_span_eq _ _ rfl]
  exact isGeneratedBySections_pullback_projectiveSpaceCoordinate φ

/-- The subspace spanned by `s₀, …, sₙ`, as a set of global sections, is the set of combinations
`∑ aᵢ sᵢ`. -/
private theorem image_toSection_eq_linearSystem (𝔡 : LinearSystem q L) {n : ℕ}
    (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections) :
    toSection '' (𝔡.sections : Set (globalSectionsOverField q L)) =
      linearSystem q (fun i => toSection (s i)) := by
  ext t
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, ← hs] at ht
    exact (mem_ofFamily_sections_iff 𝔡.isInvertible s t).mp ht
  · intro ht
    refine ⟨show globalSectionsOverField q L from t, ?_, rfl⟩
    change _ ∈ 𝔡.sections
    rw [← hs]
    exact (mem_ofFamily_sections_iff 𝔡.isInvertible s t).mpr ht

/-- **Hartshorne II, Proposition 7.3 (section form), for any morphism defined by a spanning
family** (the section form of the criterion Remark 7.8.2 states with divisors). Let `X` be
projective over an algebraically closed field `k`, let `s₀, …, sₙ` span the subspace `V` of a
linear system `𝔡`, and let `φ : X ⟶ ℙⁿ_k` come with an isomorphism `φ^* 𝒪(1) ≅ L` carrying each
`φ^* xᵢ` to `sᵢ`. Then `φ` is a closed immersion exactly when `V` separates points and tangent
vectors (Proposition 7.3). -/
theorem isClosedImmersion_iff_of_span_eq [IsAlgClosed k] (hX : Projective q)
    (𝔡 : LinearSystem q L) {n : ℕ} (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections)
    (φ : X ⟶ projectiveSpaceOverScheme n (Spec (.of k)))
    (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
    (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
    (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) =
      toSection (s i)) :
    IsClosedImmersion φ ↔
      SectionsSeparatePoints (toSection '' (𝔡.sections : Set (globalSectionsOverField q L))) ∧
        SectionsSeparateTangentVectors q
          (toSection '' (𝔡.sections : Set (globalSectionsOverField q L))) := by
  rw [𝔡.image_toSection_eq_linearSystem s hs]
  exact isClosedImmersion_iff_sectionsSeparatePoints_and_sectionsSeparateTangentVectors q
    𝔡.isInvertible _ φ hφ e he hX

/-- **Hartshorne II, Proposition 7.3 (section form), for the morphism of Remark 7.8.1.** Let `X`
be projective over an algebraically closed field `k` and `𝔡` a base-point-free linear system with a
family `s₀, …, sₙ` spanning its subspace `V`. The morphism `φ : X ⟶ ℙⁿ_k` it determines
(Remark 7.8.1) is a closed immersion exactly when the sections in `V` separate points and tangent
vectors in the sense of Proposition 7.3. Remark 7.8.2 rephrases this criterion in terms of the
divisors of `𝔡` (`P ∈ Supp D`, `Q ∉ Supp D`, `t ∉ T_P(D)`); that divisor form is not stated here.
(Hartshorne's `X` there is a nonsingular projective variety over an algebraically closed field,
p. 156.) -/
theorem isClosedImmersion_morphism_iff [IsAlgClosed k] (hX : Projective q)
    (𝔡 : LinearSystem q L) (h𝔡 : 𝔡.IsBasePointFree) {n : ℕ}
    (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections) :
    IsClosedImmersion (𝔡.morphism h𝔡 s hs) ↔
      SectionsSeparatePoints (toSection '' (𝔡.sections : Set (globalSectionsOverField q L))) ∧
        SectionsSeparateTangentVectors q
          (toSection '' (𝔡.sections : Set (globalSectionsOverField q L))) := by
  obtain ⟨hφ, e, he⟩ := 𝔡.morphism_spec h𝔡 s hs
  exact isClosedImmersion_iff_of_span_eq hX 𝔡 s hs _ hφ e he

end LinearSystem

end Hartshorne
