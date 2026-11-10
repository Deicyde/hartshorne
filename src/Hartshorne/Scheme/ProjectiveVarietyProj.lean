/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VarietySchemeOverK
import Hartshorne.Rational.AffineOpenBasis
import Hartshorne.Projective.PointIdeal
import Hartshorne.Projective.AwayAtPrime
import Hartshorne.Topology.Subspace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Hartshorne.Scheme.TopIsoRestriction

/-!
# A projective variety completes to `Proj`

Hartshorne, *Algebraic Geometry*, II.2, Exercise 2.14(d) (p. 81), with
Example 2.5.1 (p. 77).

For a projective variety `Y ⊆ ℙⁿ` over an algebraically closed field `k`, with
homogeneous coordinate ring `S(Y)`, the scheme `t(Y)` associated to `Y` by
generic completion is canonically isomorphic to `Proj S(Y)`, compatibly with the
structure morphisms to `Spec k`.

## Reading of the statement

"Naturally isomorphic" is read as: there is a canonical isomorphism, given
explicitly on points (`Z ↦ I(Z)`, a classical point `x ↦ 𝔪_x`) and on sections
(evaluation of homogeneous fractions at classical points); these descriptions
are recorded as the `_hom_base`, `_hom_base_alpha` and `_hom_app` lemmas.
"Over `Spec k`" is read as compatibility with the structure morphisms: the
isomorphism composed with `Proj S(Y) → Spec S(Y)₀ → Spec k` is the structure
morphism of `t(Y)` given by the constant regular functions.

## Construction

Rather than gluing chart-wise isomorphisms `t(Y ∩ D(xᵢ)) ≅ D₊(xᵢ)` along double
overlaps, the isomorphism is built globally and directly, in parallel with the
affine comparison `t(Y) ≅ Spec A(Y)`.

* **Points.** An irreducible closed subset `Z ⊆ Y` goes to its ideal
  `I(Z) ⊆ S(Y)`, the intersection of the homogeneous primes `𝔪_x` for `x ∈ Z`;
  it is a relevant homogeneous prime. The inverse sends a relevant homogeneous
  prime `𝔭` to its zero set `{x | 𝔭 ⊆ 𝔪_x}`. That these are inverse uses the
  projective Nullstellensatz: a homogeneous element of positive degree vanishing
  on the zero set of `𝔭` has a power in `𝔭`, and the zero set is nonempty since
  `𝔭` does not contain every `xᵢ`. Closed sets correspond, so the bijection is a
  homeomorphism, and a classical point `x` goes to `𝔪_x`.
* **Sections.** Over an open `W ⊆ Proj S(Y)`, a section of the structure sheaf
  is sent to the function on the corresponding open of `Y` whose value at `x` is
  its value in `S(Y)_(𝔪_x)` evaluated at `x`, a homogeneous fraction `a / b`
  going to `a(x) / b(x)`. Locally the section is `a / b`, so the function is
  regular. Injectivity and surjectivity both come from the identity principle in
  `S(Y)`: a homogeneous element vanishing on a nonempty open subset of the
  irreducible `Y` is zero. For surjectivity a regular function is written as a
  quotient of homogeneous polynomials of equal degree near a classical point of
  the zero set of each prime, and these local quotients agree in every
  homogeneous localization.
* **Over `Spec k`.** The structure morphism of `Proj S(Y)` is
  `Proj S(Y) → Spec S(Y)₀ → Spec k`. A constant `c ∈ k` gives the global section
  `c / 1`, which evaluates to the constant function `c`; so the isomorphism
  intertwines the structure morphisms.

## Main definitions and results

* `Hartshorne.projIrreducibleClosedsEquiv`, `Hartshorne.projGenericCompletionHomeomorph`:
  the homeomorphism `t(Y) ≃ₜ Proj S(Y)`, `Z ↦ I(Z)`.
* `Hartshorne.projAtPrimeEval`: evaluation of a homogeneous fraction at a
  classical point.
* `Hartshorne.projToRegular`: evaluation of structure-sheaf sections at
  classical points, a ring isomorphism onto regular functions.
* `Hartshorne.projectiveVarietyAssociatedSchemeIsoProj`: the isomorphism of
  schemes `t(Y) ≅ Proj S(Y)`, with its description on points and sections.
* `Hartshorne.projCoordStructureMorphism`: the structure morphism
  `Proj S(Y) → Spec k`.
* `Hartshorne.projectiveVarietyAssociatedSchemeIsoProj_hom_comp_structureMorphism`:
  the isomorphism is compatible with the structure morphisms to `Spec k`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace MvPolynomial AlgebraicGeometry

namespace Hartshorne

universe u

variable {k : Type u} [Field k] {σ : Type u} {Y : Set (ProjectiveSpace k σ)}

/-! ### Evaluation and the ideals `𝔪_P` -/

/-- Evaluation of an element of `S(Y)` at the chosen representative of a point
of `Y`. -/
def projCoordEval (x : Y) : homogeneousCoordinateRing Y →+* k :=
  Ideal.Quotient.lift (homogeneousVanishingIdeal Y) (eval x.1.rep) fun _ hg =>
    eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal hg x.2

@[simp]
theorem projCoordEval_mk (x : Y) (g : MvPolynomial σ k) :
    projCoordEval x (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) g) = eval x.1.rep g :=
  rfl

theorem projCoordEval_algebraMap (x : Y) (c : k) :
    projCoordEval x (algebraMap k (homogeneousCoordinateRing Y) c) = c := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial σ k) (homogeneousCoordinateRing Y),
    Ideal.Quotient.algebraMap_eq, projCoordEval_mk]
  simp

/-! ### Ideals of subsets of `Y` and zero sets in `Y` -/

/-- The ideal `I(C) ⊆ S(Y)` of a subset `C ⊆ Y`: the elements lying in `𝔪_x`
for every `x ∈ C`. -/
def projIdealOf (C : Set Y) : Ideal (homogeneousCoordinateRing Y) :=
  ⨅ x ∈ C, projPointIdeal Y x.1

theorem mem_projIdealOf {C : Set Y} {a : homogeneousCoordinateRing Y} :
    a ∈ projIdealOf C ↔ ∀ x ∈ C, a ∈ projPointIdeal Y x.1 := by
  simp [projIdealOf, Submodule.mem_iInf]

/-- The zero set in `Y` of a subset `s ⊆ S(Y)`: the points `x` with `s ⊆ 𝔪_x`. -/
def projZeroSetIn (s : Set (homogeneousCoordinateRing Y)) : Set Y :=
  {x | s ⊆ projPointIdeal Y x.1}

theorem subset_projZeroSetIn_iff {C : Set Y} {s : Set (homogeneousCoordinateRing Y)} :
    C ⊆ projZeroSetIn s ↔ s ⊆ projIdealOf C := by
  constructor
  · intro h a ha
    exact mem_projIdealOf.2 fun x hx => h hx ha
  · intro h x hx a ha
    exact mem_projIdealOf.1 (h ha) x hx

theorem projIdealOf_anti {C D : Set Y} (h : C ⊆ D) : projIdealOf D ≤ projIdealOf C :=
  fun _ ha => mem_projIdealOf.2 fun x hx => mem_projIdealOf.1 ha x (h hx)

theorem projZeroSetIn_anti {s t : Set (homogeneousCoordinateRing Y)} (h : s ⊆ t) :
    projZeroSetIn t ⊆ projZeroSetIn s :=
  fun _ hx => h.trans hx

theorem projIdealOf_singleton (x : Y) : projIdealOf {x} = projPointIdeal Y x.1 := by
  ext a
  simp [mem_projIdealOf]

/-- A homogeneous element of `S(Y)` is the class of a homogeneous polynomial of
the same degree. -/
theorem exists_isHomogeneous_of_mem_projCoordGrading {n : ℕ}
    {a : homogeneousCoordinateRing Y} (ha : a ∈ projCoordGrading Y n) :
    ∃ g : MvPolynomial σ k, g.IsHomogeneous n ∧
      Ideal.Quotient.mk (homogeneousVanishingIdeal Y) g = a := by
  obtain ⟨g, hg, rfl⟩ := ha
  exact ⟨g, (mem_homogeneousSubmodule n g).1 hg, rfl⟩

theorem mk_mem_projCoordGrading {n : ℕ} {g : MvPolynomial σ k} (hg : g.IsHomogeneous n) :
    Ideal.Quotient.mk (homogeneousVanishingIdeal Y) g ∈ projCoordGrading Y n :=
  ⟨g, (mem_homogeneousSubmodule n g).2 hg, rfl⟩



/-- A homogeneous element of `S(Y)` lies in `𝔪_x` exactly when it vanishes at
`x`. -/
theorem mem_projPointIdeal_iff_eval {n : ℕ} {a : homogeneousCoordinateRing Y}
    (ha : a ∈ projCoordGrading Y n) (x : Y) :
    a ∈ projPointIdeal Y x.1 ↔ projCoordEval x a = 0 := by
  obtain ⟨g, hg, rfl⟩ := exists_isHomogeneous_of_mem_projCoordGrading ha
  rw [mem_projPointIdeal_iff x.2, mem_homogeneousVanishingIdeal_singleton_iff hg]
  rfl

/-- The locus where a homogeneous element of `S(Y)` lies in `𝔪_x` is closed. -/
theorem isClosed_setOf_mem_projPointIdeal {n : ℕ} {b : homogeneousCoordinateRing Y}
    (hb : b ∈ projCoordGrading Y n) :
    IsClosed {x : Y | b ∈ projPointIdeal Y x.1} := by
  obtain ⟨g, hg, rfl⟩ := exists_isHomogeneous_of_mem_projCoordGrading hb
  have heq : {x : Y | Ideal.Quotient.mk (homogeneousVanishingIdeal Y) g ∈ projPointIdeal Y x.1} =
      Subtype.val ⁻¹' projZeroSet {g} := by
    ext x
    rw [Set.mem_ofPred_eq, mem_projPointIdeal_iff_eval hb, projCoordEval_mk]
    simp [HomogeneousVanish]
  rw [heq]
  refine IsClosed.preimage continuous_subtype_val
    (isClosed_iff_isProjAlgebraicSet.2 ⟨{g}, ?_, rfl⟩)
  rintro f rfl
  exact ⟨n, hg⟩

theorem isHomogeneous_projIdealOf (C : Set Y) :
    (projIdealOf C).IsHomogeneous (projCoordGrading Y) :=
  Ideal.IsHomogeneous.iInf₂ fun _ _ => isHomogeneous_projPointIdeal

theorem isClosed_projZeroSetIn (s : Set (homogeneousCoordinateRing Y)) :
    IsClosed (projZeroSetIn s) := by
  have heq : projZeroSetIn s = ⋂ a ∈ s, ⋂ n : ℕ,
      {x : Y | (DirectSum.decompose (projCoordGrading Y) a n :
        homogeneousCoordinateRing Y) ∈ projPointIdeal Y x.1} := by
    ext x
    simp only [projZeroSetIn, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h a ha n
      exact (isHomogeneous_projPointIdeal (Y := Y) (P := x.1)).mem_iff.1 (h ha) n
    · intro h a ha
      exact (isHomogeneous_projPointIdeal (Y := Y) (P := x.1)).mem_iff.2 (h a ha)
  rw [heq]
  exact isClosed_biInter fun a _ => isClosed_iInter fun n =>
    isClosed_setOf_mem_projPointIdeal (SetLike.coe_mem _)

theorem projIdealOf_closure (C : Set Y) : projIdealOf (closure C) = projIdealOf C := by
  refine le_antisymm (projIdealOf_anti subset_closure) fun a ha => ?_
  have hC : C ⊆ projZeroSetIn {a} := subset_projZeroSetIn_iff.2 (by simpa using ha)
  have := (isClosed_projZeroSetIn {a}).closure_subset_iff.2 hC
  exact subset_projZeroSetIn_iff.1 this rfl

/-- The ideal of an irreducible subset is prime: primality of a homogeneous ideal
is tested on homogeneous elements, whose loci in `𝔪_x` are closed. -/
theorem isPrime_projIdealOf {Z : Set Y} (hZ : IsIrreducible Z) : (projIdealOf Z).IsPrime := by
  refine (Ideal.IsHomogeneous.isPrime_iff (isHomogeneous_projIdealOf Z)).2 ⟨?_, ?_⟩
  · intro htop
    obtain ⟨x, hx⟩ := hZ.nonempty
    have h1 : (1 : homogeneousCoordinateRing Y) ∈ projPointIdeal Y x.1 :=
      mem_projIdealOf.1 (htop ▸ Submodule.mem_top) x hx
    exact (isPrime_projPointIdeal x.2).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · rintro a b ⟨m, ha⟩ ⟨n, hb⟩ hab
    have hcov : Z ⊆ {x : Y | a ∈ projPointIdeal Y x.1} ∪ {x | b ∈ projPointIdeal Y x.1} :=
      fun x hx => (isPrime_projPointIdeal x.2).mem_or_mem (mem_projIdealOf.1 hab x hx)
    rcases isPreirreducible_iff_isClosed_union_isClosed.1 hZ.2 _ _
      (isClosed_setOf_mem_projPointIdeal ha) (isClosed_setOf_mem_projPointIdeal hb) hcov with
      h | h
    · exact Or.inl (mem_projIdealOf.2 fun x hx => h hx)
    · exact Or.inr (mem_projIdealOf.2 fun x hx => h hx)

/-- The ideal of a nonempty subset does not contain the irrelevant ideal: some
coordinate `xᵢ` is nonzero at a point of the subset. -/
theorem not_irrelevant_le_projIdealOf {C : Set Y} (hC : C.Nonempty) :
    ¬ (HomogeneousIdeal.irrelevant (projCoordGrading Y)).toIdeal ≤ projIdealOf C := by
  obtain ⟨x, hx⟩ := hC
  obtain ⟨i, hi⟩ := exists_mem_standardChart x.1
  intro h
  exact mk_X_notMem_projPointIdeal x.2 i hi (mem_projIdealOf.1
    (h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (mk_X_mem_projCoordGrading i Y))) x hx)

/-- For a closed subset `C` of a closed `Y`, the zero set of `I(C)` is `C`. -/
theorem projZeroSetIn_projIdealOf (hY : IsClosed Y) {C : Set Y} (hC : IsClosed C) :
    projZeroSetIn (projIdealOf C : Set (homogeneousCoordinateRing Y)) = C := by
  refine Set.Subset.antisymm (fun y hy => ?_) (subset_projZeroSetIn_iff.2 le_rfl)
  have halg : IsProjAlgebraicSet (Subtype.val '' C) :=
    isClosed_iff_isProjAlgebraicSet.1 (isClosed_image_val hY hC)
  have hy' : y.1 ∈ projZeroSet (homogeneousVanishingSet (Subtype.val '' C)) := by
    rintro g ⟨⟨n, hg⟩, hgC⟩
    have hmem : Ideal.Quotient.mk (homogeneousVanishingIdeal Y) g ∈ projIdealOf C := by
      refine mem_projIdealOf.2 fun x hx => ?_
      rw [mem_projPointIdeal_iff_eval (mk_mem_projCoordGrading hg), projCoordEval_mk]
      exact hgC x.1 ⟨x, hx, rfl⟩
    have : _ ∈ projPointIdeal Y y.1 := hy hmem
    rw [mem_projPointIdeal_iff_eval (mk_mem_projCoordGrading hg), projCoordEval_mk] at this
    exact this
  rw [halg.projZeroSet_homogeneousVanishingSet] at hy'
  obtain ⟨c, hc, hcy⟩ := hy'
  rwa [Subtype.val_injective hcy] at hc

/-- A closed nonempty subset of `Y` whose ideal is prime is irreducible: a
decomposition into two proper closed pieces would give two elements outside the
ideal with product inside it. -/
theorem isIrreducible_of_isPrime_projIdealOf (hY : IsClosed Y) {T : Set Y} (hT : IsClosed T)
    (hne : T.Nonempty) (hp : (projIdealOf T).IsPrime) : IsIrreducible T := by
  refine ⟨hne, isPreirreducible_iff_isClosed_union_isClosed.2 fun z₁ z₂ hz₁ hz₂ hcov => ?_⟩
  have key : ∀ z : Set Y, IsClosed z → ¬ T ⊆ z →
      ∃ a ∈ projIdealOf (T ∩ z), a ∉ projIdealOf T := by
    intro z hz hTz
    by_contra hall
    push Not at hall
    apply hTz
    have hle : projZeroSetIn (projIdealOf T : Set (homogeneousCoordinateRing Y)) ⊆
        projZeroSetIn (projIdealOf (T ∩ z) : Set (homogeneousCoordinateRing Y)) :=
      projZeroSetIn_anti fun a ha => hall a ha
    rw [projZeroSetIn_projIdealOf hY hT, projZeroSetIn_projIdealOf hY (hT.inter hz)] at hle
    exact fun x hx => (hle hx).2
  by_contra h
  push Not at h
  obtain ⟨a, ha, haT⟩ := key z₁ hz₁ h.1
  obtain ⟨b, hb, hbT⟩ := key z₂ hz₂ h.2
  have hab : a * b ∈ projIdealOf T := by
    refine mem_projIdealOf.2 fun x hx => ?_
    rcases hcov hx with h₁ | h₂
    · exact Ideal.mul_mem_right _ _ (mem_projIdealOf.1 ha x ⟨hx, h₁⟩)
    · exact Ideal.mul_mem_left _ _ (mem_projIdealOf.1 hb x ⟨hx, h₂⟩)
  rcases hp.mem_or_mem hab with h' | h'
  · exact haT h'
  · exact hbT h'

/-! ### The projective Nullstellensatz inside `S(Y)` -/

/-- The ideal of the polynomial ring spanned by the homogeneous polynomials
whose classes lie in a given ideal of `S(Y)`. -/
def projLiftIdeal (𝔭 : Ideal (homogeneousCoordinateRing Y)) : Ideal (MvPolynomial σ k) :=
  Ideal.span {f | (∃ m, f.IsHomogeneous m) ∧
    Ideal.Quotient.mk (homogeneousVanishingIdeal Y) f ∈ 𝔭}

theorem isHomogeneousIdeal_projLiftIdeal (𝔭 : Ideal (homogeneousCoordinateRing Y)) :
    IsHomogeneousIdeal (projLiftIdeal 𝔭) :=
  Ideal.homogeneous_span _ _ fun _ hf => isHomogeneousElem_iff.2 hf.1

theorem map_projLiftIdeal_le (𝔭 : Ideal (homogeneousCoordinateRing Y)) :
    (projLiftIdeal 𝔭).map (Ideal.Quotient.mk (homogeneousVanishingIdeal Y)) ≤ 𝔭 :=
  Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 fun _ hf => hf.2)

theorem homogeneousVanishingIdeal_le_projLiftIdeal (𝔭 : Ideal (homogeneousCoordinateRing Y)) :
    homogeneousVanishingIdeal Y ≤ projLiftIdeal 𝔭 := by
  refine Ideal.span_le.2 fun f hf => Ideal.subset_span ⟨hf.1, ?_⟩
  have h0 : Ideal.Quotient.mk (homogeneousVanishingIdeal Y) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hf)
  rw [h0]
  exact zero_mem _

theorem projZeroSet_projLiftIdeal_subset (hY : IsClosed Y)
    (𝔭 : Ideal (homogeneousCoordinateRing Y)) :
    projZeroSet (projLiftIdeal 𝔭 : Set (MvPolynomial σ k)) ⊆ Y := by
  refine (projZeroSet_anti_mono (homogeneousVanishingIdeal_le_projLiftIdeal 𝔭)).trans ?_
  rw [projZeroSet_homogeneousVanishingIdeal_eq_closure, hY.closure_eq]

/-- For a homogeneous ideal `𝔭` of `S(Y)`, a point of `Y` lies in the zero set
of `𝔭` exactly when it lies in the projective zero set of the lifted ideal. -/
theorem mem_projZeroSetIn_iff_projLiftIdeal {𝔭 : Ideal (homogeneousCoordinateRing Y)}
    (h𝔭 : 𝔭.IsHomogeneous (projCoordGrading Y)) (y : Y) :
    y ∈ projZeroSetIn (𝔭 : Set (homogeneousCoordinateRing Y)) ↔
      y.1 ∈ projZeroSet (projLiftIdeal 𝔭 : Set (MvPolynomial σ k)) := by
  rw [projLiftIdeal, projZeroSet_span]
  constructor
  · rintro hy f ⟨⟨m, hf⟩, hf𝔭⟩
    have := hy hf𝔭
    rwa [SetLike.mem_coe, mem_projPointIdeal_iff_eval (mk_mem_projCoordGrading hf),
      projCoordEval_mk] at this
  · intro hy a ha
    refine (isHomogeneous_projPointIdeal (Y := Y) (P := y.1)).mem_iff.2 fun n => ?_
    obtain ⟨g, hg, hga⟩ := exists_isHomogeneous_of_mem_projCoordGrading
      (DirectSum.decompose (projCoordGrading Y) a n).2
    rw [← hga, mem_projPointIdeal_iff_eval (mk_mem_projCoordGrading hg), projCoordEval_mk]
    exact hy g ⟨⟨n, hg⟩, hga ▸ h𝔭.mem_iff.1 ha n⟩

section AlgClosed

variable [IsAlgClosed k] [Finite σ]

/-- The zero set in `Y` of a relevant homogeneous prime of `S(Y)` is nonempty:
otherwise, by the projective Nullstellensatz, every `xᵢ` and hence every
positive-degree element would lie in the prime. -/
theorem projZeroSetIn_nonempty (hY : IsClosed Y) (q : ProjectiveSpectrum (projCoordGrading Y)) :
    (projZeroSetIn (q.asHomogeneousIdeal.toIdeal :
      Set (homogeneousCoordinateRing Y))).Nonempty := by
  by_contra hempty
  have hZ : projZeroSet (projLiftIdeal q.asHomogeneousIdeal.toIdeal : Set (MvPolynomial σ k)) =
      ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun P hP => hempty ?_
    exact ⟨⟨P, projZeroSet_projLiftIdeal_subset hY _ hP⟩,
      (mem_projZeroSetIn_iff_projLiftIdeal q.asHomogeneousIdeal.isHomogeneous _).2 hP⟩
  have hrad := (projZeroSet_eq_empty_iff (isHomogeneousIdeal_projLiftIdeal _)).1 hZ
  apply q.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  obtain ⟨g, hg, rfl⟩ := exists_isHomogeneous_of_mem_projCoordGrading (n := i) ha
  have hgirr : g ∈ irrelevantIdeal k σ := by
    have := sub_C_eval_zero_mem_irrelevantIdeal g
    rwa [eval_zero_of_isHomogeneous hg hi, map_zero, sub_zero] at this
  obtain ⟨m, hm⟩ := hrad hgirr
  refine q.isPrime.mem_of_pow_mem m (map_projLiftIdeal_le _ ?_)
  rw [← map_pow]
  exact Ideal.mem_map_of_mem _ hm

/-- **Projective Nullstellensatz in `S(Y)`.** A relevant homogeneous prime of
`S(Y)` is the ideal of its zero set in `Y`. -/
theorem projIdealOf_projZeroSetIn (hY : IsClosed Y)
    (q : ProjectiveSpectrum (projCoordGrading Y)) :
    projIdealOf (projZeroSetIn (q.asHomogeneousIdeal.toIdeal :
      Set (homogeneousCoordinateRing Y))) = q.asHomogeneousIdeal.toIdeal := by
  refine le_antisymm (fun a ha => ?_) (subset_projZeroSetIn_iff.1 le_rfl)
  refine q.asHomogeneousIdeal.isHomogeneous.mem_iff.2 fun n => ?_
  have han := (isHomogeneous_projIdealOf _).mem_iff.1 ha n
  obtain ⟨g, hg, hga⟩ := exists_isHomogeneous_of_mem_projCoordGrading
    (DirectSum.decompose (projCoordGrading Y) a n).2
  rw [← hga] at han ⊢
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · obtain ⟨y, hy⟩ := projZeroSetIn_nonempty hY q
    have hy0 := mem_projIdealOf.1 han y hy
    rw [mem_projPointIdeal_iff_eval (mk_mem_projCoordGrading hg), projCoordEval_mk] at hy0
    have hC : g = C (coeff 0 g) :=
      (totalDegree_eq_zero_iff_eq_C (p := g)).1
        ((totalDegree_zero_iff_isHomogeneous (σ := σ) (p := g)).2 hg)
    rw [hC, eval_C] at hy0
    rw [hC, hy0, map_zero, map_zero]
    exact zero_mem _
  · have hvan : ∀ P ∈ projZeroSet (projLiftIdeal q.asHomogeneousIdeal.toIdeal :
        Set (MvPolynomial σ k)), HomogeneousVanish g P := by
      intro P hP
      have hPY := projZeroSet_projLiftIdeal_subset hY _ hP
      have hy : (⟨P, hPY⟩ : Y) ∈ projZeroSetIn (q.asHomogeneousIdeal.toIdeal :
          Set (homogeneousCoordinateRing Y)) :=
        (mem_projZeroSetIn_iff_projLiftIdeal q.asHomogeneousIdeal.isHomogeneous _).2 hP
      have := mem_projIdealOf.1 han _ hy
      rwa [mem_projPointIdeal_iff_eval (mk_mem_projCoordGrading hg), projCoordEval_mk] at this
    obtain ⟨m, -, hm⟩ := exists_pow_mem_of_forall_homogeneousVanish
      (isHomogeneousIdeal_projLiftIdeal q.asHomogeneousIdeal.toIdeal) hpos hg hvan
    refine q.isPrime.mem_of_pow_mem m (map_projLiftIdeal_le _ ?_)
    simpa only [map_pow] using Ideal.mem_map_of_mem (Ideal.Quotient.mk _) hm

theorem isIrreducible_projZeroSetIn (hY : IsClosed Y)
    (q : ProjectiveSpectrum (projCoordGrading Y)) :
    IsIrreducible (projZeroSetIn (q.asHomogeneousIdeal.toIdeal :
      Set (homogeneousCoordinateRing Y))) :=
  isIrreducible_of_isPrime_projIdealOf hY (isClosed_projZeroSetIn _) (projZeroSetIn_nonempty hY q)
    (by rw [projIdealOf_projZeroSetIn hY q]; exact q.isPrime)

/-- **Points.** The irreducible closed subsets of a projective variety `Y`
correspond to the relevant homogeneous primes of `S(Y)`: an irreducible closed
subset goes to its ideal, a prime to its zero set. -/
def projIrreducibleClosedsEquiv (hY : IsProjVariety Y) :
    IrreducibleCloseds Y ≃ ProjectiveSpectrum (projCoordGrading Y) where
  toFun Z :=
    { asHomogeneousIdeal := ⟨projIdealOf (Z : Set Y), isHomogeneous_projIdealOf _⟩
      isPrime := isPrime_projIdealOf Z.isIrreducible
      not_irrelevant_le := fun h =>
        not_irrelevant_le_projIdealOf Z.isIrreducible.nonempty fun _ ha => h ha }
  invFun q := ⟨projZeroSetIn (q.asHomogeneousIdeal.toIdeal : Set (homogeneousCoordinateRing Y)),
    isIrreducible_projZeroSetIn hY.2 q, isClosed_projZeroSetIn _⟩
  left_inv Z := IrreducibleCloseds.ext (projZeroSetIn_projIdealOf hY.2 Z.isClosed)
  right_inv q := ProjectiveSpectrum.ext
    (HomogeneousIdeal.toIdeal_injective (projIdealOf_projZeroSetIn hY.2 q))

@[simp]
theorem projIrreducibleClosedsEquiv_apply_toIdeal (hY : IsProjVariety Y)
    (Z : IrreducibleCloseds Y) :
    (projIrreducibleClosedsEquiv hY Z).asHomogeneousIdeal.toIdeal = projIdealOf (Z : Set Y) :=
  rfl

@[simp]
theorem coe_projIrreducibleClosedsEquiv_symm (hY : IsProjVariety Y)
    (q : ProjectiveSpectrum (projCoordGrading Y)) :
    (((projIrreducibleClosedsEquiv hY).symm q : IrreducibleCloseds Y) : Set Y) =
      projZeroSetIn (q.asHomogeneousIdeal.toIdeal : Set (homogeneousCoordinateRing Y)) :=
  rfl

/-- **Points, with topology.** The generic completion `t(Y)` of a projective
variety is homeomorphic to `Proj S(Y)`, an irreducible closed subset going to
its ideal. -/
def projGenericCompletionHomeomorph (hY : IsProjVariety Y) :
    genericCompletionObj (TopCat.of Y) ≃ₜ ProjectiveSpectrum (projCoordGrading Y) where
  toEquiv := projIrreducibleClosedsEquiv hY
  continuous_toFun := by
    rw [continuous_iff_isClosed]
    intro C hC
    obtain ⟨S, rfl⟩ := (ProjectiveSpectrum.isClosed_iff_zeroLocus _ C).1 hC
    refine (genericCompletion_isClosed_iff (TopCat.of Y) _).2
      ⟨projZeroSetIn S, isClosed_projZeroSetIn S, ?_⟩
    ext (Z : IrreducibleCloseds Y)
    change S ⊆ projIdealOf (Z : Set Y) ↔ (Z : Set Y) ⊆ projZeroSetIn S
    exact subset_projZeroSetIn_iff.symm
  continuous_invFun := by
    rw [continuous_iff_isClosed]
    intro C hC
    obtain ⟨D, hD, rfl⟩ := (genericCompletion_isClosed_iff _ C).1 hC
    rw [ProjectiveSpectrum.isClosed_iff_zeroLocus]
    refine ⟨projIdealOf D, ?_⟩
    ext q
    change projZeroSetIn (q.asHomogeneousIdeal.toIdeal : Set (homogeneousCoordinateRing Y)) ⊆ D ↔
      (projIdealOf D : Set (homogeneousCoordinateRing Y)) ⊆ q.asHomogeneousIdeal.toIdeal
    constructor
    · intro h
      have := projIdealOf_anti h
      rwa [projIdealOf_projZeroSetIn hY.2 q] at this
    · intro h
      have := projZeroSetIn_anti h
      rwa [projZeroSetIn_projIdealOf hY.2 hD] at this

/-- On classical points the homeomorphism is `x ↦ 𝔪_x`. -/
theorem projGenericCompletionHomeomorph_alpha (hY : IsProjVariety Y) (x : Y) :
    (projGenericCompletionHomeomorph hY
      (genericCompletionAlpha (TopCat.of Y) x)).asHomogeneousIdeal.toIdeal =
      projPointIdeal Y x.1 := by
  change projIdealOf (closure {x}) = _
  rw [projIdealOf_closure, projIdealOf_singleton]

end AlgClosed

/-! ### Evaluating homogeneous fractions at classical points -/

section Evaluation

open HomogeneousLocalization

/-- The denominator of a homogeneous fraction with denominator outside a prime
`𝔮 ⊇ 𝔪_x` does not vanish at `x`. -/
theorem projCoordEval_den_ne_zero (x : Y) {𝔮 : Ideal (homogeneousCoordinateRing Y)} [𝔮.IsPrime]
    (h𝔮 : projPointIdeal Y x.1 ≤ 𝔮) (c : NumDenSameDeg (projCoordGrading Y) 𝔮.primeCompl) :
    projCoordEval x c.den ≠ 0 :=
  fun h => c.den_mem (h𝔮 ((mem_projPointIdeal_iff_eval c.den.2 x).2 h))

/-- The value `a(x) / b(x)` of a homogeneous fraction `a / b`. -/
def projFractionEval (x : Y) (𝔮 : Ideal (homogeneousCoordinateRing Y)) [𝔮.IsPrime]
    (c : NumDenSameDeg (projCoordGrading Y) 𝔮.primeCompl) : k :=
  projCoordEval x c.num / projCoordEval x c.den

/-- The value of a homogeneous fraction at `x` depends only on the fraction:
an annihilating element outside `𝔮` has a homogeneous component outside `𝔪_x`,
which annihilates the homogeneous cross-difference and does not vanish at `x`. -/
theorem projFractionEval_eq_of_embedding_eq (x : Y) {𝔮 : Ideal (homogeneousCoordinateRing Y)}
    [𝔮.IsPrime]
    (h𝔮 : projPointIdeal Y x.1 ≤ 𝔮) {c c' : NumDenSameDeg (projCoordGrading Y) 𝔮.primeCompl}
    (h : NumDenSameDeg.embedding (projCoordGrading Y) 𝔮.primeCompl c =
      NumDenSameDeg.embedding (projCoordGrading Y) 𝔮.primeCompl c') :
    projFractionEval x 𝔮 c = projFractionEval x 𝔮 c' := by
  obtain ⟨u, hu⟩ := Localization.r_iff_exists.1 (Localization.mk_eq_mk_iff.1 h)
  have hw : (c'.den : homogeneousCoordinateRing Y) * c.num - c.den * c'.num ∈
      projCoordGrading Y (c'.deg + c.deg) := by
    refine sub_mem (SetLike.mul_mem_graded c'.den.2 c.num.2) ?_
    rw [add_comm]
    exact SetLike.mul_mem_graded c.den.2 c'.num.2
  have huw : (u : homogeneousCoordinateRing Y) *
      ((c'.den : homogeneousCoordinateRing Y) * c.num - c.den * c'.num) = 0 := by
    rw [mul_sub, sub_eq_zero]
    exact hu
  have hux : (u : homogeneousCoordinateRing Y) ∉ projPointIdeal Y x.1 := fun h' => u.2 (h𝔮 h')
  obtain ⟨j, hj⟩ := exists_decompose_notMem (projPointIdeal Y x.1)
    (isHomogeneous_projPointIdeal (Y := Y) (P := x.1)) hux
  have hj0 := decompose_mul_eq_zero (j := j) hw huw
  have hjx : projCoordEval x (DirectSum.decompose (projCoordGrading Y) (u : _) j) ≠ 0 :=
    fun h' => hj ((mem_projPointIdeal_iff_eval (SetLike.coe_mem _) x).2 h')
  have hev := congrArg (projCoordEval x) hj0
  rw [map_mul, map_zero, mul_eq_zero] at hev
  have hev' := hev.resolve_left hjx
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at hev'
  unfold projFractionEval
  rw [div_eq_div_iff (projCoordEval_den_ne_zero x h𝔮 c) (projCoordEval_den_ne_zero x h𝔮 c')]
  linear_combination hev'

/-- **Evaluation at a classical point.** For a prime `𝔮` of `S(Y)` containing
`𝔪_x`, the ring map `S(Y)_(𝔮) → k` sending `a / b` to `a(x) / b(x)`. -/
def projAtPrimeEval (x : Y) (𝔮 : Ideal (homogeneousCoordinateRing Y)) [𝔮.IsPrime]
    (h𝔮 : projPointIdeal Y x.1 ≤ 𝔮) :
    HomogeneousLocalization.AtPrime (projCoordGrading Y) 𝔮 →+* k where
  toFun := Quotient.lift (projFractionEval x 𝔮) fun _ _ h =>
    projFractionEval_eq_of_embedding_eq x h𝔮 h
  map_one' := by
    change projCoordEval x 1 / projCoordEval x 1 = 1
    simp
  map_mul' a b := by
    obtain ⟨a, rfl⟩ := mk_surjective a
    obtain ⟨b, rfl⟩ := mk_surjective b
    change projCoordEval x (a.num * b.num) / projCoordEval x (a.den * b.den) =
      projCoordEval x a.num / projCoordEval x a.den * (projCoordEval x b.num /
        projCoordEval x b.den)
    rw [map_mul, map_mul, mul_div_mul_comm]
  map_zero' := by
    change projCoordEval x 0 / projCoordEval x 1 = 0
    simp
  map_add' a b := by
    obtain ⟨a, rfl⟩ := mk_surjective a
    obtain ⟨b, rfl⟩ := mk_surjective b
    change projCoordEval x (a.den * b.num + b.den * a.num) / projCoordEval x (a.den * b.den) =
      projCoordEval x a.num / projCoordEval x a.den + projCoordEval x b.num /
        projCoordEval x b.den
    have ha := projCoordEval_den_ne_zero x h𝔮 a
    have hb := projCoordEval_den_ne_zero x h𝔮 b
    rw [map_add, map_mul, map_mul, map_mul]
    field_simp
    ring

@[simp]
theorem projAtPrimeEval_mk (x : Y) (𝔮 : Ideal (homogeneousCoordinateRing Y)) [𝔮.IsPrime]
    (h𝔮 : projPointIdeal Y x.1 ≤ 𝔮) (c : NumDenSameDeg (projCoordGrading Y) 𝔮.primeCompl) :
    projAtPrimeEval x 𝔮 h𝔮 (mk c) = projCoordEval x c.num / projCoordEval x c.den :=
  rfl

end Evaluation

/-- **Identity principle in `S(Y)`.** A homogeneous element of `S(Y)` vanishing
on a nonempty open subset of the irreducible `Y` is zero. -/
theorem eq_zero_of_projCoordEval_eq_zero_of_isOpen (hY : IsIrreducible Y) {n : ℕ}
    {a : homogeneousCoordinateRing Y} (ha : a ∈ projCoordGrading Y n) {U : Set Y}
    (hU : IsOpen U) (hne : U.Nonempty) (h : ∀ x ∈ U, projCoordEval x a = 0) : a = 0 := by
  have : PreirreducibleSpace Y := isPreirreducible_iff_preirreducibleSpace.1 hY.2
  have hsub : U ⊆ {x : Y | a ∈ projPointIdeal Y x.1} :=
    fun x hx => (mem_projPointIdeal_iff_eval ha x).2 (h x hx)
  have hcl := (isClosed_setOf_mem_projPointIdeal ha).closure_subset_iff.2 hsub
  rw [(hU.dense hne).closure_eq] at hcl
  obtain ⟨g, hg, rfl⟩ := exists_isHomogeneous_of_mem_projCoordGrading ha
  refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨⟨n, hg⟩, fun P hP => ?_⟩)
  have := (mem_projPointIdeal_iff_eval ha ⟨P, hP⟩).1 (hcl (Set.mem_univ _))
  rwa [projCoordEval_mk] at this

/-! ### The sheaf comparison -/

section Sheaf

open HomogeneousLocalization

variable [IsAlgClosed k] [Finite σ] (hY : IsProjVariety Y)

/-- The homeomorphism `t(Y) ≅ Proj S(Y)` as an isomorphism in `TopCat`. -/
def projGenericCompletionIsoTop :
    genericCompletionObj (TopCat.of (Variety.ofProjective hY).carrier) ≅
      ProjectiveSpectrum.top (projCoordGrading Y) :=
  TopCat.isoOfHomeo (projGenericCompletionHomeomorph hY)

/-- The point of `Proj S(Y)` attached to a classical point `x`: the prime `𝔪_x`. -/
abbrev projPoint (x : Y) : ProjectiveSpectrum (projCoordGrading Y) :=
  projGenericCompletionHomeomorph hY (genericCompletionAlpha (TopCat.of Y) x)

theorem projPoint_toIdeal (x : Y) :
    (projPoint hY x).asHomogeneousIdeal.toIdeal = projPointIdeal Y x.1 :=
  projGenericCompletionHomeomorph_alpha hY x

theorem continuous_projPoint : Continuous (projPoint hY) :=
  (projGenericCompletionHomeomorph hY).continuous.comp
    (genericCompletionAlpha (TopCat.of Y)).hom.continuous

/-- The open subset of `Y` corresponding to an open subset `W` of `Proj S(Y)`:
the classical points whose prime lies in `W`. -/
def projOpenToVariety (W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))) :
    Opens (Variety.ofProjective hY).carrier :=
  (genericCompletionOpensOrderIso (TopCat.of _)).symm
    ((Opens.map (projGenericCompletionIsoTop hY).hom).obj W)

theorem mem_projOpenToVariety {W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))}
    {x : Y} : x ∈ projOpenToVariety hY W ↔ projPoint hY x ∈ W :=
  Iff.rfl

theorem projOpenToVariety_mono {W W' : Opens (ProjectiveSpectrum.top (projCoordGrading Y))}
    (h : W' ≤ W) : projOpenToVariety hY W' ≤ projOpenToVariety hY W :=
  fun _ hx => h hx

/-- Every point `q` of an open `W ⊆ Proj S(Y)` has a classical point of its
zero set inside the corresponding open of `Y`. -/
theorem exists_mem_projZeroSetIn_projOpenToVariety
    {W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))}
    {q : ProjectiveSpectrum (projCoordGrading Y)} (hq : q ∈ W) :
    ∃ x : Y, x ∈ projZeroSetIn (q.asHomogeneousIdeal.toIdeal : Set (homogeneousCoordinateRing Y)) ∧
      x ∈ projOpenToVariety hY W := by
  have h := (genericCompletionOpensOrderIso (TopCat.of Y)).apply_symm_apply
    ((Opens.map (projGenericCompletionIsoTop hY).hom).obj W)
  have hmem : (projGenericCompletionHomeomorph hY).symm q ∈
      (Opens.map (projGenericCompletionIsoTop hY).hom).obj W := by
    change projGenericCompletionHomeomorph hY ((projGenericCompletionHomeomorph hY).symm q) ∈ W
    rwa [Homeomorph.apply_symm_apply]
  rw [← h] at hmem
  obtain ⟨x, hxZ, hxU⟩ := hmem
  exact ⟨x, hxZ, hxU⟩

/-- The value at a classical point `x` of a section of the structure sheaf of
`Proj S(Y)`: evaluate its value in `S(Y)_(𝔪_x)` at `x`. -/
def projSectionEval {W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))}
    (s : (ProjectiveSpectrum.Proj.structureSheaf (projCoordGrading Y)).1.obj (op W))
    (x : projOpenToVariety hY W) : k :=
  projAtPrimeEval x.1 (projPoint hY x.1).asHomogeneousIdeal.toIdeal
    (projPoint_toIdeal hY x.1).ge (s.1 ⟨projPoint hY x.1, x.2⟩)

theorem projSectionEval_eq_div {W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))}
    (s : (ProjectiveSpectrum.Proj.structureSheaf (projCoordGrading Y)).1.obj (op W))
    (x : projOpenToVariety hY W)
    (c : NumDenSameDeg (projCoordGrading Y)
      (projPoint hY x.1).asHomogeneousIdeal.toIdeal.primeCompl)
    (he : s.1 ⟨projPoint hY x.1, x.2⟩ = mk c) :
    projSectionEval hY s x = projCoordEval x.1 c.num / projCoordEval x.1 c.den := by
  rw [projSectionEval, he]
  rfl

/-- A homogeneous element outside the prime of a classical point does not vanish
there. -/
theorem projCoordEval_ne_zero_of_notMem {x : Y} {n : ℕ} {b : homogeneousCoordinateRing Y}
    (hb : b ∈ projCoordGrading Y n) (h : b ∉ (projPoint hY x).asHomogeneousIdeal) :
    projCoordEval x b ≠ 0 := by
  intro h0
  apply h
  change b ∈ (projPoint hY x).asHomogeneousIdeal.toIdeal
  rw [projPoint_toIdeal]
  exact (mem_projPointIdeal_iff_eval hb x).2 h0

/-- Evaluating a structure-sheaf section at the classical points gives a
regular function. -/
theorem projSectionEval_mem {W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))}
    (s : (ProjectiveSpectrum.Proj.structureSheaf (projCoordGrading Y)).1.obj (op W)) :
    projSectionEval hY s ∈ (Variety.ofProjective hY).regular (projOpenToVariety hY W) := by
  change IsRegularProjVia (projOpenIota (projOpenToVariety hY W)) (projSectionEval hY s)
  intro P
  obtain ⟨V', hV', i, j, r, t, t_nin, hfr⟩ := s.2 ⟨projPoint hY P.1, P.2⟩
  obtain ⟨g, hg, hgr⟩ := exists_isHomogeneous_of_mem_projCoordGrading r.2
  obtain ⟨h, hh, hht⟩ := exists_isHomogeneous_of_mem_projCoordGrading t.2
  refine ⟨{x | projPoint hY x.1 ∈ V'},
    V'.isOpen.preimage ((continuous_projPoint hY).comp continuous_subtype_val), hV', j, g, h,
    hg, hh, fun x hx => ?_, fun x hx => ?_⟩
  · have := projCoordEval_ne_zero_of_notMem hY t.2 (t_nin ⟨projPoint hY x.1, hx⟩)
    rwa [← hht, projCoordEval_mk] at this
  · rw [projSectionEval_eq_div hY s x _ (hfr ⟨projPoint hY x.1, hx⟩), ← hgr, ← hht,
      projCoordEval_mk, projCoordEval_mk]

/-- **Sections.** Evaluation at classical points, as a ring map from sections
of the structure sheaf of `Proj S(Y)` over `W` to regular functions on the
corresponding open of `Y`. -/
def projToRegular (W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))) :
    (ProjectiveSpectrum.Proj.structureSheaf (projCoordGrading Y)).1.obj (op W) →+*
      (Variety.ofProjective hY).regular (projOpenToVariety hY W) where
  toFun s := ⟨projSectionEval hY s, projSectionEval_mem hY s⟩
  map_one' := Subtype.ext <| funext fun x =>
    map_one (projAtPrimeEval x.1 _ (projPoint_toIdeal hY x.1).ge)
  map_mul' s t := Subtype.ext <| funext fun x =>
    map_mul (projAtPrimeEval x.1 _ (projPoint_toIdeal hY x.1).ge)
      (s.1 ⟨projPoint hY x.1, x.2⟩) (t.1 ⟨projPoint hY x.1, x.2⟩)
  map_zero' := Subtype.ext <| funext fun x =>
    map_zero (projAtPrimeEval x.1 _ (projPoint_toIdeal hY x.1).ge)
  map_add' s t := Subtype.ext <| funext fun x =>
    map_add (projAtPrimeEval x.1 _ (projPoint_toIdeal hY x.1).ge)
      (s.1 ⟨projPoint hY x.1, x.2⟩) (t.1 ⟨projPoint hY x.1, x.2⟩)

@[simp]
theorem projToRegular_apply (W : Opens (ProjectiveSpectrum.top (projCoordGrading Y)))
    (s : (ProjectiveSpectrum.Proj.structureSheaf (projCoordGrading Y)).1.obj (op W))
    (x : projOpenToVariety hY W) :
    (projToRegular hY W s).1 x = projSectionEval hY s x :=
  rfl

/-- Evaluation at classical points is injective on structure-sheaf sections: a
section that is locally `a / b` and vanishes at the classical points has `a`
vanishing on a nonempty open subset of `Y`, so `a = 0`. -/
theorem projToRegular_injective (W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))) :
    Function.Injective (projToRegular hY W) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply Subtype.ext
  funext q
  obtain ⟨V', hqV', i, j, r, t, t_nin, hfr⟩ := s.2 q
  have hr : (r : homogeneousCoordinateRing Y) = 0 := by
    obtain ⟨x0, -, hx0⟩ := exists_mem_projZeroSetIn_projOpenToVariety hY hqV'
    refine eq_zero_of_projCoordEval_eq_zero_of_isOpen hY.1 r.2
      (projOpenToVariety hY V').isOpen ⟨x0, hx0⟩ fun x hx => ?_
    have hxW : x ∈ projOpenToVariety hY W := projOpenToVariety_mono hY i.le hx
    have h0 : projSectionEval hY s ⟨x, hxW⟩ = 0 := congrArg (fun g => g.1 ⟨x, hxW⟩) hs
    rw [projSectionEval_eq_div hY s ⟨x, hxW⟩ _ (hfr ⟨projPoint hY x, hx⟩)] at h0
    exact (div_eq_zero_iff.1 h0).resolve_right
      (projCoordEval_ne_zero_of_notMem hY t.2 (t_nin ⟨projPoint hY x, hx⟩))
  refine (hfr ⟨q.1, hqV'⟩).trans ?_
  exact mk_eq_zero_of_num _ (Subtype.ext hr)

/-- Evaluation at classical points is surjective onto regular functions: a
regular function is locally `a / b` near a classical point of the zero set of
each prime `q`; these local quotients agree in every homogeneous localization by
the identity principle, and glue to a structure-sheaf section. -/
theorem projToRegular_surjective (W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))) :
    Function.Surjective (projToRegular hY W) := by
  intro g
  have key : ∀ q : W, ∃ (O : Set Y) (n : ℕ) (a f : homogeneousCoordinateRing Y),
      a ∈ projCoordGrading Y n ∧ f ∈ projCoordGrading Y n ∧ IsOpen O ∧
      O ⊆ {y : Y | projPoint hY y ∈ W} ∧
      (∃ x ∈ O, x ∈ projZeroSetIn
        ((q.1 : ProjectiveSpectrum (projCoordGrading Y)).asHomogeneousIdeal.toIdeal :
          Set (homogeneousCoordinateRing Y))) ∧
      ∀ (y : Y) (hy : y ∈ projOpenToVariety hY W), y ∈ O →
        projCoordEval y f ≠ 0 ∧ g.1 ⟨y, hy⟩ = projCoordEval y a / projCoordEval y f := by
    intro q
    obtain ⟨x, hxZ, hxU⟩ := exists_mem_projZeroSetIn_projOpenToVariety hY q.2
    obtain ⟨O, hO, hxO, n, G, H, hG, hH, hne, heq⟩ := g.2 ⟨x, hxU⟩
    obtain ⟨O₁, hO₁, rfl⟩ := isOpen_induced_iff.1 hO
    refine ⟨O₁ ∩ {y : Y | projPoint hY y ∈ W}, n, Ideal.Quotient.mk _ G, Ideal.Quotient.mk _ H,
      mk_mem_projCoordGrading hG, mk_mem_projCoordGrading hH,
      hO₁.inter (projOpenToVariety hY W).isOpen, Set.inter_subset_right,
      ⟨x, ⟨hxO, hxU⟩, hxZ⟩, fun y hy hyO => ⟨?_, ?_⟩⟩
    · exact hne ⟨y, hy⟩ hyO.1
    · exact heq ⟨y, hy⟩ hyO.1
  choose O n a f ha hf hO hOU hx hrep using key
  have hfq : ∀ q : W, f q ∉
      (q.1 : ProjectiveSpectrum (projCoordGrading Y)).asHomogeneousIdeal.toIdeal := by
    intro q hmem
    obtain ⟨x, hxO, hxZ⟩ := hx q
    exact (hrep q x (hOU q hxO) hxO).1 ((mem_projPointIdeal_iff_eval (hf q) x).1 (hxZ hmem))
  let N : W → Opens (ProjectiveSpectrum.top (projCoordGrading Y)) := fun q =>
    (Opens.map (projGenericCompletionIsoTop hY).inv).obj
      (genericCompletionOpensOrderIso (TopCat.of Y) ⟨O q, hO q⟩)
  have hN : ∀ q (z : ProjectiveSpectrum (projCoordGrading Y)), z ∈ N q ↔
      (projZeroSetIn (z.asHomogeneousIdeal.toIdeal : Set (homogeneousCoordinateRing Y)) ∩
        O q).Nonempty :=
    fun _ _ => Iff.rfl
  have hagree : ∀ q z : W, z.1 ∈ N q → a z * f q = a q * f z := by
    intro q z hz
    have hirr := isIrreducible_projZeroSetIn hY.2 z.1
    obtain ⟨x, hxO, hxZ⟩ := hx z
    have hne : (projZeroSetIn
        ((z.1 : ProjectiveSpectrum (projCoordGrading Y)).asHomogeneousIdeal.toIdeal :
        Set (homogeneousCoordinateRing Y)) ∩ (O z ∩ O q)).Nonempty :=
      hirr.2 _ _ (hO z) (hO q) ⟨x, hxZ, hxO⟩ ((hN q z.1).1 hz)
    have hmem : a z * f q - a q * f z ∈ projCoordGrading Y (n z + n q) := by
      refine sub_mem (SetLike.mul_mem_graded (ha z) (hf q)) ?_
      rw [add_comm]
      exact SetLike.mul_mem_graded (ha q) (hf z)
    rw [← sub_eq_zero]
    refine eq_zero_of_projCoordEval_eq_zero_of_isOpen hY.1 hmem ((hO z).inter (hO q))
      (hne.mono Set.inter_subset_right) fun y hy => ?_
    have hyW := hOU z hy.1
    obtain ⟨hfz, hgz⟩ := hrep z y hyW hy.1
    obtain ⟨hfq', hgq⟩ := hrep q y hyW hy.2
    rw [hgz] at hgq
    rw [map_sub, map_mul, map_mul]
    rw [div_eq_div_iff hfz hfq'] at hgq
    linear_combination hgq
  refine ⟨⟨fun q => mk ⟨n q, ⟨a q, ha q⟩, ⟨f q, hf q⟩, hfq q⟩, fun q => ?_⟩, ?_⟩
  · have hqN : q.1 ∈ N q := by
      obtain ⟨x, hxO, hxZ⟩ := hx q
      exact (hN q q.1).2 ⟨x, hxZ, hxO⟩
    have hnin : ∀ z : (N q ⊓ W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))),
        f q ∉ z.1.asHomogeneousIdeal := by
      intro z hmem
      obtain ⟨y, hyZ, hyO⟩ := (hN q z.1).1 z.2.1
      exact (hrep q y (hOU q hyO) hyO).1 ((mem_projPointIdeal_iff_eval (hf q) y).1 (hyZ hmem))
    refine ⟨N q ⊓ W, ⟨hqN, q.2⟩, homOfLE inf_le_right, n q, ⟨a q, ha q⟩, ⟨f q, hf q⟩, hnin,
      fun z => ?_⟩
    rw [ext_iff_val, val_mk, val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    have := hagree q (homOfLE (inf_le_right : N q ⊓ W ≤ W) z) z.2.1
    simp only [OneMemClass.coe_one, one_mul]
    linear_combination this
  · apply Subtype.ext
    funext x
    let q : W := ⟨projPoint hY x.1, x.2⟩
    refine (projAtPrimeEval_mk x.1 _ (projPoint_toIdeal hY x.1).ge _).trans ?_
    -- Compare with a representation `G / H` of `g` near `x` itself: the zero set
    -- of `𝔪_x` is irreducible and meets both neighbourhoods.
    obtain ⟨x', hx'O, hx'Z⟩ := hx q
    obtain ⟨O', hO', hxO', n', G, H, hG, hH, hne, heq⟩ := g.2 x
    obtain ⟨O₁, hO₁, rfl⟩ := isOpen_induced_iff.1 hO'
    have hqx : (q.1 : ProjectiveSpectrum (projCoordGrading Y)).asHomogeneousIdeal.toIdeal =
        projPointIdeal Y x.1.1 :=
      projPoint_toIdeal hY x.1
    have hxZ : (x.1 : Y) ∈ projZeroSetIn
        ((q.1 : ProjectiveSpectrum (projCoordGrading Y)).asHomogeneousIdeal.toIdeal :
          Set (homogeneousCoordinateRing Y)) := by
      change ((q.1 : ProjectiveSpectrum (projCoordGrading Y)).asHomogeneousIdeal.toIdeal :
        Set (homogeneousCoordinateRing Y)) ⊆ projPointIdeal Y x.1.1
      rw [hqx]
    have hU : IsOpen (O₁ ∩ {y : Y | projPoint hY y ∈ W}) :=
      hO₁.inter (projOpenToVariety hY W).isOpen
    obtain ⟨y₀, -, hy₀⟩ := (isIrreducible_projZeroSetIn hY.2 q.1).2 _ _ (hO q) hU
      ⟨x', hx'Z, hx'O⟩ ⟨x.1, hxZ, hxO', x.2⟩
    have hmem : a q * Ideal.Quotient.mk (homogeneousVanishingIdeal Y) H -
        Ideal.Quotient.mk (homogeneousVanishingIdeal Y) G * f q ∈
          projCoordGrading Y (n q + n') := by
      refine sub_mem (SetLike.mul_mem_graded (ha q) (mk_mem_projCoordGrading hH)) ?_
      rw [add_comm]
      exact SetLike.mul_mem_graded (mk_mem_projCoordGrading hG) (hf q)
    have hzero := eq_zero_of_projCoordEval_eq_zero_of_isOpen hY.1 hmem ((hO q).inter hU)
      ⟨y₀, hy₀⟩ fun y hy => by
        obtain ⟨hfy, hgy⟩ := hrep q y hy.2.2 hy.1
        have hHy : eval y.1.rep H ≠ 0 := hne ⟨y, hy.2.2⟩ hy.2.1
        have hGy : g.1 ⟨y, hy.2.2⟩ = eval y.1.rep G / eval y.1.rep H := heq ⟨y, hy.2.2⟩ hy.2.1
        rw [hgy, div_eq_div_iff hfy hHy] at hGy
        rw [map_sub, map_mul, map_mul, projCoordEval_mk, projCoordEval_mk]
        linear_combination hGy
    have hfx : projCoordEval x.1 (f q) ≠ 0 := by
      intro h0
      apply hfq q
      rw [hqx]
      exact (mem_projPointIdeal_iff_eval (hf q) x.1).2 h0
    have hHx : eval x.1.1.rep H ≠ 0 := hne x hxO'
    have hx0 : projCoordEval (x.1 : Y) (a q) * eval x.1.1.rep H =
        eval x.1.1.rep G * projCoordEval (x.1 : Y) (f q) := by
      have h0 := congrArg (projCoordEval (x.1 : Y)) hzero
      rw [map_sub, map_mul, map_mul, map_zero, sub_eq_zero] at h0
      exact h0
    change projCoordEval (x.1 : Y) (a q) / projCoordEval (x.1 : Y) (f q) = g.1 x
    rw [heq x hxO', div_eq_div_iff hfx hHx]
    linear_combination hx0

/-- Evaluation at classical points, as a morphism from the structure sheaf of
`Proj S(Y)` to the pushforward of `α_* 𝒪_Y` along `t(Y) ≅ Proj S(Y)`. -/
def projToGenericCompletionPushforward :
    (ProjectiveSpectrum.Proj.structureSheaf (projCoordGrading Y)).1 ⟶
      (TopCat.Presheaf.pushforward CommRingCat (projGenericCompletionIsoTop hY).hom).obj
        (genericCompletionRegularSheaf (Variety.ofProjective hY)).obj where
  app W := CommRingCat.ofHom (projToRegular hY W.unop)
  naturality _ _ _ := by
    ext
    rfl

instance isIso_projToGenericCompletionPushforward :
    IsIso (projToGenericCompletionPushforward hY) := by
  have (W : (Opens (ProjectiveSpectrum.top (projCoordGrading Y)))ᵒᵖ) :
      IsIso ((projToGenericCompletionPushforward hY).app W) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨projToRegular_injective hY W.unop, projToRegular_surjective hY W.unop⟩
  exact NatIso.isIso_of_isIso_app _

/-- The isomorphism of sheafed spaces `(t(Y), α_* 𝒪_Y) ≅ Proj S(Y)`: on points an
irreducible closed subset goes to its ideal, and on sections a section of the
structure sheaf is sent to the regular function obtained by evaluating it at the
classical points. -/
def projGenericCompletionSheafedSpaceIsoProj :
    genericCompletionSheafedSpace (Variety.ofProjective hY) ≅
      Proj.toSheafedSpace (projCoordGrading Y) :=
  SheafedSpace.isoMk
    (PresheafedSpace.isoOfComponents (projGenericCompletionIsoTop hY)
      (asIso (projToGenericCompletionPushforward hY)).symm)

end Sheaf

/-! ### Over `Spec k` -/

/-- **The structure morphism of `Proj S(Y)` over `k`**: the composite
`Proj S(Y) → Spec S(Y)₀ → Spec k`, the second map induced by the inclusion of the
constants `k → S(Y)₀`. -/
def projCoordStructureMorphism (Y : Set (ProjectiveSpace k σ)) :
    Proj (projCoordGrading Y) ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (projCoordGrading Y) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (projCoordGrading Y 0)))

section Main

variable [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] (hY : IsProjVariety Y)

/-- **Hartshorne II, Exercise 2.14(d).** For a projective variety `Y` over an
algebraically closed field, with homogeneous coordinate ring `S(Y)`, the scheme
`t(Y)` associated to `Y` by generic completion is canonically isomorphic to
`Proj S(Y)`. On points an irreducible closed subset `Z ⊆ Y` goes to its
homogeneous ideal in `S(Y)`; on sections a section of the structure sheaf of
`Proj S(Y)` goes to the regular function obtained by evaluating it at the
classical points. -/
def projectiveVarietyAssociatedSchemeIsoProj :
    varietyAssociatedScheme (Variety.ofProjective hY)
        (Variety.hasAffineOpenBasis_ofProjective hY) ≅ Proj (projCoordGrading Y) :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (LocallyRingedSpace.isoOfSheafedSpaceIso (projGenericCompletionSheafedSpaceIsoProj hY))

/-- On points, the isomorphism sends an irreducible closed subset `Z` of `Y` to
its ideal in `S(Y)`. -/
theorem projectiveVarietyAssociatedSchemeIsoProj_hom_base (Z : IrreducibleCloseds Y) :
    ((projectiveVarietyAssociatedSchemeIsoProj hY).hom.base Z).asHomogeneousIdeal.toIdeal =
      projIdealOf (Z : Set Y) :=
  rfl

/-- On points, a classical point `x` goes to the homogeneous prime `𝔪_x`. -/
theorem projectiveVarietyAssociatedSchemeIsoProj_hom_base_alpha (x : Y) :
    ((projectiveVarietyAssociatedSchemeIsoProj hY).hom.base
      (genericCompletionAlpha (TopCat.of Y) x)).asHomogeneousIdeal.toIdeal =
        projPointIdeal Y x.1 :=
  projGenericCompletionHomeomorph_alpha hY x

/-- On sections over an open `W ⊆ Proj S(Y)`, the isomorphism is evaluation at
the classical points. -/
theorem projectiveVarietyAssociatedSchemeIsoProj_hom_app
    (W : Opens (ProjectiveSpectrum.top (projCoordGrading Y))) :
    (projectiveVarietyAssociatedSchemeIsoProj hY).hom.app W =
      CommRingCat.ofHom (projToRegular hY W) :=
  rfl

/-- On global sections, the isomorphism evaluates a global section of
`Proj S(Y)` at the classical points. -/
theorem projectiveVarietyAssociatedSchemeIsoProj_hom_appTop_apply
    (τ : Γ(Proj (projCoordGrading Y), ⊤))
    (x : ((genericCompletionOpensOrderIso (TopCat.of (Variety.ofProjective hY).carrier)).symm ⊤)) :
    ((projectiveVarietyAssociatedSchemeIsoProj hY).hom.appTop τ).1 x =
      projAtPrimeEval x.1 _ (projPoint_toIdeal hY x.1).ge (τ.1 ⟨projPoint hY x.1, trivial⟩) :=
  rfl

/-- **Hartshorne II, Exercise 2.14(d), over `Spec k`.** The isomorphism
`t(Y) ≅ Proj S(Y)` is an isomorphism of schemes over `k`: it intertwines the
structure morphism `t(Y) → Spec k` given by the constant regular functions with
the structure morphism `Proj S(Y) → Spec S(Y)₀ → Spec k`. -/
theorem projectiveVarietyAssociatedSchemeIsoProj_hom_comp_structureMorphism :
    (projectiveVarietyAssociatedSchemeIsoProj hY).hom ≫ projCoordStructureMorphism Y =
      varietyAssociatedSchemeStructureMorphism (Variety.ofProjective hY)
        (Variety.hasAffineOpenBasis_ofProjective hY) := by
  apply varietyAssociatedScheme_structureMorphism_unique
  rw [projCoordStructureMorphism, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  simp only [Proj.toSpecZero, Scheme.Hom.comp_appTop, Category.assoc]
  rw [← Category.assoc (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc]
  rw [show Scheme.Hom.appTop (Proj.basicOpenToSpec (projCoordGrading Y) 1) = _ from
    Proj.basicOpenToSpec_app_top _ 1]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  ext c
  apply Subtype.ext
  funext x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  erw [projectiveVarietyAssociatedSchemeIsoProj_hom_appTop_apply]
  show _ = c
  simp only [Scheme.isoOfEq_inv, Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  have h1 : (⊤ : (Proj (projCoordGrading Y)).Opens) ≤ Proj.basicOpen (projCoordGrading Y) 1 := by
    rw [Proj.basicOpen_one]
  erw [topIso_inv_appTop_presheaf_map_map h1]
  change projCoordEval x.1 ((algebraMap k (projCoordGrading Y 0) c : projCoordGrading Y 0) :
    homogeneousCoordinateRing Y) / projCoordEval x.1 1 = c
  rw [SetLike.GradeZero.coe_algebraMap, map_one, div_one]
  exact projCoordEval_algebraMap x.1 c

end Main

end Hartshorne
