/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.PrincipalOpenCoordinateRing
import Hartshorne.Morphism.MorphismToAffine

/-!
# The complement of a hypersurface is affine

Hartshorne, *Algebraic Geometry*, I.4, Lemma 4.2 (p. 25).

For a nonzero polynomial `f`, the principal open set `D(f)` is isomorphic to
the graph hypersurface `Z(t * f - 1)`. Projection onto the original coordinates
has inverse `x ↦ (1 / f(x), x)`. The graph hypersurface is affine because its
coordinate ring is the domain obtained by localizing away from `f`.

## Main result

* `Hartshorne.graphProjection_isIso`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {σ : Type v} [Finite σ]

/-- The principal open subset `D(f)` of affine space. -/
def principalOpen (f : MvPolynomial σ k) : Set (σ → k) :=
  {x | eval x f ≠ 0}

/-- A principal open defined by a nonzero polynomial is nonempty over an
algebraically closed field. -/
theorem principalOpen_nonempty (f : MvPolynomial σ k) (hf : f ≠ 0) :
    (principalOpen f).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hz : zeroLocus k (Ideal.span ({f} : Set (MvPolynomial σ k))) = Set.univ := by
    rw [MvPolynomial.zeroLocus_span]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    intro p hp
    subst p
    by_contra hx
    have hxD : x ∈ principalOpen f := hx
    rw [hne] at hxD
    exact hxD
  have hrad : (Ideal.span ({f} : Set (MvPolynomial σ k))).radical = ⊥ := by
    have h := congrArg (vanishingIdeal k) hz
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at h
    have hbot : vanishingIdeal k (Set.univ : Set (σ → k)) = ⊥ := by
      calc
        vanishingIdeal k (Set.univ : Set (σ → k)) =
            vanishingIdeal k (zeroLocus k (⊥ : Ideal (MvPolynomial σ k))) := by
              simpa only [Set.top_eq_univ] using congrArg (vanishingIdeal k)
                (MvPolynomial.zeroLocus_bot (k := k) (K := k) (σ := σ)).symm
        _ = (⊥ : Ideal (MvPolynomial σ k)).radical :=
          MvPolynomial.vanishingIdeal_zeroLocus_eq_radical _
        _ = ⊥ := by simp
    exact h.trans hbot
  have hmem : f ∈ (Ideal.span ({f} : Set (MvPolynomial σ k))).radical :=
    Ideal.le_radical (Ideal.subset_span (Set.mem_singleton f))
  rw [hrad] at hmem
  exact hf hmem

omit [IsAlgClosed k] [Finite σ] in
/-- A principal open is open in affine space. -/
theorem principalOpen_isOpen (f : MvPolynomial σ k) : IsOpen (principalOpen f) := by
  have hclosed : IsClosed (zeroSet ({f} : Set (MvPolynomial σ k))) :=
    isClosed_zeroSet _
  have heq : principalOpen f = (zeroSet ({f} : Set (MvPolynomial σ k)))ᶜ := by
    ext x
    simp [principalOpen, mem_zeroSet_iff]
  rw [heq]
  exact hclosed.isOpen_compl

/-- Affine space itself is an affine variety. -/
theorem affineSpace_isAffineVariety :
    IsAffineVariety (Set.univ : Set (σ → k)) := by
  simpa [MvPolynomial.zeroLocus_bot] using
    (isAffineVariety_zeroLocus_of_isPrime
      (k := k) (σ := σ) (I := (⊥ : Ideal (MvPolynomial σ k))) Ideal.isPrime_bot)

/-- The nonempty principal open `D(f)` is a quasi-affine variety. -/
theorem principalOpen_isQuasiAffineVariety (f : MvPolynomial σ k) (hf : f ≠ 0) :
    IsQuasiAffineVariety (principalOpen f) := by
  refine ⟨principalOpen_nonempty f hf, Set.univ, principalOpen f,
    affineSpace_isAffineVariety (k := k) (σ := σ), principalOpen_isOpen f, ?_⟩
  simp

/-- The graph equation cuts out an affine variety when `f` is nonzero. -/
theorem graph_isAffineVariety (f : MvPolynomial σ k) (hf : f ≠ 0) :
    IsAffineVariety (zeroLocus k (graphIdeal f)) :=
  isAffineVariety_zeroLocus_of_isPrime (graphIdeal_isPrime f hf)

/-- The variety carried by the principal open `D(f)`. -/
noncomputable abbrev PrincipalOpenVariety (f : MvPolynomial σ k) (hf : f ≠ 0) :
    Variety k :=
  Variety.ofQuasiAffine (principalOpen_isQuasiAffineVariety f hf)

/-- The affine graph hypersurface `Z(t * f - 1)`. -/
noncomputable abbrev GraphVariety (f : MvPolynomial σ k) (hf : f ≠ 0) : Variety k :=
  Variety.ofQuasiAffine (graph_isAffineVariety f hf).isQuasiAffineVariety

/-- Projection from the graph hypersurface to `D(f)`. -/
def graphProjectionMap (f : MvPolynomial σ k) (hf : f ≠ 0) :
    (GraphVariety f hf).carrier → (PrincipalOpenVariety f hf).carrier :=
  fun x => ⟨fun i => x.1 (some i), by
    change eval (x.1 ∘ some) f ≠ 0
    have hx := x.2 (graphPolynomial f)
      (Ideal.subset_span (Set.mem_singleton (graphPolynomial f)))
    simp [graphPolynomial, MvPolynomial.eval_rename] at hx
    intro hz
    rw [hz] at hx
    simp at hx⟩

/-- The coordinates of graph projection are regular. -/
theorem graphProjection_coords_regular (f : MvPolynomial σ k) (hf : f ≠ 0) :
    ∀ i, (GraphVariety f hf).IsGlobalRegular
      (fun x => (graphProjectionMap f hf x).1 i) := by
  intro i
  change IsRegularVia
    (openIota (⊤ : Opens (zeroLocus k (graphIdeal f))))
    (fun x => x.1.1 (some i))
  simpa only [openIota, MvPolynomial.eval_X] using
    (isRegularVia_eval
      (openIota (⊤ : Opens (zeroLocus k (graphIdeal f))))
      (MvPolynomial.X (some i)))

/-- Projection from the graph hypersurface to the principal open, as a
morphism of varieties. -/
noncomputable def graphProjection (f : MvPolynomial σ k) (hf : f ≠ 0) :
    VarietyHom (GraphVariety f hf) (PrincipalOpenVariety f hf) :=
  Classical.choose ((exists_varietyHom_iff_coords_regular
    (principalOpen_isQuasiAffineVariety f hf) (graphProjectionMap f hf)).2
      (graphProjection_coords_regular f hf))

theorem graphProjection_toFun (f : MvPolynomial σ k) (hf : f ≠ 0) :
    (graphProjection f hf).toFun = graphProjectionMap f hf :=
  Classical.choose_spec ((exists_varietyHom_iff_coords_regular
    (principalOpen_isQuasiAffineVariety f hf) (graphProjectionMap f hf)).2
      (graphProjection_coords_regular f hf))

/-- The inverse point map `x ↦ (1 / f(x), x)` from `D(f)` to the graph
hypersurface. -/
noncomputable def graphInverseMap (f : MvPolynomial σ k) (hf : f ≠ 0) :
    (PrincipalOpenVariety f hf).carrier → (GraphVariety f hf).carrier :=
  fun x => ⟨fun i => match i with
      | none => (eval x.1 f)⁻¹
      | some j => x.1 j,
    by
      rw [graphIdeal, MvPolynomial.zeroLocus_span]
      intro p hp
      rw [Set.mem_singleton_iff.mp hp]
      rw [MvPolynomial.aeval_eq_eval]
      simp only [graphPolynomial, MvPolynomial.eval_sub,
        MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_rename,
        map_one]
      have hfun :
          ((fun i : Option σ => match i with
            | none => (eval x.1 f)⁻¹
            | some j => x.1 j) ∘ some) = x.1 := by
        rfl
      rw [hfun]
      have hxne : eval x.1 f ≠ 0 := x.2
      exact sub_eq_zero.mpr (inv_mul_cancel₀ hxne)⟩

/-- The coordinates of the inverse graph map are regular on `D(f)`. -/
theorem graphInverse_coords_regular (f : MvPolynomial σ k) (hf : f ≠ 0) :
    ∀ i, (PrincipalOpenVariety f hf).IsGlobalRegular
      (fun x => (graphInverseMap f hf x).1 i) := by
  intro i
  cases i with
  | none =>
      change IsRegularVia
        (openIota (⊤ : Opens (principalOpen f)))
        (fun x => (eval x.1.1 f)⁻¹)
      have hreg := (isRegularVia_eval
        (openIota (⊤ : Opens (principalOpen f))) f).inv
          (fun x => x.1.2)
      have hfun : (fun x : (⊤ : Opens (principalOpen f)) => (eval x.1.1 f)⁻¹) =
          (fun x : (⊤ : Opens (principalOpen f)) => eval x.1.1 f)⁻¹ := by
        funext x
        simp
      rw [hfun]
      simpa only [openIota] using hreg
  | some i =>
      change IsRegularVia
        (openIota (⊤ : Opens (principalOpen f)))
        (fun x => x.1.1 i)
      simpa only [openIota, MvPolynomial.eval_X] using
        (isRegularVia_eval
          (openIota (⊤ : Opens (principalOpen f))) (MvPolynomial.X i))

/-- The inverse graph map is a morphism. -/
noncomputable def graphInverse (f : MvPolynomial σ k) (hf : f ≠ 0) :
    VarietyHom (PrincipalOpenVariety f hf) (GraphVariety f hf) :=
  Classical.choose ((exists_varietyHom_iff_coords_regular
    (graph_isAffineVariety f hf).isQuasiAffineVariety (graphInverseMap f hf)).2
      (graphInverse_coords_regular f hf))

theorem graphInverse_toFun (f : MvPolynomial σ k) (hf : f ≠ 0) :
    (graphInverse f hf).toFun = graphInverseMap f hf :=
  Classical.choose_spec ((exists_varietyHom_iff_coords_regular
    (graph_isAffineVariety f hf).isQuasiAffineVariety (graphInverseMap f hf)).2
      (graphInverse_coords_regular f hf))

/-- **Hartshorne, Lemma 4.2.** Projection identifies the graph hypersurface
`Z(t * f - 1)` with the principal open `D(f)`. Consequently `D(f)` is affine. -/
theorem graphProjection_isIso (f : MvPolynomial σ k) (hf : f ≠ 0) :
    (graphProjection f hf).IsIso := by
  refine ⟨graphInverse f hf, ?_, ?_⟩
  · apply VarietyHom.ext
    funext x
    apply Subtype.ext
    funext i
    rw [VarietyHom.comp_apply, graphInverse_toFun, graphProjection_toFun]
    cases i with
    | some i => rfl
    | none =>
        have hx := x.2 (graphPolynomial f)
          (Ideal.subset_span (Set.mem_singleton (graphPolynomial f)))
        simp [graphPolynomial, MvPolynomial.eval_rename] at hx
        have hmul : x.1 none * eval (x.1 ∘ some) f = 1 := sub_eq_zero.mp hx
        exact inv_eq_of_mul_eq_one_left hmul
  · apply VarietyHom.ext
    funext x
    apply Subtype.ext
    funext i
    rw [VarietyHom.comp_apply, graphProjection_toFun, graphInverse_toFun]
    rfl

end Hartshorne
