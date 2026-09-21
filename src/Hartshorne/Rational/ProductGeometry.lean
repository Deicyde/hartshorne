/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.SegreEmbedding

/-!
# Projective geometry of products

Hartshorne, *Algebraic Geometry*, I.3, Exercise 3.16(a),(b) (p. 22).

Products are embedded in projective space by the Segre map.  The factor
equations lift to homogeneous equations in the Segre coordinates, proving
closedness for projective factors.  Irreducibility uses separate continuity of
the Segre map and a closed-cover argument; it never equips the source pair with
the (incorrect here) product topology.

## Main results

* `Hartshorne.isProjVariety_segreProduct`
* `Hartshorne.isQuasiProjVariety_segreProduct`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k] {σ τ : Type*}

/-- Substitute a fixed right vector into the Segre coordinates. -/
noncomputable def segreLeftSliceRingHom (y : τ → k) :
    MvPolynomial (σ × τ) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval fun ij => C (y ij.2) * X ij.1

/-- Substitute a fixed left vector into the Segre coordinates. -/
noncomputable def segreRightSliceRingHom (x : σ → k) :
    MvPolynomial (σ × τ) k →ₐ[k] MvPolynomial τ k :=
  MvPolynomial.aeval fun ij => C (x ij.1) * X ij.2

theorem segreLeftSliceRingHom_isHomogeneous {y : τ → k}
    {f : MvPolynomial (σ × τ) k} {n : ℕ} (hf : f.IsHomogeneous n) :
    (segreLeftSliceRingHom y f).IsHomogeneous n := by
  change (MvPolynomial.aeval (fun ij : σ × τ => C (y ij.2) * X ij.1) f).IsHomogeneous n
  simpa using hf.aeval (fun ij : σ × τ => C (y ij.2) * X ij.1)
    (fun ij : σ × τ => isHomogeneous_C_mul_X (y ij.2) ij.1)

theorem segreRightSliceRingHom_isHomogeneous {x : σ → k}
    {f : MvPolynomial (σ × τ) k} {n : ℕ} (hf : f.IsHomogeneous n) :
    (segreRightSliceRingHom x f).IsHomogeneous n := by
  change (MvPolynomial.aeval (fun ij : σ × τ => C (x ij.1) * X ij.2) f).IsHomogeneous n
  simpa using hf.aeval (fun ij : σ × τ => C (x ij.1) * X ij.2)
    (fun ij : σ × τ => isHomogeneous_C_mul_X (x ij.1) ij.2)

theorem eval_segreLeftSliceRingHom (x : σ → k) (y : τ → k)
    (f : MvPolynomial (σ × τ) k) :
    eval x (segreLeftSliceRingHom y f) = eval (segreVector x y) f := by
  rw [segreLeftSliceRingHom, aeval_def, eval_eval₂]
  simp only [eval_mul, eval_C, eval_X]
  have hc : (eval x).comp (algebraMap k (MvPolynomial σ k)) = RingHom.id k := by
    ext c
    simp
  rw [hc, eval₂_id]
  have hfun : (fun ij : σ × τ => y ij.2 * x ij.1) = segreVector x y := by
    funext ij
    exact mul_comm _ _
  rw [hfun]

theorem eval_segreRightSliceRingHom (x : σ → k) (y : τ → k)
    (f : MvPolynomial (σ × τ) k) :
    eval y (segreRightSliceRingHom x f) = eval (segreVector x y) f := by
  rw [segreRightSliceRingHom, aeval_def, eval_eval₂]
  simp only [eval_mul, eval_C, eval_X]
  have hc : (eval y).comp (algebraMap k (MvPolynomial τ k)) = RingHom.id k := by
    ext c
    simp
  rw [hc, eval₂_id]
  rfl

theorem homogeneousVanish_segreMap_iff_leftSlice
    {f : MvPolynomial (σ × τ) k} {n : ℕ} (hf : f.IsHomogeneous n)
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ) :
    HomogeneousVanish f (segreMap P Q) ↔
      HomogeneousVanish (segreLeftSliceRingHom Q.rep f) P := by
  unfold segreMap
  rw [homogeneousVanish_iff_of_isHomogeneous hf
    (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)]
  change eval (segreVector P.rep Q.rep) f = 0 ↔
    eval P.rep (segreLeftSliceRingHom Q.rep f) = 0
  rw [eval_segreLeftSliceRingHom]

theorem homogeneousVanish_segreMap_iff_rightSlice
    {f : MvPolynomial (σ × τ) k} {n : ℕ} (hf : f.IsHomogeneous n)
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ) :
    HomogeneousVanish f (segreMap P Q) ↔
      HomogeneousVanish (segreRightSliceRingHom P.rep f) Q := by
  unfold segreMap
  rw [homogeneousVanish_iff_of_isHomogeneous hf
    (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)]
  change eval (segreVector P.rep Q.rep) f = 0 ↔
    eval Q.rep (segreRightSliceRingHom P.rep f) = 0
  rw [eval_segreRightSliceRingHom]

def segreLeftSlicePolynomials (y : τ → k)
    (T : Set (MvPolynomial (σ × τ) k)) : Set (MvPolynomial σ k) :=
  segreLeftSliceRingHom y '' T

def segreRightSlicePolynomials (x : σ → k)
    (T : Set (MvPolynomial (σ × τ) k)) : Set (MvPolynomial τ k) :=
  segreRightSliceRingHom x '' T

theorem isHomogeneousSet_segreLeftSlicePolynomials {y : τ → k}
    {T : Set (MvPolynomial (σ × τ) k)} (hT : IsHomogeneousSet T) :
    IsHomogeneousSet (segreLeftSlicePolynomials y T) := by
  rintro g ⟨f, hf, rfl⟩
  obtain ⟨n, hn⟩ := hT f hf
  exact ⟨n, segreLeftSliceRingHom_isHomogeneous hn⟩

theorem isHomogeneousSet_segreRightSlicePolynomials {x : σ → k}
    {T : Set (MvPolynomial (σ × τ) k)} (hT : IsHomogeneousSet T) :
    IsHomogeneousSet (segreRightSlicePolynomials x T) := by
  rintro g ⟨f, hf, rfl⟩
  obtain ⟨n, hn⟩ := hT f hf
  exact ⟨n, segreRightSliceRingHom_isHomogeneous hn⟩

theorem preimage_projZeroSet_segreMap_left (Q : ProjectiveSpace k τ)
    {T : Set (MvPolynomial (σ × τ) k)} (hT : IsHomogeneousSet T) :
    (fun P : ProjectiveSpace k σ => segreMap P Q) ⁻¹' projZeroSet T =
      projZeroSet (segreLeftSlicePolynomials Q.rep T) := by
  ext P
  constructor
  · intro hP g hg
    obtain ⟨f, hf, rfl⟩ := hg
    obtain ⟨n, hn⟩ := hT f hf
    exact (homogeneousVanish_segreMap_iff_leftSlice hn P Q).1 (hP f hf)
  · intro hP f hf
    obtain ⟨n, hn⟩ := hT f hf
    exact (homogeneousVanish_segreMap_iff_leftSlice hn P Q).2
      (hP (segreLeftSliceRingHom Q.rep f) ⟨f, hf, rfl⟩)

theorem preimage_projZeroSet_segreMap_right (P : ProjectiveSpace k σ)
    {T : Set (MvPolynomial (σ × τ) k)} (hT : IsHomogeneousSet T) :
    (fun Q : ProjectiveSpace k τ => segreMap P Q) ⁻¹' projZeroSet T =
      projZeroSet (segreRightSlicePolynomials P.rep T) := by
  ext Q
  constructor
  · intro hQ g hg
    obtain ⟨f, hf, rfl⟩ := hg
    obtain ⟨n, hn⟩ := hT f hf
    exact (homogeneousVanish_segreMap_iff_rightSlice hn P Q).1 (hQ f hf)
  · intro hQ f hf
    obtain ⟨n, hn⟩ := hT f hf
    exact (homogeneousVanish_segreMap_iff_rightSlice hn P Q).2
      (hQ (segreRightSliceRingHom P.rep f) ⟨f, hf, rfl⟩)

theorem continuous_segreMap_left (Q : ProjectiveSpace k τ) :
    Continuous (fun P : ProjectiveSpace k σ => segreMap P Q) := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_isProjAlgebraicSet.1 hZ
  rw [preimage_projZeroSet_segreMap_left Q hT]
  exact isClosed_iff_isProjAlgebraicSet.2
    ⟨_, isHomogeneousSet_segreLeftSlicePolynomials hT, rfl⟩

theorem continuous_segreMap_right (P : ProjectiveSpace k σ) :
    Continuous (fun Q : ProjectiveSpace k τ => segreMap P Q) := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_isProjAlgebraicSet.1 hZ
  rw [preimage_projZeroSet_segreMap_right P hT]
  exact isClosed_iff_isProjAlgebraicSet.2
    ⟨_, isHomogeneousSet_segreRightSlicePolynomials hT, rfl⟩

/-- Separate continuity is enough for the image of two irreducible spaces to
be irreducible. No product topology is used on the source pair. -/
theorem isIrreducible_range_prod_of_separatelyContinuous
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [IrreducibleSpace A] [IrreducibleSpace B]
    (f : A → B → C) (hleft : ∀ b, Continuous fun a => f a b)
    (hright : ∀ a, Continuous fun b => f a b) :
    IsIrreducible (Set.range fun p : A × B => f p.1 p.2) := by
  refine ⟨Set.range_nonempty _, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro C D hC hD hcover
  let AC : Set A := {a | ∀ b, f a b ∈ C}
  let AD : Set A := {a | ∀ b, f a b ∈ D}
  have hAC : IsClosed AC := by
    have hi : IsClosed (⋂ b : B, (fun a => f a b) ⁻¹' C) :=
      isClosed_iInter fun b => hC.preimage (hleft b)
    convert hi using 1
    ext a
    simp [AC]
  have hAD : IsClosed AD := by
    have hi : IsClosed (⋂ b : B, (fun a => f a b) ⁻¹' D) :=
      isClosed_iInter fun b => hD.preimage (hleft b)
    convert hi using 1
    ext a
    simp [AD]
  have hAcover : Set.univ ⊆ AC ∪ AD := by
    intro a ha
    have hBcover : Set.univ ⊆
        (fun b => f a b) ⁻¹' C ∪ (fun b => f a b) ⁻¹' D := by
      intro b hb
      exact hcover ⟨(a, b), rfl⟩
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp
        (PreirreducibleSpace.isPreirreducible_univ (X := B)) _ _
        (hC.preimage (hright a)) (hD.preimage (hright a)) hBcover with h | h
    · exact Or.inl (fun b => h (Set.mem_univ b))
    · exact Or.inr (fun b => h (Set.mem_univ b))
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp
      (PreirreducibleSpace.isPreirreducible_univ (X := A)) AC AD hAC hAD hAcover with h | h
  · left
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact h (Set.mem_univ a) b
  · right
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact h (Set.mem_univ a) b

/-- Equations on the left factor, placed in every column of the Segre matrix. -/
def segreLeftPolynomials (T : Set (MvPolynomial σ k)) :
    Set (MvPolynomial (σ × τ) k) :=
  {g | ∃ f ∈ T, ∃ j : τ, rename (fun i => (i, j)) f = g}

/-- Equations on the right factor, placed in every row of the Segre matrix. -/
def segreRightPolynomials (T : Set (MvPolynomial τ k)) :
    Set (MvPolynomial (σ × τ) k) :=
  {g | ∃ f ∈ T, ∃ i : σ, rename (fun j => (i, j)) f = g}

theorem isHomogeneousSet_segreLeftPolynomials {T : Set (MvPolynomial σ k)}
    (hT : IsHomogeneousSet T) :
    IsHomogeneousSet (segreLeftPolynomials (τ := τ) T) := by
  rintro g ⟨f, hf, j, rfl⟩
  obtain ⟨n, hn⟩ := hT f hf
  exact ⟨n, hn.rename_isHomogeneous⟩

theorem isHomogeneousSet_segreRightPolynomials {T : Set (MvPolynomial τ k)}
    (hT : IsHomogeneousSet T) :
    IsHomogeneousSet (segreRightPolynomials (σ := σ) T) := by
  rintro g ⟨f, hf, i, rfl⟩
  obtain ⟨n, hn⟩ := hT f hf
  exact ⟨n, hn.rename_isHomogeneous⟩

/-- The ambient closed locus saying that the left Segre factor lies in `X`. -/
def segreLeftLocus (X : Set (ProjectiveSpace k σ)) :
    Set (ProjectiveSpace k (σ × τ)) :=
  projZeroSet (segreLeftPolynomials (τ := τ) (homogeneousVanishingSet X))

/-- The ambient closed locus saying that the right Segre factor lies in `Y`. -/
def segreRightLocus (Y : Set (ProjectiveSpace k τ)) :
    Set (ProjectiveSpace k (σ × τ)) :=
  projZeroSet (segreRightPolynomials (σ := σ) (homogeneousVanishingSet Y))

theorem isProjAlgebraicSet_segreLeftLocus (X : Set (ProjectiveSpace k σ)) :
    IsProjAlgebraicSet (segreLeftLocus (τ := τ) X) := by
  exact ⟨_, isHomogeneousSet_segreLeftPolynomials
    (isHomogeneousSet_homogeneousVanishingSet X), rfl⟩

theorem isProjAlgebraicSet_segreRightLocus (Y : Set (ProjectiveSpace k τ)) :
    IsProjAlgebraicSet (segreRightLocus (σ := σ) Y) := by
  exact ⟨_, isHomogeneousSet_segreRightPolynomials
    (isHomogeneousSet_homogeneousVanishingSet Y), rfl⟩

theorem isClosed_segreLeftLocus (X : Set (ProjectiveSpace k σ)) :
    IsClosed (segreLeftLocus (τ := τ) X) :=
  isClosed_iff_isProjAlgebraicSet.2 (isProjAlgebraicSet_segreLeftLocus X)

theorem isClosed_segreRightLocus (Y : Set (ProjectiveSpace k τ)) :
    IsClosed (segreRightLocus (σ := σ) Y) :=
  isClosed_iff_isProjAlgebraicSet.2 (isProjAlgebraicSet_segreRightLocus Y)

theorem eval_segreVector_rename_left {f : MvPolynomial σ k} {n : ℕ}
    (hf : f.IsHomogeneous n) (x : σ → k) (y : τ → k) (j : τ) :
    eval (segreVector x y) (rename (fun i => (i, j)) f) =
      y j ^ n * eval x f := by
  rw [eval_rename]
  have hfun : segreVector x y ∘ (fun i => (i, j)) = y j • x := by
    funext i
    simp only [Function.comp_apply, segreVector, Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  rw [hfun, hf.eval_smul]

theorem eval_segreVector_rename_right {f : MvPolynomial τ k} {n : ℕ}
    (hf : f.IsHomogeneous n) (x : σ → k) (y : τ → k) (i : σ) :
    eval (segreVector x y) (rename (fun j => (i, j)) f) =
      x i ^ n * eval y f := by
  rw [eval_rename]
  have hfun : segreVector x y ∘ (fun j => (i, j)) = x i • y := by
    funext j
    simp only [Function.comp_apply, segreVector, Pi.smul_apply, smul_eq_mul]
  rw [hfun, hf.eval_smul]

theorem homogeneousVanish_rename_left_segreMap {f : MvPolynomial σ k} {n : ℕ}
    (hf : f.IsHomogeneous n) (P : ProjectiveSpace k σ)
    (Q : ProjectiveSpace k τ) (j : τ) :
    HomogeneousVanish (rename (fun i => (i, j)) f) (segreMap P Q) ↔
      Q.rep j ^ n * eval P.rep f = 0 := by
  unfold segreMap
  rw [homogeneousVanish_iff_of_isHomogeneous hf.rename_isHomogeneous
    (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)]
  rw [eval_segreVector_rename_left hf]

theorem homogeneousVanish_rename_right_segreMap {f : MvPolynomial τ k} {n : ℕ}
    (hf : f.IsHomogeneous n) (P : ProjectiveSpace k σ)
    (Q : ProjectiveSpace k τ) (i : σ) :
    HomogeneousVanish (rename (fun j => (i, j)) f) (segreMap P Q) ↔
      P.rep i ^ n * eval Q.rep f = 0 := by
  unfold segreMap
  rw [homogeneousVanish_iff_of_isHomogeneous hf.rename_isHomogeneous
    (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)]
  rw [eval_segreVector_rename_right hf]

theorem segreMap_mem_leftLocus_iff
    {X : Set (ProjectiveSpace k σ)} (hX : IsProjAlgebraicSet X)
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ) :
    segreMap P Q ∈ segreLeftLocus (τ := τ) X ↔ P ∈ X := by
  constructor
  · intro hP
    have hPX : P ∈ projZeroSet (homogeneousVanishingSet X) := by
      intro f hf
      obtain ⟨n, hfn⟩ := hf.1
      obtain ⟨j, hj⟩ := Function.ne_iff.mp Q.rep_nonzero
      have hvan := hP (rename (fun i => (i, j)) f)
        (show rename (fun i => (i, j)) f ∈
            segreLeftPolynomials (τ := τ) (homogeneousVanishingSet X) from
          ⟨f, hf, j, rfl⟩)
      rw [homogeneousVanish_rename_left_segreMap hfn] at hvan
      exact (mul_eq_zero.mp hvan).resolve_left (pow_ne_zero n hj)
    rwa [hX.projZeroSet_homogeneousVanishingSet] at hPX
  · intro hP g hg
    obtain ⟨f, hf, j, rfl⟩ := hg
    obtain ⟨n, hfn⟩ := hf.1
    rw [homogeneousVanish_rename_left_segreMap hfn]
    have hPX : P ∈ projZeroSet (homogeneousVanishingSet X) := by
      rwa [hX.projZeroSet_homogeneousVanishingSet]
    rw [show eval P.rep f = 0 from hPX f hf, mul_zero]

theorem segreMap_mem_rightLocus_iff
    {Y : Set (ProjectiveSpace k τ)} (hY : IsProjAlgebraicSet Y)
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ) :
    segreMap P Q ∈ segreRightLocus (σ := σ) Y ↔ Q ∈ Y := by
  constructor
  · intro hQ
    have hQY : Q ∈ projZeroSet (homogeneousVanishingSet Y) := by
      intro f hf
      obtain ⟨n, hfn⟩ := hf.1
      obtain ⟨i, hi⟩ := Function.ne_iff.mp P.rep_nonzero
      have hvan := hQ (rename (fun j => (i, j)) f)
        (show rename (fun j => (i, j)) f ∈
            segreRightPolynomials (σ := σ) (homogeneousVanishingSet Y) from
          ⟨f, hf, i, rfl⟩)
      rw [homogeneousVanish_rename_right_segreMap hfn] at hvan
      exact (mul_eq_zero.mp hvan).resolve_left (pow_ne_zero n hi)
    rwa [hY.projZeroSet_homogeneousVanishingSet] at hQY
  · intro hQ g hg
    obtain ⟨f, hf, i, rfl⟩ := hg
    obtain ⟨n, hfn⟩ := hf.1
    rw [homogeneousVanish_rename_right_segreMap hfn]
    have hQY : Q ∈ projZeroSet (homogeneousVanishingSet Y) := by
      rwa [hY.projZeroSet_homogeneousVanishingSet]
    rw [show eval Q.rep f = 0 from hQY f hf, mul_zero]

/-- The product subset, always regarded with the topology induced through the
Segre embedding rather than with the topological product topology. -/
def segreProduct (X : Set (ProjectiveSpace k σ))
    (Y : Set (ProjectiveSpace k τ)) : Set (ProjectiveSpace k (σ × τ)) :=
  segreEmbedding (k := k) '' (X ×ˢ Y)

theorem mem_segreProduct_iff {X : Set (ProjectiveSpace k σ)}
    {Y : Set (ProjectiveSpace k τ)} {R : ProjectiveSpace k (σ × τ)} :
    R ∈ segreProduct X Y ↔
      ∃ P ∈ X, ∃ Q ∈ Y, segreMap P Q = R := by
  constructor
  · rintro ⟨⟨P, Q⟩, ⟨hP, hQ⟩, rfl⟩
    exact ⟨P, hP, Q, hQ, rfl⟩
  · rintro ⟨P, hP, Q, hQ, rfl⟩
    exact ⟨(P, Q), ⟨hP, hQ⟩, rfl⟩

theorem isIrreducible_segreProduct
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsIrreducible X) (hY : IsIrreducible Y) :
    IsIrreducible (segreProduct X Y) := by
  let _ : IrreducibleSpace X := Subtype.irreducibleSpace hX
  let _ : IrreducibleSpace Y := Subtype.irreducibleSpace hY
  have hirr := isIrreducible_range_prod_of_separatelyContinuous
    (fun P : X => fun Q : Y => segreMap P.1 Q.1)
    (fun Q => (continuous_segreMap_left Q.1).comp continuous_subtype_val)
    (fun P => (continuous_segreMap_right P.1).comp continuous_subtype_val)
  have hrange :
      Set.range (fun PQ : X × Y => segreMap PQ.1.1 PQ.2.1) =
        segreProduct X Y := by
    ext R
    constructor
    · rintro ⟨⟨P, Q⟩, rfl⟩
      exact (mem_segreProduct_iff).2 ⟨P.1, P.2, Q.1, Q.2, rfl⟩
    · rw [mem_segreProduct_iff]
      rintro ⟨P, hP, Q, hQ, hR⟩
      exact ⟨(⟨P, hP⟩, ⟨Q, hQ⟩), hR⟩
  rw [hrange] at hirr
  exact hirr

theorem segreProduct_eq_range_inter_loci
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsProjAlgebraicSet X) (hY : IsProjAlgebraicSet Y) :
    segreProduct X Y =
      Set.range (segreEmbedding (k := k) (σ := σ) (τ := τ)) ∩
        segreLeftLocus (τ := τ) X ∩ segreRightLocus (σ := σ) Y := by
  ext R
  constructor
  · rw [mem_segreProduct_iff]
    rintro ⟨P, hP, Q, hQ, rfl⟩
    exact ⟨⟨⟨(P, Q), rfl⟩,
      (segreMap_mem_leftLocus_iff hX P Q).2 hP⟩,
      (segreMap_mem_rightLocus_iff hY P Q).2 hQ⟩
  · rintro ⟨⟨⟨⟨P, Q⟩, rfl⟩, hP⟩, hQ⟩
    rw [mem_segreProduct_iff]
    exact ⟨P, (segreMap_mem_leftLocus_iff hX P Q).1 hP,
      Q, (segreMap_mem_rightLocus_iff hY P Q).1 hQ, rfl⟩

theorem isClosed_range_segreEmbedding :
    IsClosed (Set.range (segreEmbedding (k := k) (σ := σ) (τ := τ))) := by
  rw [range_segreEmbedding]
  exact isClosed_iff_isProjAlgebraicSet.2
    isProjAlgebraicSet_projZeroSet_segreIdeal

theorem isClosed_segreProduct
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsClosed X) (hY : IsClosed Y) :
    IsClosed (segreProduct X Y) := by
  rw [segreProduct_eq_range_inter_loci
    (isClosed_iff_isProjAlgebraicSet.1 hX)
    (isClosed_iff_isProjAlgebraicSet.1 hY)]
  exact (isClosed_range_segreEmbedding.inter
    (isClosed_segreLeftLocus X)).inter (isClosed_segreRightLocus Y)

theorem segreProduct_nonempty {X : Set (ProjectiveSpace k σ)}
    {Y : Set (ProjectiveSpace k τ)} (hX : X.Nonempty) (hY : Y.Nonempty) :
    (segreProduct X Y).Nonempty := by
  obtain ⟨P, hP⟩ := hX
  obtain ⟨Q, hQ⟩ := hY
  exact ⟨segreMap P Q, (mem_segreProduct_iff).2 ⟨P, hP, Q, hQ, rfl⟩⟩

/-- Once product irreducibility is available (the content inherited from
Exercise 3.15(a)), closedness upgrades immediately to projectivity. -/
theorem isProjVariety_segreProduct_of_isIrreducible
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsProjVariety X) (hY : IsProjVariety Y)
    (hirr : IsIrreducible (segreProduct X Y)) :
    IsProjVariety (segreProduct X Y) :=
  ⟨hirr, isClosed_segreProduct hX.2 hY.2⟩

theorem isProjVariety_segreProduct
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsProjVariety X) (hY : IsProjVariety Y) :
    IsProjVariety (segreProduct X Y) :=
  ⟨isIrreducible_segreProduct hX.1 hY.1,
    isClosed_segreProduct hX.2 hY.2⟩

theorem segreProduct_inter_open_eq
    {V U : Set (ProjectiveSpace k σ)} {W T : Set (ProjectiveSpace k τ)}
    (hU : IsOpen U) (hT : IsOpen T) :
    segreProduct (V ∩ U) (W ∩ T) =
      segreProduct V W ∩
        ((segreLeftLocus (τ := τ) Uᶜ)ᶜ ∩
          (segreRightLocus (σ := σ) Tᶜ)ᶜ) := by
  have hUc : IsProjAlgebraicSet Uᶜ :=
    isClosed_iff_isProjAlgebraicSet.1 hU.isClosed_compl
  have hTc : IsProjAlgebraicSet Tᶜ :=
    isClosed_iff_isProjAlgebraicSet.1 hT.isClosed_compl
  ext R
  constructor
  · rw [mem_segreProduct_iff]
    rintro ⟨P, ⟨hPV, hPU⟩, Q, ⟨hQW, hQT⟩, rfl⟩
    refine ⟨(mem_segreProduct_iff).2 ⟨P, hPV, Q, hQW, rfl⟩, ?_, ?_⟩
    · simpa [segreMap_mem_leftLocus_iff hUc P Q] using hPU
    · simpa [segreMap_mem_rightLocus_iff hTc P Q] using hQT
  · rintro ⟨hprod, hleft, hright⟩
    rw [mem_segreProduct_iff] at hprod ⊢
    obtain ⟨P, hPV, Q, hQW, rfl⟩ := hprod
    have hPU : P ∈ U := by
      simpa [segreMap_mem_leftLocus_iff hUc P Q] using hleft
    have hQT : Q ∈ T := by
      simpa [segreMap_mem_rightLocus_iff hTc P Q] using hright
    exact ⟨P, ⟨hPV, hPU⟩, Q, ⟨hQW, hQT⟩, rfl⟩

/-- Products of quasi-projective varieties are quasi-projective in the Segre
ambient projective space. -/
theorem isQuasiProjVariety_segreProduct
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y) :
    IsQuasiProjVariety (segreProduct X Y) := by
  obtain ⟨hXne, V, U, hV, hU, rfl⟩ := hX
  obtain ⟨hYne, W, T, hW, hT, rfl⟩ := hY
  refine ⟨segreProduct_nonempty hXne hYne,
    segreProduct V W,
    (segreLeftLocus (τ := τ) Uᶜ)ᶜ ∩
    (segreRightLocus (σ := σ) Tᶜ)ᶜ,
    isProjVariety_segreProduct hV hW,
    (isClosed_segreLeftLocus Uᶜ).isOpen_compl.inter
      (isClosed_segreRightLocus Tᶜ).isOpen_compl,
    segreProduct_inter_open_eq hU hT⟩

end Hartshorne
