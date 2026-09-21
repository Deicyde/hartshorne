/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Zariski
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Determinantal rank loci

Hartshorne, *Algebraic Geometry*, I.5, proof of Theorem 5.3 (p. 33).

For a finite matrix whose entries are polynomials, the locus where its
evaluation has rank less than `q` is the common zero set of its `q × q`
minors and is therefore Zariski closed.  The case `q = 0` is included: the
unique empty minor has determinant one, so the rank-drop locus is empty.

## Main results

* `Hartshorne.rank_lt_iff_forall_minors_eq_zero`: the rank/minor criterion.
* `Hartshorne.matrixRankDropLocus_eq_zeroSet`: the rank-drop locus is the
  common zero set of the polynomial minors.
* `Hartshorne.isClosed_matrixRankDropLocus`: the rank-drop locus is Zariski
  closed.
-/

open Matrix

namespace Hartshorne

/-- If a finite matrix over a field has rank at least `q`, it has a `q × q`
minor with nonzero determinant. -/
theorem exists_minor_det_ne_zero_of_le_rank
    {k : Type*} [Field k] {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n k) {q : ℕ} (h : q ≤ A.rank) :
    ∃ (r : Fin q → m) (c : Fin q → n), Function.Injective r ∧
      Function.Injective c ∧ (A.submatrix r c).det ≠ 0 := by
  classical
  have hcols :=
    Submodule.exists_fun_fin_finrank_span_eq k (Set.range A.col)
  rw [← A.rank_eq_finrank_span_cols] at hcols
  obtain ⟨v, hv_mem, -, hv_li⟩ := hcols
  let e : Fin q → Fin A.rank := Fin.castLE h
  choose c hc using fun i ↦ hv_mem (e i)
  have hc_inj : Function.Injective c := by
    intro i j hij
    apply (Fin.castLE_injective h)
    apply hv_li.injective
    rw [← hc i, ← hc j, hij]
  let B : Matrix m (Fin q) k := A.submatrix id c
  have hBcol : B.col = v ∘ e := by
    ext i j
    exact congrFun (hc i) j
  have hBli : LinearIndependent k B.col := by
    rw [hBcol]
    exact hv_li.comp e (Fin.castLE_injective h)
  have hBrank : B.rank = q := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hBli,
      Fintype.card_fin]
  have hrows :=
    Submodule.exists_fun_fin_finrank_span_eq k (Set.range B.row)
  rw [← B.rank_eq_finrank_span_row, hBrank] at hrows
  obtain ⟨w, hw_mem, -, hw_li⟩ := hrows
  choose r hr using hw_mem
  have hr_inj : Function.Injective r := by
    intro i j hij
    apply hw_li.injective
    rw [← hr i, ← hr j, hij]
  let C : Matrix (Fin q) (Fin q) k := B.submatrix r id
  have hCrow : C.row = w := by
    ext i j
    exact congrFun (hr i) j
  have hCunit : IsUnit C := by
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    rw [hCrow]
    exact hw_li
  have hCdet : C.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det C).mp hCunit).ne_zero
  exact ⟨r, c, hr_inj, hc_inj, by simpa [C, B] using hCdet⟩

/-- A finite matrix over a field has rank less than `q` exactly when every
`q × q` minor has zero determinant. -/
theorem rank_lt_iff_forall_minors_eq_zero
    {k : Type*} [Field k] {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n k) (q : ℕ) :
    A.rank < q ↔
      ∀ (r : Fin q → m) (c : Fin q → n), Function.Injective r →
        Function.Injective c → (A.submatrix r c).det = 0 := by
  constructor
  · intro h r c _ _
    by_contra hdet
    have hminor : (A.submatrix r c).rank = q := by
      simpa using Matrix.rank_of_det_ne_zero hdet
    have hq : q ≤ A.rank := hminor ▸ Matrix.rank_submatrix_le A r c
    exact (Nat.not_le_of_lt h) hq
  · intro h
    by_contra hnlt
    obtain ⟨r, c, hr, hc, hdet⟩ :=
      exists_minor_det_ne_zero_of_le_rank A (Nat.le_of_not_gt hnlt)
    exact hdet (h r c hr hc)

/-- The set of polynomial `q × q` minors of a matrix.  Rows and columns are
indexed injectively, so these are honest minors rather than submatrices with
repeated indices. -/
def determinantalMinors
    {k : Type*} [Field k] {σ m n : Type*}
    (M : Matrix m n (MvPolynomial σ k)) (q : ℕ) :
    Set (MvPolynomial σ k) :=
  {f | ∃ (r : Fin q → m) (c : Fin q → n), Function.Injective r ∧
    Function.Injective c ∧ f = (M.submatrix r c).det}

/-- The only `0 × 0` minor is the empty determinant, namely one. -/
@[simp]
theorem determinantalMinors_zero
    {k : Type*} [Field k] {σ m n : Type*}
    (M : Matrix m n (MvPolynomial σ k)) :
    determinantalMinors M 0 = {1} := by
  classical
  ext f
  constructor
  · rintro ⟨r, c, -, -, rfl⟩
    simp
  · intro hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    exact ⟨Fin.elim0, Fin.elim0, fun i ↦ Fin.elim0 i,
      fun i ↦ Fin.elim0 i, by simp⟩

/-- Evaluation of a polynomial minor is the corresponding minor of the
evaluated matrix. -/
theorem eval_determinantalMinor
    {k : Type*} [Field k] {σ m n q : Type*} [Fintype q] [DecidableEq q]
    (M : Matrix m n (MvPolynomial σ k)) (P : σ → k) (r : q → m) (c : q → n) :
    MvPolynomial.eval P ((M.submatrix r c).det) =
      ((M.map (MvPolynomial.eval P)).submatrix r c).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map]

/-- The points where a polynomial matrix has rank strictly less than `q`. -/
def matrixRankDropLocus
    {k : Type*} [Field k] {σ m n : Type*} [Fintype n]
    (M : Matrix m n (MvPolynomial σ k)) (q : ℕ) : Set (σ → k) :=
  {P | (M.map (MvPolynomial.eval P)).rank < q}

/-- The rank-drop locus of a polynomial matrix is exactly the common zero set
of its `q × q` minors. -/
theorem matrixRankDropLocus_eq_zeroSet
    {k : Type*} [Field k] {σ m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n (MvPolynomial σ k)) (q : ℕ) :
    matrixRankDropLocus M q = zeroSet (determinantalMinors M q) := by
  ext P
  simp only [matrixRankDropLocus, Set.mem_ofPred_eq, mem_zeroSet_iff,
    determinantalMinors]
  rw [rank_lt_iff_forall_minors_eq_zero]
  constructor
  · intro h f
    rintro ⟨r, c, hr, hc, rfl⟩
    rw [eval_determinantalMinor]
    exact h r c hr hc
  · intro h r c hr hc
    rw [← eval_determinantalMinor]
    exact h _ ⟨r, c, hr, hc, rfl⟩

/-- The locus on which a polynomial matrix has rank less than `q` is Zariski
closed. -/
theorem isClosed_matrixRankDropLocus
    {k : Type*} [Field k] {σ m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n (MvPolynomial σ k)) (q : ℕ) :
    @IsClosed (σ → k) Hartshorne.zariskiTopology (matrixRankDropLocus M q) := by
  rw [matrixRankDropLocus_eq_zeroSet]
  exact isClosed_zeroSet _

/-- There is no matrix of rank strictly below zero.  Equivalently, the empty
minor cuts out the empty set because its determinant is one. -/
@[simp]
theorem matrixRankDropLocus_zero
    {k : Type*} [Field k] {σ m n : Type*} [Fintype n]
    (M : Matrix m n (MvPolynomial σ k)) :
    matrixRankDropLocus M 0 = ∅ := by
  ext P
  simp [matrixRankDropLocus]

end Hartshorne
