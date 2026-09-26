/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Finiteness of Frobenius on affine algebras

Over a perfect field of positive characteristic, a finite-type algebra is
finite over its subalgebra of `p ^ e`-th powers.  We package both that image
subalgebra and the equivalent statement that the iterated Frobenius ring
homomorphism is finite.

The definitions include the degenerate one-element algebra.  In that case the
power map is the unique ring endomorphism; otherwise the algebra inherits the
base field's exponential characteristic and the map is Mathlib's iterated
Frobenius.
-/

namespace Hartshorne

noncomputable section

universe u v

variable (k : Type u) (A : Type v) [Field k] [PerfectField k]
  [CommRing A] [Algebra k A]
  (p e : ℕ) [Fact p.Prime] [CharP k p]

/-- The `p ^ e`-power endomorphism of an algebra over a perfect field of
characteristic `p`.

For a nontrivial algebra this is `iterateFrobenius A p e`.  The separate
subsingleton branch keeps the construction available for the zero algebra,
where no `CharP A p` instance can exist for prime `p`. -/
def frobeniusPowerHom : A →+* A := by
  classical
  by_cases hA : Nontrivial A
  · let _ : Nontrivial A := hA
    let _ : ExpChar A p :=
      expChar_of_injective_algebraMap (algebraMap k A).injective p
    exact iterateFrobenius A p e
  · let _ : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    exact
      { toFun := fun x => x ^ p ^ e
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ }

omit [PerfectField k] in
@[simp]
theorem frobeniusPowerHom_apply (x : A) :
    frobeniusPowerHom k A p e x = x ^ p ^ e := by
  classical
  rw [frobeniusPowerHom]
  split_ifs with hA
  · rfl
  · let _ : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    rfl

omit [PerfectField k] in
/-- On an algebra carrying the expected exponential characteristic, the
everywhere-defined power map is Mathlib's iterated Frobenius. -/
theorem frobeniusPowerHom_eq_iterateFrobenius [ExpChar A p] :
    frobeniusPowerHom k A p e = iterateFrobenius A p e := by
  ext x
  rw [frobeniusPowerHom_apply, iterateFrobenius_def]

/-- The subalgebra `A^(p^e)` of `p ^ e`-th powers in `A`.

Perfection of the base field ensures that the image of its algebra map is
contained in the power image, so the range is a `k`-subalgebra rather than only
a subring. -/
def frobeniusPowerSubalgebra : Subalgebra k A where
  __ := (frobeniusPowerHom k A p e).range
  algebraMap_mem' c := by
    let _ : ExpChar k p := ExpChar.prime Fact.out
    obtain ⟨d, hd⟩ := (bijective_iterateFrobenius k p e).surjective c
    refine ⟨algebraMap k A d, ?_⟩
    rw [frobeniusPowerHom_apply, ← map_pow, ← iterateFrobenius_def, hd]

@[simp]
theorem mem_frobeniusPowerSubalgebra_iff (x : A) :
    x ∈ frobeniusPowerSubalgebra k A p e ↔
      ∃ y : A, y ^ p ^ e = x := by
  change x ∈ (frobeniusPowerHom k A p e).range ↔ _
  rw [RingHom.mem_range]
  simp only [frobeniusPowerHom_apply]

/-- For a nontrivial algebra, the power subalgebra has the iterated Frobenius
range as its underlying subring. -/
theorem frobeniusPowerSubalgebra_toSubring_eq_range [ExpChar A p] :
    (frobeniusPowerSubalgebra k A p e).toSubring =
      (iterateFrobenius A p e).range := by
  ext x
  change x ∈ (frobeniusPowerHom k A p e).range ↔
    x ∈ (iterateFrobenius A p e).range
  rw [RingHom.mem_range, RingHom.mem_range]
  simp only [frobeniusPowerHom_apply, iterateFrobenius_def]

/-- A finite-type algebra over a perfect field is finite as a module over its
subalgebra of `p ^ e`-th powers. -/
theorem moduleFinite_frobeniusPowerSubalgebra [Algebra.FiniteType k A] :
    Module.Finite (frobeniusPowerSubalgebra k A p e) A := by
  let S := frobeniusPowerSubalgebra k A p e
  let _ : Algebra.FiniteType S A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k S A
  have hIntegral : Algebra.IsIntegral S A := ⟨fun x => by
    apply IsIntegral.of_pow
      (pow_pos (show 0 < p from (Fact.out : Nat.Prime p).pos) e)
    let y : S :=
      ⟨x ^ p ^ e, (mem_frobeniusPowerSubalgebra_iff k A p e _).2 ⟨x, rfl⟩⟩
    change IsIntegral S (algebraMap S A y)
    exact isIntegral_algebraMap⟩
  exact hIntegral.finite

/-- The iterated Frobenius endomorphism is finite.  Unfolding
`RingHom.Finite` gives the scalar-restriction form `Module.Finite A A` for the
algebra structure induced by `frobeniusPowerHom`. -/
theorem frobeniusPowerHom_finite [Algebra.FiniteType k A] :
    (frobeniusPowerHom k A p e).Finite := by
  let S := frobeniusPowerSubalgebra k A p e
  let f : A →+* S :=
    (frobeniusPowerHom k A p e).codRestrict S fun x =>
      (mem_frobeniusPowerSubalgebra_iff k A p e _).2
        ⟨x, (frobeniusPowerHom_apply k A p e x).symm⟩
  have hf : f.Finite := RingHom.Finite.of_surjective f fun y => by
    obtain ⟨x, hx⟩ :=
      (mem_frobeniusPowerSubalgebra_iff k A p e y).1 y.property
    refine ⟨x, Subtype.ext ?_⟩
    exact (frobeniusPowerHom_apply k A p e x).trans hx
  have hι : S.val.toRingHom.Finite := by
    rw [show S.val.toRingHom = algebraMap S A from rfl,
      RingHom.finite_algebraMap]
    exact moduleFinite_frobeniusPowerSubalgebra k A p e
  have hcomp := hι.comp hf
  convert hcomp using 1
  ext x
  rfl

/-- The usual iterated Frobenius is finite whenever the algebra carries the
base field's exponential characteristic. -/
theorem iterateFrobenius_finite [ExpChar A p] [Algebra.FiniteType k A] :
    (iterateFrobenius A p e).Finite := by
  rw [← frobeniusPowerHom_eq_iterateFrobenius k A p e]
  exact frobeniusPowerHom_finite k A p e

end

end Hartshorne
