/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.DirectSum.Basic
import Hartshorne.Intersection.RationalEquivalence

/-!
# The graded Chow groups

Hartshorne, *Algebraic Geometry*, Appendix A.1 (p. 426).

Let `X` be a variety: an integral scheme, separated and of finite type over a field `k`, of
dimension `n`. The Chow group of codimension-`r` cycles is the quotient
`A^r(X) = Z^r(X) / Rat^r(X)` of the codimension-`r` cycles by the rational-equivalence subgroup
(`chowGroup`), and the graded Chow group is the direct sum `A(X) = ⨁_{r=0}^{n} A^r(X)`
(`gradedChowGroup`), graded by its summands. At this stage `A(X)` is only a graded abelian group.

Since `X` is irreducible, the only codimension-zero cycles are the multiples of `[X]`, and there
are no codimension `-1` subvarieties, so `A^0(X) ≃ ℤ` (`chowGroupZeroEquivInt`), the isomorphism
taking the class of a cycle to its coefficient at the generic point
(`chowGroupZeroEquivInt_mk`). There are no subvarieties of codimension larger than `n`, so
`A^r(X) = 0` for `r > n` (`subsingleton_chowGroup_of_lt`).
-/

namespace Hartshorne

open AlgebraicGeometry Order TopologicalSpace

universe u

/-- The codimension of the closure of a point is the coheight of that closure among the
irreducible closed subsets. -/
private theorem codim_closure_singleton_eq_coheight_irreducibleCloseds {X : Type*}
    [TopologicalSpace X] (x : X) :
    codim (closure ({x} : Set X)) =
      coheight (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds X) := by
  apply le_antisymm
  · exact iInf₂_le (f := fun (W : IrreducibleCloseds X) (_ : (W : Set X) ⊆ closure {x}) ↦
      coheight W) _ Set.Subset.rfl
  · exact le_iInf₂ fun W hW ↦ coheight_anti (show W ≤ _ from hW)

/-- In an irreducible scheme, a point whose closure has codimension zero is the generic point. -/
private theorem eq_genericPoint_of_codim_closure_singleton_eq_zero {X : Scheme.{u}}
    [IrreducibleSpace X] {x : X} (h : codim (closure ({x} : Set X)) = 0) :
    x = genericPoint X := by
  rw [codim_closure_singleton_eq_coheight_irreducibleCloseds, coheight_eq_zero] at h
  have hle : (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      IrreducibleCloseds X) ≤ ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :=
    show closure {x} ⊆ Set.univ from Set.subset_univ _
  have huniv : closure ({x} : Set X) = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ _) (h hle)
  exact IsGenericPoint.eq huniv (genericPoint_spec X)

/-- The closure of the generic point of an irreducible scheme has codimension zero. -/
private theorem codim_closure_genericPoint {X : Scheme.{u}} [IrreducibleSpace X] :
    codim (closure ({genericPoint X} : Set X)) = 0 := by
  rw [codim_closure_singleton_eq_coheight_irreducibleCloseds, coheight_eq_zero]
  intro W _
  change (W : Set X) ⊆ closure {genericPoint X}
  rw [genericPoint_closure]
  exact Set.subset_univ _

/-- The codimension of the closure of a point is at most the dimension of the space. -/
private theorem codim_closure_singleton_le_topologicalKrullDim {X : Type*} [TopologicalSpace X]
    (x : X) : (codim (closure ({x} : Set X)) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rw [codim_closure_singleton_eq_coheight_irreducibleCloseds]
  exact coheight_le_krullDim _

section Variety

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The Chow group of codimension `r`** (Hartshorne, Appendix A.1). On a variety `X` (an
integral scheme, separated and of finite type over a field `k`, of dimension `n`), `A^r(X)` is the
group of codimension-`r` cycles modulo rational equivalence, `Z^r(X) / Rat^r(X)`. -/
abbrev chowGroup (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p) [IsSeparated p]
    {n : ℕ} (hn : topologicalKrullDim X = n) (r : ℕ) : Type u :=
  codimensionCycles X r ⧸ rationalEquivalenceSubgroup p hp hn r

/-- **The graded Chow group** (Hartshorne, Appendix A.1). On a variety `X` of dimension `n`,
`A(X) = ⨁_{r=0}^{n} A^r(X)`, the direct sum of the Chow groups of codimension `0, …, n`, graded by
its summands. -/
abbrev gradedChowGroup (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p) [IsSeparated p]
    {n : ℕ} (hn : topologicalKrullDim X = n) : Type u :=
  DirectSum (Fin (n + 1)) fun r ↦ chowGroup p hp hn r

/-- There are no codimension `-1` subvarieties, so rational equivalence in codimension zero is
trivial. -/
theorem rationalEquivalenceSubgroup_zero (p : X ⟶ Spec (.of k)) [IsIntegral X]
    (hp : FiniteType p) [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n) :
    rationalEquivalenceSubgroup p hp hn 0 = ⊥ := by
  rw [rationalEquivalenceSubgroup, AddSubgroup.closure_eq_bot_iff]
  rintro c ⟨V, _, i, _, hV, -⟩
  exact absurd hV (by simp)

open scoped Classical in
/-- On an irreducible scheme, an integer multiple of the generic point is a codimension-zero
cycle. -/
private theorem single_genericPoint_mem_codimensionCycles_zero [IrreducibleSpace X] (m : ℤ) :
    Function.locallyFinsuppWithin.single (genericPoint X) m ∈ codimensionCycles X 0 := by
  have hsupp : ∀ x, (Function.locallyFinsuppWithin.single (genericPoint X) m :
      AlgebraicCycle X ℤ) x ≠ 0 → x = genericPoint X := by
    intro x hx
    by_contra h
    exact hx (by simp [Function.locallyFinsuppWithin.single_apply, h])
  refine ⟨(Set.finite_singleton (genericPoint X)).subset fun x hx ↦ hsupp x hx, fun x hx ↦ ?_⟩
  rw [hsupp x hx]
  exact_mod_cast codim_closure_genericPoint

open scoped Classical in
/-- On an integral scheme, a codimension-zero cycle is determined by its coefficient at the
generic point: it is that coefficient times `[X]`. -/
noncomputable def codimensionCyclesZeroEquivInt [IsIntegral X] :
    codimensionCycles X 0 ≃+ ℤ where
  toFun c := (c : AlgebraicCycle X ℤ) (genericPoint X)
  invFun m := ⟨Function.locallyFinsuppWithin.single (genericPoint X) m,
    single_genericPoint_mem_codimensionCycles_zero m⟩
  left_inv c := by
    ext x
    change Function.locallyFinsuppWithin.single (genericPoint X)
      ((c : AlgebraicCycle X ℤ) (genericPoint X)) x = (c : AlgebraicCycle X ℤ) x
    rw [Function.locallyFinsuppWithin.single_apply]
    split_ifs with hx
    · rw [hx]
    · symm
      by_contra hc
      exact hx (eq_genericPoint_of_codim_closure_singleton_eq_zero
        (by exact_mod_cast c.2.2 x hc))
  right_inv m := by
    change Function.locallyFinsuppWithin.single (genericPoint X) m (genericPoint X) = m
    simp
  map_add' _ _ := rfl

/-- **`A^0(X) ≃ ℤ`** (Hartshorne, Appendix A.1). On a variety `X`, the Chow group of
codimension zero is isomorphic to `ℤ`. -/
noncomputable def chowGroupZeroEquivInt (p : X ⟶ Spec (.of k)) [IsIntegral X]
    (hp : FiniteType p) [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n) :
    chowGroup p hp hn 0 ≃+ ℤ :=
  (QuotientAddGroup.quotientAddEquivOfEq (rationalEquivalenceSubgroup_zero p hp hn)).trans
    (QuotientAddGroup.quotientBot.trans codimensionCyclesZeroEquivInt)

/-- The isomorphism `A^0(X) ≃ ℤ` takes the class of a codimension-zero cycle to its coefficient
at the generic point of `X`; in particular the class of `[X]` goes to `1`. -/
theorem chowGroupZeroEquivInt_mk (p : X ⟶ Spec (.of k)) [IsIntegral X]
    (hp : FiniteType p) [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n)
    (c : codimensionCycles X 0) :
    chowGroupZeroEquivInt p hp hn (QuotientAddGroup.mk c) =
      (c : AlgebraicCycle X ℤ) (genericPoint X) :=
  rfl

/-- There are no codimension-`r` cycles on a scheme of dimension `n < r`. -/
theorem codimensionCycles_eq_bot_of_lt {n r : ℕ} (hn : topologicalKrullDim X = n) (hr : n < r) :
    codimensionCycles X r = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [AddSubgroup.mem_bot]
  ext x
  by_contra hx
  have hx' : x ∈ c.support := fun h ↦ hx (by rw [h]; rfl)
  have h := codim_closure_singleton_le_topologicalKrullDim x
  rw [hc.2 x hx', hn] at h
  have : r ≤ n := by exact_mod_cast h
  omega

/-- **`A^r(X) = 0` for `r > dim X`** (Hartshorne, Appendix A.1). On a variety `X` of dimension
`n`, the Chow group of codimension `r > n` is zero. -/
theorem subsingleton_chowGroup_of_lt (p : X ⟶ Spec (.of k)) [IsIntegral X]
    (hp : FiniteType p) [IsSeparated p] {n : ℕ} (hn : topologicalKrullDim X = n) {r : ℕ}
    (hr : n < r) : Subsingleton (chowGroup p hp hn r) := by
  have : Subsingleton (codimensionCycles X r) := by
    rw [codimensionCycles_eq_bot_of_lt hn hr]
    infer_instance
  constructor
  rintro ⟨a⟩ ⟨b⟩
  exact congrArg _ (Subsingleton.elim a b)

end Variety

end Hartshorne
