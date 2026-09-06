/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# An element stabilising a finite-dimensional subspace is integral

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(a).

If `K` is a `k`-algebra domain, `V ⊆ K` a nonzero finite-dimensional
`k`-subspace, and `f ∈ K` satisfies `f · V ⊆ V`, then `f` is integral over `k`;
and if `k` is algebraically closed and `K` a domain, `f` lies in `k`.

This is the whole content of Theorem 3.4(a), with the geometry removed.
Hartshorne's argument for `𝒪(Y) = k` is: a global regular function multiplies
some graded piece `S(Y)_N` into itself, that piece is a finite-dimensional
`k`-vector space, so the function is integral over `k`, and `k` is algebraically
closed. Only the first two clauses are about projective varieties; the rest is
the statement below.

The reason `f · V ⊆ V` gives integrality, rather than merely algebraicity, is
the standard determinant trick, and Mathlib supplies it in the form
`IsIntegral.of_mem_of_fg`: it is enough that `k[f]` be finitely generated as a
`k`-module. That follows because `a ↦ a · v` embeds `k[f]` into `V` for any
nonzero `v ∈ V`, injectively because `K` is a domain.

## Main results

* `Hartshorne.isIntegral_of_mul_mem`
* `Hartshorne.exists_algebraMap_eq_of_mul_mem`
-/

namespace Hartshorne

open Polynomial

variable {k K : Type*} [Field k] [CommRing K] [IsDomain K] [Algebra k K]

/-- **An element stabilising a nonzero finite-dimensional subspace is integral.**

`k[f]` embeds into `V` by acting on a nonzero element, so it is finitely
generated as a `k`-module, and every element of a finitely generated subalgebra
is integral. -/
theorem isIntegral_of_mul_mem (V : Submodule k K) [Module.Finite k ↥V] (hV : V ≠ ⊥)
    {f : K} (hf : ∀ v ∈ V, f * v ∈ V) : IsIntegral k f := by
  set S := Algebra.adjoin k ({f} : Set K) with hS
  -- Everything in `k[f]` stabilises `V`, by induction on the generation.
  have hSV : ∀ a ∈ S, ∀ v ∈ V, a * v ∈ V := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hf
    | algebraMap c => intro v hv; rw [← Algebra.smul_def]; exact V.smul_mem c hv
    | add x y _ _ hx hy => intro v hv; rw [add_mul]; exact V.add_mem (hx v hv) (hy v hv)
    | mul x y _ hy hx hyy => intro v hv; rw [mul_assoc]; exact hx _ (hyy v hv)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff V).1 hV
  -- Acting on `v` embeds `k[f]` into `V`.
  let φ : S.toSubmodule →ₗ[k] V :=
    { toFun := fun a => ⟨a.1 * v, hSV a.1 a.2 v hv⟩
      map_add' := fun a b => by ext; simp [add_mul]
      map_smul' := fun c a => by ext; simp [Algebra.smul_def, mul_assoc] }
  have hφ : Function.Injective φ := by
    intro a b hab
    have : a.1 * v = b.1 * v := congrArg Subtype.val hab
    exact Subtype.ext (mul_right_cancel₀ hv0 this)
  have : FiniteDimensional k S.toSubmodule := FiniteDimensional.of_injective φ hφ
  refine IsIntegral.of_mem_of_fg S ?_ f (Algebra.self_mem_adjoin_singleton k f)
  exact (Submodule.fg_top _).1 (Module.Finite.iff_fg.1 inferInstance)

/-- **And over an algebraically closed field it is a constant.**

The minimal polynomial of an integral element is irreducible, hence linear when
`k` is algebraically closed, so the element is the negative of its constant
term. -/
theorem exists_algebraMap_eq_of_isIntegral [IsAlgClosed k] {f : K} (hf : IsIntegral k f) :
    ∃ c : k, algebraMap k K c = f := by
  refine ⟨-(minpoly k f).coeff 0, ?_⟩
  have hq : (minpoly k f).leadingCoeff = 1 := minpoly.monic hf
  have hdeg : (minpoly k f).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hf)
  have haeval : aeval f (minpoly k f) = 0 := minpoly.aeval k f
  rw [eq_X_add_C_of_degree_eq_one hdeg, hq, C_1, one_mul, map_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at haeval
  exact (map_neg (algebraMap k K) ((minpoly k f).coeff 0)).symm ▸ haeval.symm

/-- The two together: over an algebraically closed field, an element stabilising
a nonzero finite-dimensional subspace is a constant. This is Theorem 3.4(a) with
the geometry removed. -/
theorem exists_algebraMap_eq_of_mul_mem [IsAlgClosed k] (V : Submodule k K)
    [Module.Finite k ↥V] (hV : V ≠ ⊥) {f : K} (hf : ∀ v ∈ V, f * v ∈ V) :
    ∃ c : k, algebraMap k K c = f :=
  exists_algebraMap_eq_of_isIntegral (isIntegral_of_mul_mem V hV hf)

end Hartshorne
