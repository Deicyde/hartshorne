/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.ResidueField
import Hartshorne.Cohomology.FlatFamilies.FlatEquidimensional
import Hartshorne.Intersection.CodimensionCycles
import Hartshorne.Scheme.DimensionCodimension

/-!
# Raw pushforward of cycles

Hartshorne, *Algebraic Geometry*, Appendix A.1 (pp. 425–426).

Cycles are represented as in `Hartshorne.codimensionCycles`: an irreducible closed subset `Y` of a
scheme is recorded by its generic point `x`, so `Y = closure {x}`. For a morphism `f : X ⟶ X'`,
the closure of `f(Y)` is then `closure {f x}`, and its function field, like that of `Y`, is the
residue field at its generic point (the stalk of the reduced induced structure at the generic point
is the residue field). Hence `[K(Y) : K(closure f(Y))]` is the degree of the residue field
extension `κ(f x) → κ(x)`, which is `Hom.residueDegree f x`.

The generator-level definition and the linear extension to finitely supported cycles of a fixed
codimension, with values in all algebraic cycles of the target, make sense for any morphism of
schemes. The codimension reindexing is stated for varieties: `X` and `X'` are integral schemes of
finite type over a field `k`, of dimensions `n` and `n'`, and `f` is a morphism over `k`. Then
`rawCyclePushforward` maps codimension-`r` cycles of `X` to codimension-`(r + n' - n)` cycles of
`X'`. Membership in the target uses the dimension-codimension formula in `X` and in `X'`, together
with the inequality `dim closure f(Y) ≤ dim Y` (`height_apply_le`), so that the generators without a
dimension drop are exactly those with `dim closure f(Y) = dim Y`. When `r + n' < n` every generator
has a dimension drop and the map is zero (`rawCyclePushforward_eq_zero_of_lt`); the target index is
then truncated to `0`.
-/

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Order

universe u

variable {X X' : Scheme}

open scoped Classical in
/-- The coefficient of `f_*[Y]` for `Y = closure {x}`: zero if the closure of `f(Y)` has smaller
dimension than `Y`, and otherwise the degree `[κ(x) : κ(f x)]` of the function field extension. -/
noncomputable def rawCyclePushforwardCoeff (f : X ⟶ X') (x : X) : ℤ :=
  if topologicalKrullDim (closure (f.base '' closure ({x} : Set X))) <
      topologicalKrullDim (closure ({x} : Set X)) then 0
  else f.residueDegree x

/-- The closure of the image of `closure {x}` is the closure of `{f x}`. -/
lemma rawCyclePushforward_closure_image_eq (f : X ⟶ X') (x : X) :
    closure (f.base '' closure ({x} : Set X)) = closure {f.base x} := by
  rw [closure_image_closure f.base.hom.continuous, Set.image_singleton]

open scoped Classical in
/-- The raw pushforward `f_*[Y]` of the cycle of `Y = closure {x}`: the coefficient
`rawCyclePushforwardCoeff f x` times the cycle of `closure {f x}`. -/
noncomputable def rawCyclePushforwardGenerator (f : X ⟶ X') (x : X) : AlgebraicCycle X' ℤ :=
  Function.locallyFinsuppWithin.single (f.base x) (rawCyclePushforwardCoeff f x)

/-- A finitely supported codimension-`r` cycle viewed as a finitely supported function. -/
noncomputable def codimensionCyclesToFinsupp (r : ℕ) : codimensionCycles X r →+ (X →₀ ℤ) where
  toFun c := Finsupp.ofSupportFinite (c : AlgebraicCycle X ℤ) c.2.1
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

/-- The raw pushforward of codimension-`r` cycles, extended linearly from
`rawCyclePushforwardGenerator`, with values in all algebraic cycles of the target. -/
noncomputable def rawCyclePushforwardUngraded (f : X ⟶ X') (r : ℕ) :
    codimensionCycles X r →+ AlgebraicCycle X' ℤ :=
  (Finsupp.liftAddHom fun x => zmultiplesHom _ (rawCyclePushforwardGenerator f x)).comp
    (codimensionCyclesToFinsupp r)

lemma rawCyclePushforwardUngraded_apply (f : X ⟶ X') (r : ℕ) (c : codimensionCycles X r) :
    rawCyclePushforwardUngraded f r c =
      ∑ x ∈ c.2.1.toFinset, (c : AlgebraicCycle X ℤ) x • rawCyclePushforwardGenerator f x := by
  simp only [rawCyclePushforwardUngraded, AddMonoidHom.comp_apply, Finsupp.liftAddHom_apply]
  rfl

/-- A point in the support of the raw pushforward of a codimension-`r` cycle `c` is `f x` for a
point `x` of the support of `c` whose coefficient `rawCyclePushforwardCoeff f x` is nonzero. -/
lemma exists_of_mem_support_rawCyclePushforwardUngraded (f : X ⟶ X') {r : ℕ}
    (c : codimensionCycles X r) {y : X'}
    (hy : y ∈ (rawCyclePushforwardUngraded f r c).support) :
    ∃ x ∈ (c : AlgebraicCycle X ℤ).support, f.base x = y ∧ rawCyclePushforwardCoeff f x ≠ 0 := by
  classical
  have hy' : rawCyclePushforwardUngraded f r c y ≠ 0 := hy
  rw [rawCyclePushforwardUngraded_apply, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply] at hy'
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy'
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, rawCyclePushforwardGenerator,
    Function.locallyFinsuppWithin.single_apply, smul_eq_mul] at hne
  by_cases hyx : y = f.base x
  · rw [if_pos hyx] at hne
    exact ⟨x, c.2.1.mem_toFinset.mp hx, hyx.symm, right_ne_zero_of_mul hne⟩
  · rw [if_neg hyx, mul_zero] at hne
    exact absurd rfl hne

section Varieties

variable {k : Type u} [Field k] {X X' : Scheme.{u}}

/-- For a morphism `f` over `k` of schemes of finite type over a field `k`, the closure of the image
of `closure {x}` has dimension at most that of `closure {x}`: in the specialization order,
`height (f x) ≤ height x`. -/
theorem height_apply_le (p : X ⟶ Spec (.of k)) (p' : X' ⟶ Spec (.of k)) (hp : FiniteType p)
    (hp' : FiniteType p') (f : X ⟶ X') (hf : f ≫ p' = p) (x : X) :
    height (f.base x) ≤ height x := by
  have : LocallyOfFiniteType (f ≫ p') := by rw [hf]; exact hp.1
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f p'
  -- A point of `closure {x}` over `f x` of least height is minimal in its fibre.
  let S : Set X := {z | z ≤ x ∧ f.base z = f.base x}
  have hS : S.Nonempty := ⟨x, le_rfl, rfl⟩
  let z := Function.argminOn (fun z : X => height z) S hS
  have hz : z ∈ S := Function.argminOn_mem _ _ _
  have hmin : ∀ w, w ≤ z → f.base w = f.base z → w = z := by
    intro w hwz hfw
    by_contra hne
    have hlt : w < z := lt_of_le_not_ge hwz fun hzw => hne (Specializes.antisymm hzw hwz).eq
    obtain ⟨N, hN, -⟩ := FlatEquidimensional.catenaryAt_of_finiteType p hp w
    have h1 := height_strictMono hlt (by rw [hN]; exact ENat.natCast_lt_top N)
    have h2 : height z ≤ height w :=
      Function.argminOn_le (fun z : X => height z) S ⟨hwz.trans hz.1, hfw.trans hz.2⟩
    exact (h1.trans_le h2).false
  have := FlatEquidimensional.height_eq_height_of_forall p p' hp hp' f z hmin
  calc height (f.base x) = height (f.base z) := by rw [hz.2]
    _ = height z := this.symm
    _ ≤ height x := height_mono hz.1

/-- Reindexing of the raw pushforward. Let `X` and `X'` be integral schemes of finite type over `k`
of dimensions `n` and `n'`, and `f` a morphism over `k`. If `y` lies in the support of the raw
pushforward of a codimension-`r` cycle, then `n ≤ r + n'` and `closure {y}` has codimension
`r + n' - n` in `X'`. -/
theorem codim_closure_of_mem_support_rawCyclePushforwardUngraded (p : X ⟶ Spec (.of k))
    (p' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X'] (hp : FiniteType p)
    (hp' : FiniteType p') (f : X ⟶ X') (hf : f ≫ p' = p) {n n' : ℕ}
    (hn : topologicalKrullDim X = n) (hn' : topologicalKrullDim X' = n') {r : ℕ}
    (c : codimensionCycles X r) {y : X'}
    (hy : y ∈ (rawCyclePushforwardUngraded f r c).support) :
    n ≤ r + n' ∧ codim (closure ({y} : Set X')) = ((r + n' - n : ℕ) : ℕ∞) := by
  obtain ⟨x, hx, rfl, hcoeff⟩ := exists_of_mem_support_rawCyclePushforwardUngraded f c hy
  have hr : codim (closure ({x} : Set X)) = r := c.2.2 x hx
  -- No dimension drop, since the coefficient is nonzero.
  have hge : ¬ height (f.base x) < height x := by
    intro hlt
    apply hcoeff
    rw [rawCyclePushforwardCoeff, rawCyclePushforward_closure_image_eq,
      FlatEquidimensional.topologicalKrullDim_closure_singleton,
      FlatEquidimensional.topologicalKrullDim_closure_singleton, if_pos (WithBot.coe_lt_coe.mpr hlt)]
  have heq : height (f.base x) = height x :=
    le_antisymm (height_apply_le p p' hp hp' f hf x) (not_lt.mp hge)
  -- The dimension-codimension formula in `X` and in `X'`.
  have hX := dimension_codimension_formula p hp (closure ({x} : Set X)) isClosed_closure
    ⟨x, subset_closure (Set.mem_singleton x)⟩
  have hX' := dimension_codimension_formula p' hp' (closure ({f.base x} : Set X'))
    isClosed_closure ⟨f.base x, subset_closure (Set.mem_singleton _)⟩
  rw [FlatEquidimensional.topologicalKrullDim_closure_singleton, hr, hn] at hX
  rw [FlatEquidimensional.topologicalKrullDim_closure_singleton, heq, hn'] at hX'
  have h1 : height x + (r : ℕ∞) = n := by exact_mod_cast hX
  have h2 : height x + codim (closure ({f.base x} : Set X')) = n' := by exact_mod_cast hX'
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (le_self_add.trans_eq h1))
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top n') (le_add_self.trans_eq h2))
  rw [← ha] at h1 h2
  rw [← hb] at h2
  have h1' : a + r = n := by exact_mod_cast h1
  have h2' : a + b = n' := by exact_mod_cast h2
  exact ⟨by omega, by rw [← hb]; exact_mod_cast (by omega : b = r + n' - n)⟩

/-- **Raw pushforward of cycles** (Hartshorne, Appendix A.1). Let `X` and `X'` be integral schemes
of finite type over a field `k` (varieties), of dimensions `n` and `n'`, and let `f : X → X'` be a
morphism over `k`. For an irreducible closed subset `Y = closure {x}` of `X`, `f_*[Y]` is `0` if
`dim closure f(Y) < dim Y`, and otherwise `[K(Y) : K(closure f(Y))] [closure f(Y)]`
(`rawCyclePushforwardGenerator`). Extended linearly, this maps codimension-`r` cycles of `X` to
codimension-`(r + n' - n)` cycles of `X'`. Here the target index is a natural-number
subtraction: when `r + n' < n` it truncates to `0`, and the map is then zero
(`rawCyclePushforward_eq_zero_of_lt`). -/
noncomputable def rawCyclePushforward (p : X ⟶ Spec (.of k)) (p' : X' ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral X'] (hp : FiniteType p) (hp' : FiniteType p') (f : X ⟶ X')
    (hf : f ≫ p' = p) {n n' : ℕ} (hn : topologicalKrullDim X = n)
    (hn' : topologicalKrullDim X' = n') (r : ℕ) :
    codimensionCycles X r →+ codimensionCycles X' (r + n' - n) :=
  (rawCyclePushforwardUngraded f r).codRestrict _ fun c =>
    ⟨((c.2.1.image fun x => f.base x).subset fun y hy => by
        obtain ⟨x, hx, hxy, -⟩ := exists_of_mem_support_rawCyclePushforwardUngraded f c hy
        exact ⟨x, hx, hxy⟩),
      fun _ hy =>
        (codim_closure_of_mem_support_rawCyclePushforwardUngraded p p' hp hp' f hf hn hn' c hy).2⟩

/-- The raw pushforward of a codimension-`r` cycle is the linear extension of the generators. -/
lemma coe_rawCyclePushforward (p : X ⟶ Spec (.of k)) (p' : X' ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral X'] (hp : FiniteType p) (hp' : FiniteType p') (f : X ⟶ X')
    (hf : f ≫ p' = p) {n n' : ℕ} (hn : topologicalKrullDim X = n)
    (hn' : topologicalKrullDim X' = n') (r : ℕ) (c : codimensionCycles X r) :
    (rawCyclePushforward p p' hp hp' f hf hn hn' r c : AlgebraicCycle X' ℤ) =
      ∑ x ∈ c.2.1.toFinset, (c : AlgebraicCycle X ℤ) x • rawCyclePushforwardGenerator f x :=
  rawCyclePushforwardUngraded_apply f r c

/-- When `r + dim X' < dim X`, every generator has a dimension drop, so the raw pushforward of
codimension-`r` cycles is zero. -/
lemma rawCyclePushforward_eq_zero_of_lt (p : X ⟶ Spec (.of k)) (p' : X' ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral X'] (hp : FiniteType p) (hp' : FiniteType p') (f : X ⟶ X')
    (hf : f ≫ p' = p) {n n' : ℕ} (hn : topologicalKrullDim X = n)
    (hn' : topologicalKrullDim X' = n') {r : ℕ} (hr : r + n' < n) :
    rawCyclePushforward p p' hp hp' f hf hn hn' r = 0 := by
  refine AddMonoidHom.ext fun c => Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  show rawCyclePushforwardUngraded f r c y = 0
  by_contra hy
  have := (codim_closure_of_mem_support_rawCyclePushforwardUngraded p p' hp hp' f hf hn hn' c
    (y := y) hy).1
  omega

end Varieties

end Hartshorne
