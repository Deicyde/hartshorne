/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.RawCyclePushforward

/-!
# Functoriality of the raw pushforward of cycles

Hartshorne, *Algebraic Geometry*, Appendix A.1 (pp. 425–426).

For composable morphisms `f : X → X'` and `g : X' → X''` of integral schemes of finite type over a
field `k`, over `k`, the raw cycle pushforward satisfies `(g ∘ f)_* = g_* ∘ f_*`
(`rawCyclePushforward_comp`), and the identity acts as the identity (`rawCyclePushforward_id`).
Both are stated on the underlying algebraic cycles: `f_*` maps codimension `r` to codimension
`r + n' - n`, `g_*` then to codimension `(r + n' - n) + n'' - n'`, while `(g ∘ f)_*` maps to
codimension `r + n'' - n`. These natural-number indices agree whenever `f_*` is not forced to be
zero, but not in general.

At the level of generators: a dimension drop at either stage is a dimension drop of the composite
(`dimension_drop_comp_iff`), and the coefficients multiply
(`rawCyclePushforwardCoeff_comp`); in the dimension-preserving case this is the tower law
`[K(Y) : K(Y'')] = [K(Y') : K(Y'')] [K(Y) : K(Y')]` for the residue degrees
(`residueDegree_comp`).
-/

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Order

universe u

/-- Tower law for residue degrees: for `f : X ⟶ Y`, `g : Y ⟶ Z` and `x : X`,
`[κ(x) : κ(g (f x))] = [κ(f x) : κ(g (f x))] [κ(x) : κ(f x)]` (with the convention that an infinite
degree is `0`). -/
theorem residueDegree_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f.base x) * f.residueDegree x := by
  let F := Z.residueField (g.base (f.base x))
  let K := Y.residueField (f.base x)
  let A := X.residueField x
  let _ : Algebra F K := (g.residueFieldMap (f.base x)).hom.toAlgebra
  let _ : Algebra K A := (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra F A := (((f ≫ g).residueFieldMap x : _ ⟶ A) : F ⟶ A).hom.toAlgebra
  have : IsScalarTower F K A :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
      (Scheme.residueFieldMap_comp f g x))
  exact (Module.finrank_mul_finrank F K A).symm

variable {X X' X'' : Scheme.{u}}

/-- The coefficient of the raw pushforward in terms of heights in the specialization order:
`closure {x}` has a dimension drop exactly when `height (f x) < height x`. -/
lemma rawCyclePushforwardCoeff_eq_ite (f : X ⟶ X') (x : X) :
    rawCyclePushforwardCoeff f x =
      if height (f.base x) < height x then 0 else (f.residueDegree x : ℤ) := by
  classical
  rw [rawCyclePushforwardCoeff, rawCyclePushforward_closure_image_eq,
    FlatEquidimensional.topologicalKrullDim_closure_singleton,
    FlatEquidimensional.topologicalKrullDim_closure_singleton]
  simp only [WithBot.coe_lt_coe]

/-- The raw pushforward of the identity has coefficient `1` everywhere. -/
lemma rawCyclePushforwardCoeff_id (x : X) : rawCyclePushforwardCoeff (𝟙 X) x = 1 := by
  simp [rawCyclePushforwardCoeff_eq_ite]

open scoped Classical in
/-- The value at `y` of the raw pushforward of a codimension-`r` cycle `c`. -/
lemma rawCyclePushforwardUngraded_apply_apply (f : X ⟶ X') (r : ℕ) (c : codimensionCycles X r)
    (y : X') :
    rawCyclePushforwardUngraded f r c y =
      ∑ x ∈ c.2.1.toFinset,
        (c : AlgebraicCycle X ℤ) x *
          (if y = f.base x then rawCyclePushforwardCoeff f x else 0) := by
  classical
  rw [rawCyclePushforwardUngraded_apply, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, rawCyclePushforwardGenerator,
    Function.locallyFinsuppWithin.single_apply, smul_eq_mul]

/-- The raw pushforward on finitely supported functions: the linear extension of
`x ↦ rawCyclePushforwardCoeff f x • [f x]`. -/
noncomputable def rawCyclePushforwardFinsupp (f : X ⟶ X') : (X →₀ ℤ) →+ (X' →₀ ℤ) :=
  Finsupp.liftAddHom fun x =>
    zmultiplesHom _ (Finsupp.single (f.base x) (rawCyclePushforwardCoeff f x))

/-- The linear extension of the generators, on finitely supported functions. -/
noncomputable def rawCyclePushforwardGeneratorSum (f : X ⟶ X') : (X →₀ ℤ) →+ AlgebraicCycle X' ℤ :=
  Finsupp.liftAddHom fun x => zmultiplesHom _ (rawCyclePushforwardGenerator f x)

/-- The raw pushforward of a codimension-`r` cycle is the linear extension of the generators applied
to its underlying finitely supported function. -/
lemma rawCyclePushforwardUngraded_eq (f : X ⟶ X') (r : ℕ) (c : codimensionCycles X r) :
    rawCyclePushforwardUngraded f r c =
      rawCyclePushforwardGeneratorSum f (codimensionCyclesToFinsupp r c) :=
  rfl

/-- Pushing forward and then summing the generators of `g` is summing the generators of `f ≫ g`,
given the multiplicativity of the coefficients. -/
lemma rawCyclePushforwardGeneratorSum_comp_finsupp (f : X ⟶ X') (g : X' ⟶ X'')
    (h : ∀ x, rawCyclePushforwardCoeff (f ≫ g) x =
      rawCyclePushforwardCoeff g (f.base x) * rawCyclePushforwardCoeff f x) :
    (rawCyclePushforwardGeneratorSum g).comp (rawCyclePushforwardFinsupp f) =
      rawCyclePushforwardGeneratorSum (f ≫ g) := by
  classical
  refine Finsupp.addHom_ext fun x a => ?_
  refine Function.locallyFinsuppWithin.ext fun z => ?_
  simp only [AddMonoidHom.comp_apply, rawCyclePushforwardFinsupp, rawCyclePushforwardGeneratorSum,
    Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, map_zsmul,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, rawCyclePushforwardGenerator,
    Function.locallyFinsuppWithin.single_apply, smul_eq_mul, h, Scheme.Hom.comp_base,
    TopCat.hom_comp, ContinuousMap.comp_apply]
  split_ifs <;> ring

/-- The finitely supported function underlying the raw pushforward of a codimension-`r` cycle. -/
lemma codimensionCyclesToFinsupp_rawCyclePushforward {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) (p' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X']
    (hp : FiniteType p) (hp' : FiniteType p') (f : X ⟶ X') (hf : f ≫ p' = p) {n n' : ℕ}
    (hn : topologicalKrullDim X = n) (hn' : topologicalKrullDim X' = n') (r : ℕ)
    (c : codimensionCycles X r) :
    codimensionCyclesToFinsupp (r + n' - n) (rawCyclePushforward p p' hp hp' f hf hn hn' r c) =
      rawCyclePushforwardFinsupp f (codimensionCyclesToFinsupp r c) := by
  classical
  ext y
  change (rawCyclePushforward p p' hp hp' f hf hn hn' r c : AlgebraicCycle X' ℤ) y = _
  rw [coe_rawCyclePushforward, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  simp only [rawCyclePushforwardFinsupp, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, rawCyclePushforwardGenerator,
    Function.locallyFinsuppWithin.single_apply, smul_eq_mul, zmultiplesHom_apply,
    Finsupp.smul_apply, Finsupp.single_apply, codimensionCyclesToFinsupp, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Finsupp.ofSupportFinite_coe]
  split_ifs <;> simp_all

section Varieties

variable {k : Type u} [Field k]

/-- **Dimension drop is absorbing.** For morphisms `f : X → X'` and `g : X' → X''` over `k` of
schemes of finite type over `k`, and `Y = closure {x}` in `X`, the composite `g ∘ f` drops the
dimension of `Y` if and only if `f` drops the dimension of `Y` or `g` drops the dimension of
`closure f(Y)`. -/
theorem dimension_drop_comp_iff (p : X ⟶ Spec (.of k)) (p' : X' ⟶ Spec (.of k))
    (p'' : X'' ⟶ Spec (.of k)) (hp : FiniteType p) (hp' : FiniteType p') (hp'' : FiniteType p'')
    (f : X ⟶ X') (g : X' ⟶ X'') (hf : f ≫ p' = p) (hg : g ≫ p'' = p') (x : X) :
    topologicalKrullDim (closure ((f ≫ g).base '' closure ({x} : Set X))) <
        topologicalKrullDim (closure ({x} : Set X)) ↔
      topologicalKrullDim (closure (f.base '' closure ({x} : Set X))) <
          topologicalKrullDim (closure ({x} : Set X)) ∨
        topologicalKrullDim (closure (g.base '' closure (f.base '' closure ({x} : Set X)))) <
          topologicalKrullDim (closure (f.base '' closure ({x} : Set X))) := by
  rw [rawCyclePushforward_closure_image_eq, rawCyclePushforward_closure_image_eq,
    rawCyclePushforward_closure_image_eq,
    show (f ≫ g).base x = g.base (f.base x) from rfl,
    FlatEquidimensional.topologicalKrullDim_closure_singleton,
    FlatEquidimensional.topologicalKrullDim_closure_singleton,
    FlatEquidimensional.topologicalKrullDim_closure_singleton]
  simp only [WithBot.coe_lt_coe]
  have hfle := height_apply_le p p' hp hp' f hf x
  have hgle := height_apply_le p' p'' hp' hp'' g hg (f.base x)
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact (h.trans_le (hne.1.trans hne.2)).false
  · rintro (h | h)
    · exact hgle.trans_lt h
    · exact h.trans_le hfle

/-- **Multiplicativity of the raw pushforward coefficients.** For morphisms `f : X → X'` and
`g : X' → X''` over `k` of schemes of finite type over `k`, the coefficient of `(g ∘ f)_*[Y]` is the
product of those of `g_*[closure f(Y)]` and `f_*[Y]`: it is `0` when either stage drops dimension,
and otherwise `[K(Y) : K(Y'')] = [K(Y') : K(Y'')] [K(Y) : K(Y')]` for `Y' = closure f(Y)` and
`Y'' = closure g(Y')`. -/
theorem rawCyclePushforwardCoeff_comp (p : X ⟶ Spec (.of k)) (p' : X' ⟶ Spec (.of k))
    (p'' : X'' ⟶ Spec (.of k)) (hp : FiniteType p) (hp' : FiniteType p') (hp'' : FiniteType p'')
    (f : X ⟶ X') (g : X' ⟶ X'') (hf : f ≫ p' = p) (hg : g ≫ p'' = p') (x : X) :
    rawCyclePushforwardCoeff (f ≫ g) x =
      rawCyclePushforwardCoeff g (f.base x) * rawCyclePushforwardCoeff f x := by
  have hfle := height_apply_le p p' hp hp' f hf x
  have hgle := height_apply_le p' p'' hp' hp'' g hg (f.base x)
  simp only [rawCyclePushforwardCoeff_eq_ite, Scheme.Hom.comp_base, TopCat.hom_comp,
    ContinuousMap.comp_apply, residueDegree_comp, Nat.cast_mul]
  by_cases h1 : height (f.base x) < height x
  · rw [if_pos (hgle.trans_lt h1), if_pos h1, mul_zero]
  · have heq : height (f.base x) = height x := le_antisymm hfle (not_lt.mp h1)
    rw [if_neg h1]
    by_cases h2 : height (g.base (f.base x)) < height (f.base x)
    · rw [if_pos (heq ▸ h2), if_pos h2, zero_mul]
    · rw [if_neg (heq ▸ h2), if_neg h2]

/-- **The identity acts identically** on cycles: for an integral scheme `X` of finite type over
`k` of dimension `n`, the raw pushforward along the identity of `X` maps every codimension-`r` cycle
to itself. -/
theorem rawCyclePushforward_id (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p) {n : ℕ}
    (hn : topologicalKrullDim X = n) (r : ℕ) (c : codimensionCycles X r) :
    (rawCyclePushforward p p hp hp (𝟙 X) (Category.id_comp p) hn hn r c : AlgebraicCycle X ℤ) =
      c := by
  classical
  refine Function.locallyFinsuppWithin.ext fun y => ?_
  change rawCyclePushforwardUngraded (𝟙 X) r c y = _
  rw [rawCyclePushforwardUngraded_apply_apply]
  simp only [rawCyclePushforwardCoeff_id, Scheme.Hom.id_base, TopCat.hom_id, ContinuousMap.id_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hy
  · rfl
  · exact (Function.notMem_support.mp fun h => hy (c.2.1.mem_toFinset.mpr h)).symm

/-- **Functoriality of the raw pushforward of cycles** (Hartshorne, Appendix A.1). Let `X`, `X'`,
`X''` be integral schemes of finite type over a field `k` (varieties), of dimensions `n`, `n'`,
`n''`, and let `f : X → X'` and `g : X' → X''` be morphisms over `k`. Then for every
codimension-`r` cycle `c` on `X`, `(g ∘ f)_* c = g_* (f_* c)` as cycles on `X''`. Here
`f_* c` has codimension `r + n' - n`, and `(g ∘ f)_* c` codimension `r + n'' - n`. -/
theorem rawCyclePushforward_comp (p : X ⟶ Spec (.of k)) (p' : X' ⟶ Spec (.of k))
    (p'' : X'' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X'] [IsIntegral X''] (hp : FiniteType p)
    (hp' : FiniteType p') (hp'' : FiniteType p'')
    (f : X ⟶ X') (g : X' ⟶ X'') (hf : f ≫ p' = p) (hg : g ≫ p'' = p') {n n' n'' : ℕ}
    (hn : topologicalKrullDim X = n) (hn' : topologicalKrullDim X' = n')
    (hn'' : topologicalKrullDim X'' = n'') (r : ℕ) (c : codimensionCycles X r) :
    (rawCyclePushforward p p'' hp hp'' (f ≫ g) (by rw [Category.assoc, hg, hf]) hn hn'' r c :
        AlgebraicCycle X'' ℤ) =
      rawCyclePushforward p' p'' hp' hp'' g hg hn' hn'' (r + n' - n)
        (rawCyclePushforward p p' hp hp' f hf hn hn' r c) := by
  change rawCyclePushforwardUngraded (f ≫ g) r c =
    rawCyclePushforwardUngraded g (r + n' - n) (rawCyclePushforward p p' hp hp' f hf hn hn' r c)
  rw [rawCyclePushforwardUngraded_eq, rawCyclePushforwardUngraded_eq,
    codimensionCyclesToFinsupp_rawCyclePushforward,
    ← rawCyclePushforwardGeneratorSum_comp_finsupp f g
      (rawCyclePushforwardCoeff_comp p p' p'' hp hp' hp'' f g hf hg)]
  rfl

end Varieties

end Hartshorne
