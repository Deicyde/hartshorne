/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Algebra.Polynomial.Basis
import Hartshorne.Scheme.CoherentAffineLocalCriterion

/-!
# A coherent pushforward counterexample

Hartshorne, Caution II.5.8.1 and Exercise II.5.5(a): the direct image of a coherent sheaf need
not be coherent.  For a field `k`, let `f : 𝔸¹_k = Spec k[t] → Spec k` be the structure
morphism.  The structure sheaf of `𝔸¹_k` is coherent, but `Γ(Spec k, f_* 𝒪) = k[t]` is not a
finitely generated `k`-module, so `f_* 𝒪` is not coherent.

Hartshorne's varieties in Chapter II are integral schemes that are separated and of finite type
over `Spec k` (with `k` algebraically closed).  The statement below is phrased with these
conditions written out for schemes over `Spec k` (finite type being locally of finite type and
quasi-compact), and it holds for every field `k`.
-/

open CategoryTheory AlgebraicGeometry Polynomial

namespace Hartshorne

universe u

/-- The polynomial ring `k[t]` is not a finitely generated `k`-module. -/
theorem not_moduleFinite_polynomial (k : Type u) [Field k] : ¬ Module.Finite k k[X] := by
  intro _
  have := Module.Finite.finite_basis (basisMonomials k)
  exact not_finite ℕ

/-- The direct image of the structure sheaf along `𝔸¹_k → Spec k` is not coherent: its global
sections form the `k`-module `k[t]`, which is not finitely generated. -/
theorem not_isCoherent_pushforward_affineLine (k : Type u) [Field k] :
    ¬ IsCoherent ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of k[X])).ringCatSheaf)) := by
  intro h
  have hfin := (forall_affine_finite_of_isCoherent _ h ⟨⊤, isAffineOpen_top _⟩).1
  apply not_moduleFinite_polynomial k
  let F := (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap k k[X])))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of k[X])).ringCatSheaf)
  let e : Γ(F, ⊤) ≃+ k[X] :=
    (Scheme.ΓSpecIso (CommRingCat.of k[X])).commRingCatIsoToRingEquiv.toAddEquiv
  refine (CoherentAux.finite_iff_of_ringEquiv_addEquiv
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv e ?_).mp hfin
  intro a s
  have hnat := congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k k[X]))) a)
  change (Scheme.ΓSpecIso (CommRingCat.of k[X])).hom
      ((Spec.map (CommRingCat.ofHom (algebraMap k k[X]))).appTop a *
        (show Γ(Spec (CommRingCat.of k[X]), ⊤) from s)) = _
  rw [map_mul]
  erw [hnat]
  rw [Algebra.smul_def]
  rfl

/-- **Hartshorne, Caution II.5.8.1.** Over any field `k` there are varieties `X` and `Y`
(integral schemes, separated and of finite type over `Spec k`), a morphism `f : X → Y` over
`Spec k`, and a coherent `𝒪_X`-module `F` such that `f_* F` is not coherent.  One takes
`f : 𝔸¹_k → Spec k` and `F = 𝒪_{𝔸¹_k}`. -/
theorem exists_isCoherent_not_isCoherent_pushforward (k : Type u) [Field k] :
    ∃ (X Y : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k))
      (f : X ⟶ Y),
      f ≫ pY = pX ∧ IsIntegral X ∧ IsIntegral Y ∧
        IsSeparated pX ∧ LocallyOfFiniteType pX ∧ QuasiCompact pX ∧
        IsSeparated pY ∧ LocallyOfFiniteType pY ∧ QuasiCompact pY ∧
        ∃ F : X.Modules, IsCoherent F ∧ ¬ IsCoherent ((Scheme.Modules.pushforward f).obj F) := by
  let f : Spec (CommRingCat.of k[X]) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k[X]))
  have hf : LocallyOfFiniteType f := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact ⟨_, _, f, 𝟙 _, f, Category.comp_id f, inferInstance, inferInstance,
    inferInstance, hf, inferInstance, inferInstance, inferInstance, inferInstance,
    _, isCoherent_structureSheafModule _, not_isCoherent_pushforward_affineLine k⟩

end Hartshorne
