/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFibreRank
import Hartshorne.Scheme.Differentials.ConormalCriterionNonsingular
import Hartshorne.Scheme.Differentials.NonsingularClosedImmersionConormal

/-!
# Extensions of locally free sheaves

Let `X` be a reduced locally Noetherian scheme and `0 → F' → F → F'' → 0` a short exact
sequence of `𝒪_X`-modules with `F'` locally free of rank `a`, `F''` locally free of rank `b` and
`F` coherent. Then `F` is locally free of rank `a + b` (`isLocallyFreeOfRank_of_shortExact`).

At a point `x` the stalk sequence `0 → F'_x → F_x → F''_x → 0` is exact; it splits because
`F''_x` is free, so `F_x ≅ F'_x × F''_x` is free of rank `a + b`, and the fibre `F_x ⊗ k(x)`
has dimension `a + b`. The constant fibre dimension criterion concludes.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Module
open scoped TensorProduct

namespace Hartshorne

/-- **Extensions of locally free sheaves.** On a reduced locally Noetherian scheme, if
`0 → F' → F → F'' → 0` is short exact with `F'` locally free of rank `a`, `F''` locally free of
rank `b` and `F` coherent, then `F` is locally free of rank `a + b`. -/
theorem isLocallyFreeOfRank_of_shortExact {X : Scheme.{u}} [IsReduced X] [IsLocallyNoetherian X]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) {a b : ℕ}
    (h₁ : S.X₁.IsLocallyFreeOfRank a) (h₃ : S.X₃.IsLocallyFreeOfRank b)
    (h₂ : IsCoherent S.X₂) : S.X₂.IsLocallyFreeOfRank (a + b) := by
  refine (isLocallyFreeOfRank_iff_forall_finrank_fibre _ h₂ (a + b)).mpr fun x => ?_
  have : Mono S.f := hS.mono_f
  obtain ⟨hex, hsurj⟩ := NonsingularConormal.stalk_exact_and_surjective (R := X.sheaf) S
    hS.exact hS.epi_g x
  have hinj := ConormalCriterion.injective_stalk_of_mono S.f x
  obtain ⟨e₁⟩ := NonsingularConormal.nonempty_stalk_equiv_of_isLocallyFreeOfRank S.X₁ a h₁ x
  obtain ⟨e₃⟩ := NonsingularConormal.nonempty_stalk_equiv_of_isLocallyFreeOfRank S.X₃ b h₃ x
  have : IsLocalRing (ringSheafStalk X.sheaf x) :=
    inferInstanceAs (IsLocalRing (X.presheaf.stalk x))
  let Fx := Ringed.moduleStalkFunctor (R := X.sheaf) x
  let O := ringSheafStalk X.sheaf x
  let e₁' : Fx.obj S.X₁ ≃ₗ[O] (Fin a → O) := e₁
  let e₃' : Fx.obj S.X₃ ≃ₗ[O] (Fin b → O) := e₃
  let f : Fx.obj S.X₁ →ₗ[O] Fx.obj S.X₂ := (Fx.map S.f).hom
  let g : Fx.obj S.X₂ →ₗ[O] Fx.obj S.X₃ := (Fx.map S.g).hom
  have : Module.Free O (Fx.obj S.X₃) := Module.Free.of_equiv e₃'.symm
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hsurj
  obtain ⟨e, -⟩ := (Function.Exact.splitSurjectiveEquiv (f := f) (g := g) hex hinj ⟨l, hl⟩)
  let e' : Fx.obj S.X₂ ≃ₗ[O] (Fin a ⊕ Fin b → O) :=
    e.trans ((e₁'.prodCongr e₃').trans (LinearEquiv.sumArrowLequivProdArrow _ _ O O).symm)
  have : Module.Free O (Fx.obj S.X₂) := Module.Free.of_equiv e'.symm
  have : Module.Finite O (Fx.obj S.X₂) := Module.Finite.equiv e'.symm
  have key : finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] Fx.obj S.X₂) =
      a + b := by
    rw [Module.finrank_baseChange, e'.finrank_eq, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  exact key

end Hartshorne
