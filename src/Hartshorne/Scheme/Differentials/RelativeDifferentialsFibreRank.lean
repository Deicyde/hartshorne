/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFibreRank
import Hartshorne.Scheme.Differentials.RelativeDifferentialsQuasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Constant fibre dimension of relative differentials

Hartshorne, *Algebraic Geometry*, III.10, Example 10.0.2 (p. 268): for a morphism `f : X ⟶ Y`
of schemes of finite type over a field with `X` integral, the third clause of Hartshorne's
definition of smoothness,

`dim_{k(x)} ((Ω_{X/Y})_x ⊗ k(x)) = n` for every `x ∈ X`,

is equivalent to `Ω_{X/Y}` being locally free of rank `n`. This is the constant fibre dimension
criterion for coherent sheaves on integral locally Noetherian schemes, applied to the coherent
sheaf `Ω_{X/Y}`.

As a corollary, a morphism that is smooth of relative dimension `n` in Mathlib's sense
(locally standard smooth of relative dimension `n`) has `Ω_{X/Y}` locally free of rank `n`: on
an affine open where `Γ(Y, U) → Γ(X, V)` is standard smooth of relative dimension `n`,
`Ω_{X/Y}|_V ≅ (Ω_{Γ(X, V)/Γ(Y, U)})~` and this module is free of rank `n`.
-/

open CategoryTheory TensorProduct IsLocalRing Module

namespace AlgebraicGeometry

open RelDiffLocal

universe u

/-- **Hartshorne III.10, Example 10.0.2**, general form: for a morphism `f : X ⟶ Y` locally of
finite type with `X` integral and locally Noetherian, `Ω_{X/Y}` is locally free of rank `n` if
and only if `dim_{k(x)} ((Ω_{X/Y})_x ⊗ k(x)) = n` for every `x ∈ X`. -/
theorem Scheme.relativeDifferentials_isLocallyFreeOfRank_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsIntegral X] [IsLocallyNoetherian X] (n : ℕ) :
    (Scheme.relativeDifferentials f).IsLocallyFreeOfRank n ↔
      ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          (Scheme.relativeDifferentials f).presheaf.stalk x) = n :=
  Hartshorne.isLocallyFreeOfRank_iff_forall_finrank_fibre _
    (Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f) n

/-- **Hartshorne III.10, Example 10.0.2.** Let `X` be an integral scheme of finite type over a
field `k` and `f : X ⟶ Y` a morphism of `k`-schemes. Then
`dim_{k(x)} ((Ω_{X/Y})_x ⊗ k(x)) = n` for every `x ∈ X` if and only if `Ω_{X/Y}` is locally free
of rank `n`. -/
theorem Scheme.relativeDifferentials_isLocallyFreeOfRank_iff_of_field {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    [IsIntegral X.left] (f : X ⟶ Y) (n : ℕ) :
    (Scheme.relativeDifferentials f.left).IsLocallyFreeOfRank n ↔
      ∀ x : X.left, finrank (ResidueField (X.left.presheaf.stalk x))
        (ResidueField (X.left.presheaf.stalk x) ⊗[X.left.presheaf.stalk x]
          (Scheme.relativeDifferentials f.left).presheaf.stalk x) = n := by
  have : LocallyOfFiniteType X.hom := hX.1
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  exact Scheme.relativeDifferentials_isLocallyFreeOfRank_iff f.left n

/-- If `f : X ⟶ Y` is smooth of relative dimension `n` (locally standard smooth of relative
dimension `n`), then `Ω_{X/Y}` is locally free of rank `n`. -/
theorem Scheme.relativeDifferentials_isLocallyFreeOfRank_of_smoothOfRelativeDimension
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f] :
    (Scheme.relativeDifferentials f).IsLocallyFreeOfRank n := by
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  let := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) Γ(X, V) := hf
  have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nontrivial Γ(X, V) := Scheme.component_nontrivial X V
  have hrank := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Γ(X, V)) n
  let b := Module.Free.chooseBasis Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)]
  have hι : Cardinal.mk (Module.Free.ChooseBasisIndex Γ(X, V) Ω[Γ(X, V)⁄Γ(Y, U)]) =
      Cardinal.mk (ULift.{u} (Fin n)) := by
    rw [b.mk_eq_rank'', hrank]
    simp
  obtain ⟨eι⟩ := Cardinal.eq.mp hι
  let E : Ω[Γ(X, V)⁄Γ(Y, U)] ≃ₗ[Γ(X, V)] (ULift.{u} (Fin n) →₀ Γ(X, V)) :=
    b.repr ≪≫ₗ Finsupp.domLCongr eι
  let β : Hartshorne.specRestriction (Scheme.relativeDifferentials f) ⟨V, hV⟩ ≅
      SheafOfModules.free (ULift.{u} (Fin n)) :=
    affineIso f ⟨V, hV⟩ ⟨U, hU⟩ e ≪≫ (tilde.functor Γ(X, V)).mapIso E.toModuleIso ≪≫
      tildeFinsupp _
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  exact ⟨V, hxV, ⟨(Scheme.Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app _ ≪≫
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso β ≪≫
    Scheme.Modules.restrictFreeIso _ _⟩⟩

end AlgebraicGeometry
