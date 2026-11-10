/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity
import Hartshorne.Scheme.LocallyFreeInvertible
import Mathlib.Topology.KrullDimension

/-!
# Differentials and Frobenius: shared helpers

General facts used for Frobenius morphisms in characteristic `p`: derivations kill `p`-th powers
where `p` vanishes, a vanishing first map of the transitivity sequence makes
`Ω_{X/Z} ⟶ Ω_{X/Y}` an isomorphism, local freeness of rank `r` is invariant under isomorphism,
`p = 0` in every ring of sections of a scheme over a field of characteristic `p`, and a nonempty
subsingleton space has topological Krull dimension zero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace PresheafOfModules.Derivation

variable {C : Type*} [Category C] {D : Type*} [Category D]
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {φ : S ⟶ F.op ⋙ R}

/-- The Leibniz rule for powers: `d(a ^ (n + 1)) = (n + 1) a ^ n · d a`. -/
theorem d_pow_succ (d : M.Derivation φ) {X : Dᵒᵖ} (a : R.obj X) (n : ℕ) :
    d.d (a ^ (n + 1)) = (((n + 1 : ℕ) : R.obj X) * a ^ n) • d.d a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, d.d_mul, ih, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- A derivation kills `p`-th powers where the prime `p` vanishes. -/
theorem d_pow_eq_zero (d : M.Derivation φ) {X : Dᵒᵖ} (a : R.obj X) {p : ℕ} [Fact p.Prime]
    (hp : ((p : ℕ) : R.obj X) = 0) : d.d (a ^ p) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 :=
    ⟨p - 1, (Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos).symm⟩
  rw [d_pow_succ, hp, zero_mul, zero_smul]

end PresheafOfModules.Derivation

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- If `d_{X/Z}` kills `f^♯ b` for every local section `b` of `𝒪_Y`, then the first map
`f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` of the transitivity sequence vanishes. -/
theorem pullbackRelativeDifferentialsToComp_eq_zero_of_d (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : ∀ (V : Y.Opensᵒᵖ) (b : Y.presheaf.obj V),
      (relativeDifferentialsDerivation (f ≫ g)).d (f.c.app V b) = 0) :
    pullbackRelativeDifferentialsToComp f g = 0 := by
  apply ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [pullbackRelativeDifferentialsToComp_homEquiv, Adjunction.homEquiv_unit, Functor.map_zero,
    comp_zero]
  apply (relativeDifferentialsHomEquiv g _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext V b
  change (relativeDifferentialsToPushforwardComp f g).val.app V
    ((relativeDifferentialsDerivation g).d b) = 0
  exact (relativeDifferentialsToPushforwardComp_d f g V b).trans (h V b)

/-- When the first map of the transitivity sequence vanishes, `Ω_{X/Z} ⟶ Ω_{X/Y}` is an
isomorphism. -/
theorem isIso_relativeDifferentialsCompToLeft_of_eq_zero (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : pullbackRelativeDifferentialsToComp f g = 0) :
    IsIso (relativeDifferentialsCompToLeft f g) := by
  let hc := relativeDifferentialsTransitivityIsColimit f g
  let inv : relativeDifferentials f ⟶ relativeDifferentials (f ≫ g) :=
    hc.desc (CokernelCofork.ofπ (𝟙 _) (by rw [h, zero_comp]))
  have h₁ : relativeDifferentialsCompToLeft f g ≫ inv = 𝟙 _ :=
    hc.fac (CokernelCofork.ofπ (𝟙 _) (by rw [h, zero_comp])) WalkingParallelPair.one
  refine ⟨inv, h₁, ?_⟩
  apply Cofork.IsColimit.hom_ext hc
  change relativeDifferentialsCompToLeft f g ≫ inv ≫ relativeDifferentialsCompToLeft f g =
    relativeDifferentialsCompToLeft f g ≫ 𝟙 _
  rw [← Category.assoc, h₁, Category.id_comp, Category.comp_id]

/-- Locally free of rank `r` is invariant under isomorphism of module sheaves. -/
theorem Modules.isLocallyFreeOfRank_of_iso {M N : X.Modules} (e : M ≅ N) {r : ℕ}
    (h : M.IsLocallyFreeOfRank r) : N.IsLocallyFreeOfRank r := by
  intro x
  obtain ⟨U, hx, ⟨e'⟩⟩ := h x
  exact ⟨U, hx, ⟨(Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ e'⟩⟩

/-- On a scheme over a field of characteristic `p`, the integer `p` vanishes in every ring of
sections. -/
theorem natCast_eq_zero_of_hom_spec {K : Type u} [Field K] {p : ℕ} [CharP K p]
    (s : X ⟶ Spec (.of K)) (U : X.Opens) : ((p : ℕ) : Γ(X, U)) = 0 := by
  have := map_natCast ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)) p
  rw [CharP.cast_eq_zero, map_zero] at this
  exact this.symm

/-- A relative derivation kills `p`-th powers on an open where `p` vanishes. -/
theorem relativeDifferentialsDerivation_d_pow_eq_zero (k : X ⟶ Z) {p : ℕ} [Fact p.Prime]
    {U : X.Opensᵒᵖ} (hp : ((p : ℕ) : Γ(X, U.unop)) = 0) (a : Γ(X, U.unop)) :
    (relativeDifferentialsDerivation k).d (a ^ p) = 0 := by
  exact PresheafOfModules.Derivation.d_pow_eq_zero (relativeDifferentialsDerivation k)
    (X := U) a hp

end AlgebraicGeometry.Scheme

namespace Hartshorne

/-- A nonempty subsingleton space has topological Krull dimension zero. -/
theorem topologicalKrullDim_eq_zero_of_subsingleton (T : Type*) [TopologicalSpace T]
    [Subsingleton T] [Nonempty T] : topologicalKrullDim T = 0 := by
  refine le_antisymm (topologicalKrullDim_zero_of_discreteTopology T) ?_
  obtain ⟨x⟩ := ‹Nonempty T›
  have : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

end Hartshorne
