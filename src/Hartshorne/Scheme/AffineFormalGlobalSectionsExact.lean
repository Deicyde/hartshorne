/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModuleReduction
import Hartshorne.Scheme.SheafCechOneLift

/-!
# Exactness of global sections on an affine formal scheme

Hartshorne, *Algebraic Geometry*, II.9, Exercise 9.3(a,b) (pp. 199–200): on an affine Noetherian
formal scheme `X`, global sections of a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of
`𝒪_X`-modules with `F'` coherent form a short exact sequence.

This file proves the surjectivity `Γ(X, F) ⟶ Γ(X, F'')` for a Noetherian formal scheme `X` with an
ideal of definition `J`, under two hypotheses on the thickenings `Xₙ = (X, 𝒪_X / J ^ (n + 1))`:
every `Xₙ` is affine, and the transition maps
`Γ(X, F' / J ^ (n + 2) F') ⟶ Γ(X, F' / J ^ (n + 1) F')` are surjective.

* `Hartshorne.IsIdealOfDefinition.cechOneVanishes_powQuotient`: if `Xₙ` is affine, every Čech
  1-cocycle of `F' / J ^ (n + 1) F'` on a cover of `X` is a coboundary. The module is the
  pushforward of the coherent `𝒪_{Xₙ}`-module `F'ₙ` (Proposition 9.6(a)), and on the affine scheme
  `Xₙ` global sections lift along every monomorphism out of `F'ₙ` (Proposition 5.6).
* `Hartshorne.IsIdealOfDefinition.globalSections_surjective_of_isAffine`: the surjectivity. A
  global section of `F''` lifts locally; since `X` is quasi-compact, finitely many opens suffice.
  As `F' = lim_n F' / J ^ (n + 1) F'` (Proposition 9.6(a)), the Čech 1-cocycles of `F'` on that
  cover are coboundaries by the Mittag–Leffler argument (Proposition 9.1(b)), so the local lifts
  can be corrected to glue.
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J)

/-- On an affine scheme, global sections lift along every monomorphism out of a quasi-coherent
module (Hartshorne II, Proposition 5.6). -/
lemma surjective_cokernel_of_isAffine {Y : Scheme.{u}} [IsAffine Y] (G : Y.Modules)
    [G.IsQuasicoherent] (P : Y.Modules) (f : G ⟶ P) (hf : Mono f) :
    Function.Surjective ((sheafOfModulesAbMap (cokernel.π f)).app (op ⊤)) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
  have : S.X₁.IsQuasicoherent := ‹_›
  exact (ModuleCat.epi_iff_surjective _).mp (affine_globalSections_shortExact S hS).epi_g

/-- **Čech `H¹` of `F / J ^ (n + 1) F`.** Let `F` be a coherent module on a Noetherian formal
scheme with ideal of definition `J`, and suppose the scheme `Xₙ = (X, 𝒪_X / J ^ (n + 1))` is
affine. Then on every cover of `X`, every Čech 1-cocycle of `F / J ^ (n + 1) F` is a coboundary:
this module is the pushforward of the coherent `𝒪_{Xₙ}`-module `Fₙ`, on the same space, and on the
affine scheme `Xₙ` global sections lift along monomorphisms out of `Fₙ`. -/
theorem cechOneVanishes_powQuotient
    {F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)}
    (hF : IsCoherentFormalModule F) (n : ℕ) [IsAffine (h.pow_succ n).quotientScheme] {ι : Type}
    (U : ι → Opens X.carrier) (hU : iSup U = ⊤) :
    CechOneVanishes (J.powQuotient F n).val.presheaf U := by
  have hcoh := (h.reconstruction hF).1 n
  have : (h.reduction F n).IsQuasicoherent := hcoh.isQuasicoherent
  have hG : CechOneVanishes (h.reduction F n).val.presheaf
      (show ι → Opens (h.pow_succ n).quotientScheme from U) :=
    cechOneVanishes_of_surjective_cokernel (h.reduction F n) _ hU
      (surjective_cokernel_of_isAffine _)
  have hiso := h.isIso_toReduction F n
  exact CechOneVanishes.of_iso ((PresheafOfModules.toPresheaf _).mapIso
    ((SheafOfModules.forget _).mapIso (asIso (h.toReduction F n)))).symm hG

/-- **Surjectivity of global sections under affine thickenings.** Let `X` be a Noetherian formal
scheme with ideal of definition `J`, `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` a short exact sequence of
`𝒪_X`-modules with `F'` coherent. Suppose every `Xₙ = (X, 𝒪_X / J ^ (n + 1))` is affine and the
transition maps `Γ(X, F' / J ^ (n + 2) F') ⟶ Γ(X, F' / J ^ (n + 1) F')` are surjective. Then
`Γ(X, F) ⟶ Γ(X, F'')` is surjective. -/
theorem globalSections_surjective_of_isAffine
    {S : ShortComplex (SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace))}
    (hS : S.ShortExact) (hF : IsCoherentFormalModule S.X₁)
    (haff : ∀ n, IsAffine (h.pow_succ n).quotientScheme)
    (hML : ∀ n, Function.Surjective
      ((sheafOfModulesAbMap (J.powQuotientMap S.X₁ n)).app (op ⊤))) :
    Function.Surjective ((sheafOfModulesAbMap S.g).app (op ⊤)) := by
  intro s
  have : Epi S.g := hS.epi_g
  have hloc : ∀ x : X.carrier, ∃ V : Opens X.carrier, x ∈ V ∧
      ∃ t : S.X₂.val.presheaf.obj (op V),
        (sheafOfModulesAbMap S.g).app _ t = presheafRes S.X₃.val.presheaf le_top s := by
    intro x
    obtain ⟨V, hVU, hxV, t, ht⟩ := @sheafOfModules_exists_local_lift _
      X.toLocallyRingedSpace.sheaf _ _ S.g this ⊤ s x trivial
    exact ⟨V, hxV, t, ht⟩
  choose V hxV hlift using hloc
  have : CompactSpace X.carrier := (inferInstance : CompactSpace h.quotientScheme)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X.carrier))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  let e := t.equivFin
  let U : Fin t.card → Opens X.carrier := fun i => V (e.symm i)
  have hU : iSup U = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    refine Opens.mem_iSup.mpr ⟨e ⟨x, hx⟩, ?_⟩
    change y ∈ V (e.symm (e ⟨x, hx⟩))
    rw [Equiv.symm_apply_apply]
    exact hy
  refine sheafOfModules_exists_lift_of_cechOneVanishes hS hU ?_ s fun i => hlift _
  -- Čech vanishing for `F'` on `U`, from the inverse limit `F' = lim_n F' / J ^ (n + 1) F'`
  have hiso : IsIso ((limit.isLimit (J.powQuotientDiagram S.X₁)).lift (J.powQuotientCone S.X₁)) :=
    (h.reconstruction hF).2.2
  have hc : IsLimit (J.powQuotientCone S.X₁) :=
    IsLimit.ofPointIso (limit.isLimit (J.powQuotientDiagram S.X₁))
  let Q := J.powQuotientDiagram S.X₁ ⋙ SheafOfModules.toSheaf _
  have := cechOneVanishes_of_isLimit Q ((SheafOfModules.toSheaf _).mapCone (J.powQuotientCone S.X₁))
    (fun W x y hxy => sheafOfModules_limit_ext hc W fun j => hxy j.unop)
    (fun W y hy => by
      obtain ⟨x, hx⟩ := sheafOfModules_limit_exists hc W (fun j => y j.unop)
        (fun j j' g => hy g)
      exact ⟨x, fun n => hx (op n)⟩)
    hU (fun n => (haveI := haff n; h.cechOneVanishes_powQuotient hF n U hU))
    (fun n => by
      have hmap := Functor.ofOpSequence_map_homOfLE_succ (J.powQuotientMap S.X₁) n
      change Function.Surjective ((sheafOfModulesAbMap
        ((J.powQuotientDiagram S.X₁).map (homOfLE (Nat.le_succ n)).op)).app (op ⊤))
      rw [show (J.powQuotientDiagram S.X₁).map (homOfLE (Nat.le_succ n)).op =
        J.powQuotientMap S.X₁ n from hmap]
      exact hML n)
  exact this

end IsIdealOfDefinition

end Hartshorne
