/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModuleReconstruction

/-!
# Quotients of the completion of a module on a scheme

Hartshorne, *Algebraic Geometry*, II, Corollary 9.8 (p. 198), the quotient statement.

Let `X` be a scheme, `I` a quasi-coherent ideal subsheaf of `𝒪_X` cutting out the closed subscheme
`Y`, `X̂` the formal completion of `X` along `Y`, a locally ringed space on `|Y|`, and
`J = ker (𝒪_{X̂} ⟶ 𝒪_Y)` the completed ideal of `I`
(`QuasicoherentIdealSubsheaf.formalCompletionIdealSubsheaf I`, whose ideals of sections are
`QuasicoherentIdealSubsheaf.formalCompletionIdeal I`; on an affine open `U = Spec A` with
`I(U) = 𝔞` it is the completion of `𝔞` in the `𝔞`-adic completion of `A`). For an `𝒪_X`-module `F`
let `F̂ = lim_n (F / I ^ (n + 1) F)|_Y` be its completion, a module over `𝒪_{X̂}`. Here
`(F / I ^ (n + 1) F)|_Y` (`QuasicoherentIdealSubsheaf.moduleCompletionObj I F n`) is the quotient
`F / I ^ (n + 1) F`, a module supported on `|Y|`, restricted to `|Y|` and viewed as an
`𝒪_{X̂}`-module through `𝒪_{X̂} ⟶ 𝒪_{Y_(n+1)}`.

* `Hartshorne.QuasicoherentIdealSubsheaf.powQuotientToModuleCompletionObj I F n`: the canonical map
  `F̂ / J ^ (n + 1) F̂ ⟶ (F / I ^ (n + 1) F)|_Y` of `𝒪_{X̂}`-modules, induced by the projection
  `F̂ ⟶ (F / I ^ (n + 1) F)|_Y`, which kills `J ^ (n + 1) F̂`
  (`powQuotientπ_powQuotientToModuleCompletionObj`).
* `Hartshorne.QuasicoherentIdealSubsheaf.isIso_powQuotientToModuleCompletionObj`: for `X` locally
  Noetherian and `F` quasi-coherent, this map is an isomorphism for every `n ≥ 0`.

Hartshorne states the corollary for `X` Noetherian and `F` coherent; the result here supplements it
to `X` locally Noetherian and `F` quasi-coherent. The proof identifies the kernel of
`F̂ ⟶ (F / I ^ (n + 1) F)|_Y` with `J ^ (n + 1) F̂` and shows that this projection is an
epimorphism (`QuasicoherentIdealSubsheaf.moduleCompletionPowShortComplex_exact`,
`QuasicoherentIdealSubsheaf.epi_moduleCompletionπ'`), both checked on the opens `U ∩ |Y|`, `U` an
affine open of `X`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace Hartshorne

universe u

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X) [IsLocallyNoetherian X] (F : X.Modules)

/-- **The canonical map `F̂ / J ^ (n + 1) F̂ ⟶ (F / I ^ (n + 1) F)|_Y`** of `𝒪_{X̂}`-modules on
`|Y|`, where `J = ker (𝒪_{X̂} ⟶ 𝒪_Y)` is the completed ideal of `I`: the map induced by the
projection `F̂ ⟶ (F / I ^ (n + 1) F)|_Y`, which vanishes on `J ^ (n + 1) F̂`. -/
def powQuotientToModuleCompletionObj (n : ℕ) :
    I.formalCompletionIdealSubsheaf.powQuotient (I.moduleCompletion' F) n ⟶
      I.moduleCompletionObj' F n :=
  cokernel.desc _ (I.moduleCompletionπ' F n) (I.smulι_moduleCompletionπ F n)

/-- The canonical map `F̂ / J ^ (n + 1) F̂ ⟶ (F / I ^ (n + 1) F)|_Y` composed with the projection
`F̂ ⟶ F̂ / J ^ (n + 1) F̂` is the projection `F̂ ⟶ (F / I ^ (n + 1) F)|_Y`. -/
@[reassoc (attr := simp)]
lemma powQuotientπ_powQuotientToModuleCompletionObj (n : ℕ) :
    I.formalCompletionIdealSubsheaf.powQuotientπ (I.moduleCompletion' F) n ≫
      I.powQuotientToModuleCompletionObj F n = I.moduleCompletionπ' F n :=
  cokernel.π_desc _ _ _

/-- **Quotients of the completion of a module** (Hartshorne II, Corollary 9.8, there for `X`
Noetherian and `F` coherent). Let `X` be locally Noetherian, `I` a quasi-coherent ideal subsheaf
of `𝒪_X` cutting out `Y`, `J = ker (𝒪_{X̂} ⟶ 𝒪_Y)` the completed ideal of `I` on the formal
completion `X̂` along `Y`, and `F` a quasi-coherent `𝒪_X`-module with completion `F̂`. For every
`n ≥ 0`, the canonical map `F̂ / J ^ (n + 1) F̂ ⟶ (F / I ^ (n + 1) F)|_Y` induced by the projection
`F̂ ⟶ (F / I ^ (n + 1) F)|_Y` is an isomorphism of `𝒪_{X̂}`-modules on the common support `|Y|`. -/
theorem isIso_powQuotientToModuleCompletionObj [F.IsQuasicoherent] (n : ℕ) :
    IsIso (I.powQuotientToModuleCompletionObj F n) := by
  have h : I.powQuotientToModuleCompletionObj F n = (I.powQuotientModuleCompletionIso F n).hom :=
    coequalizer.hom_ext ((I.powQuotientπ_powQuotientToModuleCompletionObj F n).trans
      (I.powQuotientπ_powQuotientModuleCompletionIso_hom F n).symm)
  rw [h]
  infer_instance

end QuasicoherentIdealSubsheaf

end Hartshorne
