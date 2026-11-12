/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.NoetherianFormalScheme

/-!
# Completions of Noetherian schemes are Noetherian formal schemes

Hartshorne, *Algebraic Geometry*, II.9, Example 9.3.2 (p. 195): the completion of a Noetherian
scheme along a closed subscheme is a Noetherian formal scheme; such formal schemes are called
algebraizable.

Closed subschemes of a scheme `X` are represented by quasi-coherent ideal subsheaves of `𝒪_X`.
Since `Hartshorne.IsNoetherianFormalScheme` allows non-affine Noetherian ambient schemes in its
charts, the one-member cover by the whole completion witnesses the property.

* `Hartshorne.IsAlgebraizable X`: the locally ringed space `X` is isomorphic to the completion of
  a Noetherian scheme along a closed subscheme.
* `Hartshorne.IsAlgebraizable.isNoetherianFormalScheme`: an algebraizable locally ringed space is a
  Noetherian formal scheme.
* `Hartshorne.QuasicoherentIdealSubsheaf.isNoetherianFormalScheme_formalCompletion`: the completion
  of a Noetherian scheme along a closed subscheme is a Noetherian formal scheme.
* `Hartshorne.QuasicoherentIdealSubsheaf.toNoetherianFormalScheme`: that completion as an object of
  the category of Noetherian formal schemes.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hartshorne

universe u

/-- **Algebraizable formal schemes** (Hartshorne II.9, Example 9.3.2, p. 195): a locally ringed
space is algebraizable when it is isomorphic, as a locally ringed space, to the formal completion
of a Noetherian scheme along a closed subscheme (given by a quasi-coherent ideal subsheaf). -/
def IsAlgebraizable (X : LocallyRingedSpace.{u}) : Prop :=
  ∃ (Y : Scheme.{u}) (_ : IsNoetherian Y) (I : QuasicoherentIdealSubsheaf Y),
    Nonempty (X ≅ I.formalCompletion)

/-- An algebraizable locally ringed space is a Noetherian formal scheme (cf. Hartshorne II.9,
Example 9.3.2, p. 195): the whole space is a one-member cover by a completion of a Noetherian
scheme. -/
theorem IsAlgebraizable.isNoetherianFormalScheme {X : LocallyRingedSpace.{u}}
    (hX : IsAlgebraizable X) : IsNoetherianFormalScheme X := by
  obtain ⟨Y, hY, I, ⟨e⟩⟩ := hX
  exact ⟨Unit, inferInstance, fun _ => ⊤, iSup_const, fun _ =>
    ⟨Y, hY, I, ⟨X.restrictTopIso ≪≫ e⟩⟩⟩

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} [IsNoetherian X] (I : QuasicoherentIdealSubsheaf X)

/-- The completion of a Noetherian scheme along a closed subscheme is algebraizable
(Hartshorne II.9, Example 9.3.2, p. 195). -/
theorem isAlgebraizable_formalCompletion : IsAlgebraizable I.formalCompletion :=
  ⟨X, inferInstance, I, ⟨Iso.refl _⟩⟩

/-- **Completions are Noetherian formal schemes** (Hartshorne II.9, Example 9.3.2, p. 195): the
completion `X̂` of a Noetherian scheme `X` along a closed subscheme is a Noetherian formal
scheme. -/
theorem isNoetherianFormalScheme_formalCompletion :
    IsNoetherianFormalScheme I.formalCompletion :=
  I.isAlgebraizable_formalCompletion.isNoetherianFormalScheme

/-- The completion of a Noetherian scheme along a closed subscheme, as a Noetherian formal scheme
(Hartshorne II.9, Example 9.3.2, p. 195). -/
def toNoetherianFormalScheme : NoetherianFormalScheme.{u} where
  toLocallyRingedSpace := I.formalCompletion
  isNoetherianFormalScheme := I.isNoetherianFormalScheme_formalCompletion

end QuasicoherentIdealSubsheaf

end Hartshorne
