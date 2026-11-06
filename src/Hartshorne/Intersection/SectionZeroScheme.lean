/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteLocallyFreeDuality

/-!
# The dual map of a section and its image (partial)

Hartshorne, *Algebraic Geometry*, Appendix A, §3, C6 (p. 431).

For a global section `s` of an `𝒪_X`-module `E`, the *dual map* `s^∨ : E^∨ ⟶ 𝒪_X` sends a local
section `ψ` of `E^∨ = ℋom(E, 𝒪_X)` over `U` to `ψ(s|_U)` (`sectionDualMap`). Its image
`image(s^∨) ⊆ 𝒪_X` (`sectionDualImage`, with the monomorphism `sectionDualImageι`) is the ideal
sheaf of the zero scheme `Z(s)`, and the cokernel of `s^∨` (`sectionDualCokernel`) is
`𝒪_X / image(s^∨)`, the module of the right-exact sequence `E^∨ → 𝒪_X → 𝒪_{Z(s)} → 0`.

This file contains only the module-level part of the construction. Turning the image into a
closed subscheme requires the correspondence between quasi-coherent ideal subsheaves of `𝒪_X`
and `Scheme.IdealSheafData`, which is not yet available.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

namespace Hartshorne

variable {X : Scheme.{u}} {E : X.Modules}

/-- The dual map `s^∨ : E^∨ ⟶ 𝒪_X` of a global section `s` of `E`: on an open `U` it sends a
local section `ψ` of `E^∨` to `ψ(s|_U)`. -/
noncomputable def sectionDualMap (s : Γ(E, ⊤)) : moduleSheafDual E ⟶ structureModule X :=
  modulesHomMk (fun U => moduleSheafHomEval (doubleDualSection E s) (le_top : U ≤ ⊤))
    (fun _ _ i ψ => moduleSheafHomEval_natural (doubleDualSection E s) le_top i ψ)

/-- The dual map evaluates a local section of `E^∨` at the restriction of `s`. -/
lemma sectionDualMap_app (s : Γ(E, ⊤)) (U : X.Opens) (ψ : Γ(moduleSheafDual E, U)) :
    (sectionDualMap s).app U ψ =
      dualEval ψ (le_refl U) (E.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := rfl

/-- The image `image(s^∨)` of the dual map of a section, as an `𝒪_X`-module. -/
noncomputable def sectionDualImage (s : Γ(E, ⊤)) : X.Modules :=
  image (sectionDualMap s)

/-- The inclusion `image(s^∨) ⟶ 𝒪_X` of the image of the dual map into the structure sheaf. -/
noncomputable def sectionDualImageι (s : Γ(E, ⊤)) : sectionDualImage s ⟶ structureModule X :=
  image.ι (sectionDualMap s)

instance (s : Γ(E, ⊤)) : Mono (sectionDualImageι s) :=
  inferInstanceAs (Mono (image.ι (sectionDualMap s)))

/-- The dual map factors through its image. -/
lemma sectionDualMap_factor (s : Γ(E, ⊤)) :
    factorThruImage (sectionDualMap s) ≫ sectionDualImageι s = sectionDualMap s :=
  image.fac _

/-- The cokernel `𝒪_X / image(s^∨)` of the dual map of a section. -/
noncomputable def sectionDualCokernel (s : Γ(E, ⊤)) : X.Modules :=
  cokernel (sectionDualMap s)

end Hartshorne
