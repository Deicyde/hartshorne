/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Hartshorne.Scheme.SymmetricAlgebraSheaf
import Hartshorne.Scheme.QuasicoherentIdealSheafData
import Hartshorne.Intersection.ClosedSubschemeFundamentalCycle

/-!
# The zero scheme of a section of a locally free sheaf

Hartshorne, *Algebraic Geometry*, Appendix A, §3, C6 (p. 431).

For a global section `s` of an `𝒪_X`-module `E`, the *dual map* `s^∨ : E^∨ ⟶ 𝒪_X` sends a local
section `ψ` of `E^∨ = ℋom(E, 𝒪_X)` over `U` to `ψ(s|_U)` (`sectionDualMap`). Its image
`image(s^∨) ⊆ 𝒪_X` (`sectionDualImage`, with the monomorphism `sectionDualImageι`) is the ideal
sheaf of the zero scheme `Z(s)`, and the cokernel of `s^∨` (`sectionDualCokernel`) is
`𝒪_X / image(s^∨)`.

For `E` locally free of finite rank, `E^∨` is locally free of finite rank
(`Ringed.IsFiniteLocallyFree.moduleSheafDual`), hence quasi-coherent, so the images
`s^∨(Γ(U, E^∨)) ⊆ Γ(U, 𝒪_X)` on affine opens form ideal data (`sectionZeroIdeal`). The zero
scheme `Z(s)` (`sectionZeroScheme`) is the closed subscheme they define, with closed immersion
`sectionZeroSchemeι`. On every affine open `U`:

* the ideal of `Z(s)` is the image of `s^∨` on sections over `U`
  (`mem_sectionZeroIdeal_iff`), which is also the module of sections over `U` of the ideal sheaf
  `image(s^∨)` (`sectionZeroIdeal_ideal_eq_range_sectionDualImageι`);
* the sequence `Γ(U, E^∨) ⟶ Γ(U, 𝒪_X) ⟶ Γ(Z(s) ∩ U, 𝒪_{Z(s)}) ⟶ 0` is exact
  (`ker_sectionZeroSchemeι_app`, `sectionZeroSchemeι_app_surjective`).

On a Noetherian scheme the associated codimension-`r` cycle of `Z(s)` is its fundamental cycle
(`sectionZeroCycle`), built from the lengths of the local rings at the generic points of its
components rather than from the reduced zero set.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

namespace Hartshorne

variable {X : Scheme.{u}} {E : X.Modules}

/-- The dual map `s^∨ : E^∨ ⟶ 𝒪_X` of a global section `s` of `E`: on an open `U` it sends a
local section `ψ` of `E^∨` to `ψ(s|_U)`. -/
noncomputable def sectionDualMap (s : Γ(E, ⊤)) :
    Ringed.moduleSheafDual (R := X.sheaf) E ⟶ Ringed.structureModule X.sheaf :=
  Ringed.modulesHomMk
    (fun U => Ringed.moduleSheafHomEval (Ringed.doubleDualSection E s) (le_top : U ≤ ⊤))
    (fun _ _ i ψ => Ringed.moduleSheafHomEval_natural (Ringed.doubleDualSection E s) le_top i ψ)

/-- The dual map evaluates a local section of `E^∨` at the restriction of `s`. -/
lemma sectionDualMap_app (s : Γ(E, ⊤)) (U : X.Opens)
    (ψ : Γ(Ringed.moduleSheafDual (R := X.sheaf) E, U)) :
    Ringed.sectionsMap (sectionDualMap s) U ψ =
      Ringed.dualEval ψ (le_refl U) (E.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := rfl

/-- The image `image(s^∨)` of the dual map of a section, as an `𝒪_X`-module. -/
noncomputable def sectionDualImage (s : Γ(E, ⊤)) : SheafOfModules.{u} (ringCatSheafOf X.sheaf) :=
  image (sectionDualMap s)

/-- The inclusion `image(s^∨) ⟶ 𝒪_X` of the image of the dual map into the structure sheaf. -/
noncomputable def sectionDualImageι (s : Γ(E, ⊤)) :
    sectionDualImage s ⟶ Ringed.structureModule X.sheaf :=
  image.ι (sectionDualMap s)

instance (s : Γ(E, ⊤)) : Mono (sectionDualImageι s) :=
  inferInstanceAs (Mono (image.ι (sectionDualMap s)))

/-- The dual map factors through its image. -/
lemma sectionDualMap_factor (s : Γ(E, ⊤)) :
    factorThruImage (sectionDualMap s) ≫ sectionDualImageι s = sectionDualMap s :=
  image.fac _

/-- The cokernel `𝒪_X / image(s^∨)` of the dual map of a section. -/
noncomputable def sectionDualCokernel (s : Γ(E, ⊤)) :
    SheafOfModules.{u} (ringCatSheafOf X.sheaf) :=
  cokernel (sectionDualMap s)

/-- **The dual of a locally free module of finite rank is locally free of finite rank**: the dual
frame of a local frame is a local frame. -/
theorem Ringed.IsFiniteLocallyFree.moduleSheafDual {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    {F : SheafOfModules.{u} (ringCatSheafOf R)} (hF : Ringed.IsFiniteLocallyFree F) :
    Ringed.IsFiniteLocallyFree (Ringed.moduleSheafDual F) := by
  classical
  intro x
  obtain ⟨U, hx, n, ⟨α⟩⟩ := hF x
  exact ⟨U, hx, n, Ringed.nonempty_over_iso_free_of_isLocalFrame
    (Ringed.isLocalFrame_of_over_iso α).dual⟩

section ZeroScheme

variable (hE : Ringed.IsFiniteLocallyFree (R := X.sheaf) E)

include hE in
/-- The dual of a locally free module of finite rank on a scheme is quasi-coherent. -/
theorem isQuasicoherent_moduleSheafDual :
    SheafOfModules.IsQuasicoherent.{u, u, u} (R := X.ringCatSheaf)
      (Ringed.moduleSheafDual (R := X.sheaf) E : X.Modules) :=
  hE.moduleSheafDual.isQuasicoherent

/-- **The ideal of the zero scheme of a section.** For `E` locally free of finite rank and a
global section `s`, the ideal data whose ideal over an affine open `U` is the image
`s^∨(Γ(U, E^∨)) ⊆ Γ(U, 𝒪_X)` of the dual map. -/
noncomputable def sectionZeroIdeal (s : Γ(E, ⊤)) : X.IdealSheafData :=
  have := isQuasicoherent_moduleSheafDual hE
  idealSheafDataOfHom (sectionDualMap s)

/-- **The zero scheme `Z(s)` of a section `s` of a locally free sheaf of finite rank** (Hartshorne,
Appendix A, §3, C6): the closed subscheme of `X` defined by the ideal sheaf `image(s^∨)`. -/
noncomputable def sectionZeroScheme (s : Γ(E, ⊤)) : Scheme.{u} :=
  (sectionZeroIdeal hE s).subscheme

/-- The closed immersion `Z(s) ⟶ X`. -/
noncomputable def sectionZeroSchemeι (s : Γ(E, ⊤)) : sectionZeroScheme hE s ⟶ X :=
  (sectionZeroIdeal hE s).subschemeι

instance (s : Γ(E, ⊤)) : IsClosedImmersion (sectionZeroSchemeι hE s) :=
  inferInstanceAs (IsClosedImmersion (sectionZeroIdeal hE s).subschemeι)

/-- Over an affine open `U`, the ideal of `Z(s)` consists of the values `ψ(s|_U)` of the local
sections `ψ` of `E^∨` over `U`, i.e. it is the image of `s^∨` on sections over `U`. -/
theorem mem_sectionZeroIdeal_iff (s : Γ(E, ⊤)) (U : X.affineOpens) (t : Γ(X, U)) :
    t ∈ (sectionZeroIdeal hE s).ideal U ↔
      ∃ ψ : Γ(Ringed.moduleSheafDual (R := X.sheaf) E, U),
        Ringed.dualEval ψ (le_refl (U : X.Opens))
          (E.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op s) = t :=
  Iff.rfl

/-- Over an affine open `U`, the ideal of `Z(s)` is the module of sections over `U` of the ideal
sheaf `image(s^∨) ⊆ 𝒪_X`. -/
theorem sectionZeroIdeal_ideal_eq_range_sectionDualImageι (s : Γ(E, ⊤)) (U : X.affineOpens) :
    (sectionZeroIdeal hE s).ideal U = homRangeIdeal (sectionDualImageι s) U := by
  have := isQuasicoherent_moduleSheafDual hE
  change homRangeIdeal (sectionDualMap s) U = _
  have hepi : Epi (factorThruImage (sectionDualMap s)) := inferInstance
  rw [← sectionDualMap_factor s]
  exact @homRangeIdeal_eq_of_epi_comp X _ _ _ _ hepi _ _ U.2

/-- The ideal sheaf of the closed immersion `Z(s) ⟶ X` is the ideal of `Z(s)`. -/
@[simp]
theorem ker_sectionZeroSchemeι (s : Γ(E, ⊤)) :
    (sectionZeroSchemeι hE s).ker = sectionZeroIdeal hE s :=
  (sectionZeroIdeal hE s).ker_subschemeι

/-- **The right exact sequence `E^∨ → 𝒪_X → 𝒪_{Z(s)} → 0` on affine opens, exactness in the
middle.** Over an affine open `U`, a function on `U` vanishes on `Z(s) ∩ U` exactly when it is
of the form `ψ(s|_U)` for a local section `ψ` of `E^∨` over `U`. -/
theorem ker_sectionZeroSchemeι_app (s : Γ(E, ⊤)) (U : X.affineOpens) :
    RingHom.ker ((sectionZeroSchemeι hE s).app U).hom = (sectionZeroIdeal hE s).ideal U :=
  (sectionZeroIdeal hE s).ker_subschemeι_app U

/-- **The right exact sequence `E^∨ → 𝒪_X → 𝒪_{Z(s)} → 0` on affine opens, surjectivity.** -/
theorem sectionZeroSchemeι_app_surjective (s : Γ(E, ⊤)) (U : X.affineOpens) :
    Function.Surjective ((sectionZeroSchemeι hE s).app U) :=
  (sectionZeroIdeal hE s).subschemeι_app_surjective U

/-- The cycle associated to the zero scheme `Z(s)` on a Noetherian scheme: the codimension-`r`
fundamental cycle of `Z(s)`, whose coefficients are the lengths of the local rings of `Z(s)` at
the generic points of its irreducible components of codimension `r`. -/
noncomputable def sectionZeroCycle [IsNoetherian X] (s : Γ(E, ⊤)) (r : ℕ) :
    codimensionCycles X r :=
  closedSubschemeFundamentalCycle (sectionZeroSchemeι hE s) r

end ZeroScheme

end Hartshorne
