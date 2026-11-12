/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AmpleSectionsAffineBasis
import Hartshorne.Scheme.PicardPullback

/-!
# Symmetric and tensor powers of a module with frames of size one

For a sheaf of modules `L` on a ringed space which near every point has a frame consisting of a
single section (for instance an invertible sheaf on a scheme), the canonical epimorphism
`T^d L → S^d L`, `l₁ ⊗ ⋯ ⊗ l_d ↦ l₁ ⋯ l_d`, is an isomorphism: on an open `U` with a frame `e`,
it sends the frame `e ⊗ ⋯ ⊗ e` of `T^d L` to the frame `e^d` of `S^d L`.

So the `d`-th symmetric power of an invertible sheaf is its `d`-th tensor power
`L^{⊗ d}`; this is the identification of `S^d(L)` with `L^d` used for the twist `S · L` of
Hartshorne II.7, Lemma 7.9.

## Main results

* `Hartshorne.Ringed.isIso_moduleSheafTensorToSymmetricPower`: on a ringed space.
* `AlgebraicGeometry.Scheme.Modules.tensorPowerIsoSymmetricPower`: `T^d L ≅ S^d L` for an
  invertible sheaf `L` on a scheme.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

namespace Ringed

open SheafAlgebraOperations ModuleSheafTensor SheafTensorOperations

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- On an open `U` with a frame `e` of size one, the canonical map `T^d F → S^d F` sends the frame
`e ⊗ ⋯ ⊗ e` of `T^d F` to a frame of `S^d F`. -/
theorem isLocalFrame_tensorToSymmetricPower {F : SheafOfModules.{u} (ringCatSheafOf R)}
    {U : Opens X} {e : ULift.{u} (Fin 1) → F.val.presheaf.obj (op U)}
    (he : IsLocalFrame F U e) (d : ℕ) :
    IsLocalFrame (moduleSheafSymmetricPower d F) U (fun _ : ULift.{u} (Fin 1) =>
      sectionsMap (moduleSheafTensorToSymmetricPower F d) U
        ((moduleSheafTensorPowerMultilinear d F).app (op U) (fun _ => e default))) := by
  let : Unique (MonotoneWord (ULift.{u} (Fin 1)) d) :=
    { default := ⟨fun _ => default, monotone_const⟩
      uniq := fun w => Subtype.ext (funext fun _ => Subsingleton.elim _ _) }
  have hS := (he.moduleSheafSymmetricPower d).reindex
    (Equiv.ofUnique (ULift.{u} (Fin 1)) (MonotoneWord (ULift.{u} (Fin 1)) d))
  convert hS using 2 with i
  change (moduleSheafTensorToSymmetricPower F d).val.app (op U)
      ((moduleSheafTensorPowerMultilinear d F).app (op U) (fun _ => e default)) = _
  refine (moduleSheafTensorToSymmetricPower_multilinear F d (op U) (fun _ => e default)).trans ?_
  change (moduleSheafSymmetricPowerUnit d F).app (op U) _ =
    (sheafifyUnit (moduleSheafSymmetricPowerPresheaf d F)).app (op U) _
  congr 2

/-- **`T^d F ≅ S^d F` for a module with frames of size one.** If every point has an open
neighbourhood on which `F` has a frame consisting of a single section, the canonical epimorphism
`T^d F → S^d F` is an isomorphism. -/
theorem isIso_moduleSheafTensorToSymmetricPower {F : SheafOfModules.{u} (ringCatSheafOf R)}
    (hF : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∃ e : ULift.{u} (Fin 1) → F.val.presheaf.obj (op U), IsLocalFrame F U e) (d : ℕ) :
    IsIso (moduleSheafTensorToSymmetricPower F d) := by
  refine modules_isIso_of_locally_bijective _ fun x => ?_
  obtain ⟨U, hxU, e, he⟩ := hF x
  have he' : IsLocalFrame F U (fun _ : ULift.{u} (Fin 1) => e default) := by
    convert he using 1
    funext i
    exact congrArg e (Subsingleton.elim _ _)
  exact ⟨U, hxU, fun V hV => IsLocalFrame.app_bijective_of_map _
    (he'.moduleSheafTensorPower d) (isLocalFrame_tensorToSymmetricPower he d) (fun _ => rfl) hV⟩

end Ringed

end Hartshorne

namespace AlgebraicGeometry.Scheme.Modules

open Hartshorne Hartshorne.SheafTensorOperations

variable {X : Scheme.{u}} (L : X.Modules)

/-- **The `d`-th symmetric power of an invertible sheaf is its `d`-th tensor power**:
for an invertible sheaf `L` on a scheme, the canonical map `L^{⊗ d} → S^d(L)`,
`l₁ ⊗ ⋯ ⊗ l_d ↦ l₁ ⋯ l_d`, is an isomorphism. -/
noncomputable def tensorPowerIsoSymmetricPower (hL : L.IsInvertible) (d : ℕ) :
    moduleSheafTensorPower (R := X.sheaf) d L ≅ moduleSheafSymmetricPower (R := X.sheaf) d L :=
  haveI := Ringed.isIso_moduleSheafTensorToSymmetricPower (R := X.sheaf) (F := L)
    (fun x => by
      classical
      obtain ⟨W, hxW, ⟨α⟩⟩ := hL x
      obtain ⟨β⟩ := (Scheme.Modules.nonempty_restrict_iso_free_iff L W _).mp ⟨α⟩
      exact ⟨W, hxW, _, Ringed.isLocalFrame_of_over_iso (R := X.sheaf) β⟩) d
  asIso (moduleSheafTensorToSymmetricPower (R := X.sheaf) L d)

end AlgebraicGeometry.Scheme.Modules
