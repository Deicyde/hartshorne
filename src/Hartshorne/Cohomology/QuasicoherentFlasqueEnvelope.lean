/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.TildeInjectiveFlasque
import Hartshorne.Scheme.QcqsPushforwardQuasicoherent
import Hartshorne.Scheme.AffineGlobalSectionsExact
import Hartshorne.Scheme.AffineTildeLocalization
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Quasi-coherent flasque envelopes

Hartshorne, *Algebraic Geometry*, III, Corollary 3.6 (p. 215).

On a Noetherian scheme `X`, every quasi-coherent `𝒪_X`-module `F` embeds into a flasque
quasi-coherent `𝒪_X`-module (`Hartshorne.exists_mono_isFlasque_isQuasicoherent`).

## Proof

Cover `X` by finitely many affine opens `fᵢ : Spec Aᵢ ⟶ X`. Then `F|_{Spec Aᵢ} ≅ M̃ᵢ` with
`Mᵢ = Γ(Spec Aᵢ, F)`; embed `Mᵢ` into an injective `Aᵢ`-module `Iᵢ`. The sheaf `Ĩᵢ` is flasque
(Proposition III.3.4, `tilde_isFlasque`), so `G = ⨁ᵢ fᵢ_* Ĩᵢ` is flasque (pushforwards and finite
direct sums of flasque sheaves are flasque) and quasi-coherent (`fᵢ` is quasi-compact and
quasi-separated). The maps `F ⟶ fᵢ_* Ĩᵢ` adjoint to `F|_{Spec Aᵢ} ≅ M̃ᵢ ↪ Ĩᵢ` are jointly
injective on sections, because a section of `F` vanishing on each `fᵢ(Spec Aᵢ)` vanishes.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

variable {X : Scheme.{u}}

/-- The pushforward of an `𝒪_X`-module with flasque underlying sheaf is flasque. -/
theorem isFlasque_pushforward {Y : Scheme.{u}} (f : X ⟶ Y) (G : X.Modules)
    [TopCat.Presheaf.IsFlasque G.presheaf] :
    TopCat.Presheaf.IsFlasque ((Scheme.Modules.pushforward f).obj G).presheaf where
  epi i := TopCat.Presheaf.IsFlasque.epi (F := G.presheaf) ((Opens.map f.base).op.map i)

lemma sum_app_apply {M N : X.Modules} {ι : Type*} (s : Finset ι) (φ : ι → (M ⟶ N))
    (U : X.Opens) (x : Γ(M, U)) : (∑ j ∈ s, φ j).app U x = ∑ j ∈ s, (φ j).app U x :=
  map_sum (AddMonoidHom.mk' (fun ψ : M ⟶ N => ψ.app U x) fun ψ ψ' => by
    rw [Scheme.Modules.Hom.add_app]; rfl) φ s

end Hartshorne
