/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.CanonicalSheaf

/-!
# The geometric genus

Hartshorne, *Algebraic Geometry*, II.8, definition of the geometric genus (pp. 180–181).

For a scheme `X` over a field `k`, the global sections `Γ(X, M)` of an `𝒪_X`-module are a
`k`-vector space through the structure morphism `X ⟶ Spec k`
(`Hartshorne.GlobalSectionsOver`). The geometric genus of `X` is
`p_g(X) = dim_k Γ(X, ω_X)` (`Hartshorne.geometricGenus`), where `ω_X` is the canonical sheaf.
Hartshorne defines it for a nonsingular projective variety, where `Γ(X, ω_X)` is
finite-dimensional; the definition makes sense for any `X` over `k`.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Hartshorne

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The ring map `k ⟶ Γ(X, 𝒪_X)` induced by the structure morphism `f : X ⟶ Spec k`. -/
noncomputable def structureRingHom (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- The global sections `Γ(X, M)` of an `𝒪_X`-module `M` on a scheme `X` over `k`, regarded as a
`k`-vector space through the structure morphism `f : X ⟶ Spec k` (restriction of scalars along
`k ⟶ Γ(X, 𝒪_X)`). -/
noncomputable def GlobalSectionsOver (f : X ⟶ Spec (.of k)) (M : X.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (structureRingHom f)).obj (M.val.obj (op ⊤))

/-- Scalar multiplication on `Γ(X, M)` by `a ∈ k` is multiplication by the image of `a` in
`Γ(X, 𝒪_X)`. -/
theorem GlobalSectionsOver.smul_def (f : X ⟶ Spec (.of k)) (M : X.Modules) (a : k)
    (s : GlobalSectionsOver f M) :
    a • s = (show Γ(M, ⊤) from (structureRingHom f a • (show Γ(M, ⊤) from s))) :=
  rfl

/-- **Hartshorne II.8 (pp. 180–181).** The geometric genus `p_g(X) = dim_k Γ(X, ω_X)` of a scheme
`X` over a field `k`, where `ω_X` is the canonical sheaf (`Hartshorne.canonicalSheaf`) and
`Γ(X, ω_X)` is a `k`-vector space through the structure morphism `f : X ⟶ Spec k`. Hartshorne
defines it for a nonsingular projective variety, where `Γ(X, ω_X)` is finite-dimensional. -/
noncomputable def geometricGenus (f : X ⟶ Spec (.of k)) : ℕ :=
  Module.finrank k (GlobalSectionsOver f (canonicalSheaf f))

end Hartshorne
