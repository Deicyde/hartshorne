/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.AffineTildeChangeOfRings

/-!
# Pushforward of quasi-coherent sheaves along quasi-compact quasi-separated morphisms

Hartshorne, *Algebraic Geometry*, II, Proposition 5.8(c) (p. 115).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Hartshorne

namespace QcqsPushforward

noncomputable section

variable {X Y : Scheme.{u}}

/-- Quasi-coherence is invariant under isomorphism. -/
lemma isQuasicoherent_of_iso {M N : X.Modules} (e : M ≅ N) (hM : M.IsQuasicoherent) :
    N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hM

/-- A restriction map of a module sheaf between equal opens is an isomorphism. -/
lemma isIso_presheaf_map_homOfLE (M : X.Modules) {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    IsIso (M.presheaf.map (homOfLE h).op) := by
  have : IsIso (homOfLE h) := ⟨⟨homOfLE h', Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  infer_instance

/-- Pushforward along an isomorphism preserves quasi-coherence. -/
lemma isQuasicoherent_pushforward_of_isIso (e : X ⟶ Y) [IsIso e] (G : X.Modules)
    [G.IsQuasicoherent] : ((Scheme.Modules.pushforward e).obj G).IsQuasicoherent := by
  let u := (Scheme.Modules.restrictAdjunction e).unit.app (G.restrict (inv e))
  have hu : IsIso u := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro T
    simp only [u, Scheme.Modules.restrictAdjunction_unit_app_app]
    refine isIso_presheaf_map_homOfLE _ _ ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso]
    simp
  let e₂ : (G.restrict (inv e)).restrict e ≅ G :=
    ((Scheme.Modules.restrictFunctorComp e (inv e)).app G).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (IsIso.hom_inv_id e)).app G ≪≫
        Scheme.Modules.restrictFunctorId.app G
  exact isQuasicoherent_of_iso (asIso u ≪≫ (Scheme.Modules.pushforward e).mapIso e₂)
    (inferInstanceAs ((G.restrict (inv e)).IsQuasicoherent))

/-- Pushforward along `Spec.map φ` preserves quasi-coherence (Hartshorne II.5.2(d)). -/
lemma isQuasicoherent_pushforward_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (G : (Spec S).Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj G).IsQuasicoherent := by
  have : IsIso G.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ G).mp ‹_›
  exact isQuasicoherent_of_iso (((tildePushforwardIso φ).app _).symm ≪≫
    (Scheme.Modules.pushforward (Spec.map φ)).mapIso (@asIso _ _ _ _ G.fromTildeΓ this))
    (inferInstanceAs ((tilde.functor R).obj _).IsQuasicoherent)

/-- Pushforward along a morphism of affine schemes preserves quasi-coherence. -/
lemma isQuasicoherent_pushforward_of_isAffine [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (G : X.Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj G).IsQuasicoherent := by
  have hf : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have h₁ : ((Scheme.Modules.pushforward X.isoSpec.hom).obj G).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isIso _ G
  have h₂ : ((Scheme.Modules.pushforward (Spec.map f.appTop)).obj
      ((Scheme.Modules.pushforward X.isoSpec.hom).obj G)).IsQuasicoherent :=
    isQuasicoherent_pushforward_specMap _ _
  have h₃ := isQuasicoherent_pushforward_of_isIso Y.isoSpec.inv
    ((Scheme.Modules.pushforward (Spec.map f.appTop)).obj
      ((Scheme.Modules.pushforward X.isoSpec.hom).obj G))
  rw [hf]
  exact isQuasicoherent_of_iso
    ((Scheme.Modules.pushforwardComp (Spec.map f.appTop) Y.isoSpec.inv).app
        ((Scheme.Modules.pushforward X.isoSpec.hom).obj G) ≪≫
      (Scheme.Modules.pushforwardComp X.isoSpec.hom (Spec.map f.appTop ≫ Y.isoSpec.inv)).app G)
    h₃

end

end QcqsPushforward

end Hartshorne
