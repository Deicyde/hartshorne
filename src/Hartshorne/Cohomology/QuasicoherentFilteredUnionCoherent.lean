/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.QuasicoherentCoherentSubobjects
import Hartshorne.Scheme.CoherentExtension

/-!
# Quasi-coherent sheaves are filtered unions of coherent subsheaves

Hartshorne II, Exercise 5.15(e).  Let `X` be a Noetherian scheme and `F` a quasi-coherent
`𝒪_X`-module.  The poset of coherent subsheaves of `F` (subobjects of `F` in `𝒪_X`-modules with
coherent underlying module, `CoherentSubobject F`) is filtered, and the cocone of inclusions
exhibits `F` as its colimit.

## Proof

By `nonempty_isColimit_coherentSubobjectCocone_of_forall_mem` it suffices that every local
section `s ∈ F(U)` is a section of a coherent subsheaf.  The subsheaf of `F` spanned by `s` over
the affine opens inside `U` is coherent on `U`, so the extension statement of Hartshorne II,
Exercise 5.15(d) (`exists_isCoherent_eq_on_of_isNoetherian`) gives a coherent subsheaf `N' ⊆ F`
agreeing with it on `U`; in particular `s ∈ N'(U)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry ArtinReesKernelSheaf

universe u

noncomputable section

variable {X : Scheme.{u}} {F : X.Modules}

/-- The inclusion of a local family of submodules of `F`, as a morphism of `𝒪_X`-modules. -/
def toModulesι (N : F.val.Submodule) (hN : IsLocal N) : toModules N hN ⟶ F :=
  ⟨N.ι⟩

instance (N : F.val.Submodule) (hN : IsLocal N) : Mono (toModulesι N hN) := by
  constructor
  intro Z g h e
  ext U x
  apply Subtype.ext
  exact congr(($e).app U x)

/-- **Hartshorne II, Exercise 5.15(e)** (p. 127), in the sense of the union defined in Exercise
5.15(a): on a Noetherian scheme, every local section of a quasi-coherent module `F` is a section
of some coherent subsheaf of `F`. The proof extends the subsheaf the section spans on its domain,
by Exercise 5.15(d). -/
theorem exists_coherentSubobject_mem_range [IsNoetherian X] [F.IsQuasicoherent]
    (U : X.Opens) (s : Γ(F, U)) :
    ∃ P : CoherentSubobject F, s ∈ Set.range (P.1.arrow.app U) := by
  obtain ⟨N', hN', hcoh, heq⟩ := exists_isCoherent_eq_on_of_isNoetherian
    (isLocal_spanOn U {s}) (extendsOver_spanOn {s}) fun V hVU => by
      rw [sub_spanOn_eq {s} V hVU]
      exact Module.Finite.span_of_finite _ ((Set.finite_singleton s).image _)
  let φ := toModulesι N' hN'
  have hs : s ∈ sub N' U := by
    rw [heq U le_rfl]
    refine isLocal_spanOn U {s} U s fun x hx => ?_
    obtain ⟨W, hWU, hxW⟩ := exists_affine_le hx
    exact ⟨W, hWU, hxW, span_le_sub_spanOn {s} W hWU (Submodule.subset_span ⟨s, rfl, rfl⟩)⟩
  refine ⟨⟨Subobject.mk φ, isCoherent_of_iso (Subobject.underlyingIso φ).symm hcoh⟩,
    (Subobject.underlyingIso φ).inv.app U ⟨s, hs⟩, ?_⟩
  change ((Subobject.underlyingIso φ).inv ≫ (Subobject.mk φ).arrow).app U ⟨s, hs⟩ = s
  rw [Subobject.underlyingIso_arrow]
  rfl

variable (F)

/-- **Hartshorne II, Exercise 5.15(e).** On a Noetherian scheme, the poset of coherent
subsheaves of a quasi-coherent module `F` is filtered, and the cocone of inclusions is a colimit
cocone: `F` is the filtered union of its coherent subsheaves. -/
theorem isFiltered_coherentSubobject_and_nonempty_isColimit [IsNoetherian X]
    [F.IsQuasicoherent] :
    IsFiltered (CoherentSubobject F) ∧ Nonempty (IsColimit (coherentSubobjectCocone F)) :=
  ⟨coherentSubobject_isFiltered F,
    nonempty_isColimit_coherentSubobjectCocone_of_forall_mem exists_coherentSubobject_mem_range⟩

end

end Hartshorne
