/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Spectrum.Prime.Module
import Hartshorne.Scheme.AffineTildeLocalization
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Hartshorne.Scheme.SheafSupport

/-!
# The support of a sheaf of modules

Hartshorne, *Algebraic Geometry*, Exercise II.5.6(a)–(c) (p. 124), internal support lemmas.

For an `𝒪_X`-module `F`, its support is `Supp(F) = {x ∈ X | F_x ≠ 0}`, the support of the
underlying sheaf of abelian groups.  We show:

* on `X = Spec A`, the support of `M̃` is the set of primes `𝔭` with `M_𝔭 ≠ 0`;
* if `M` is finitely generated, then `Supp(M̃) = V(Ann_A M)`;
* the support of a coherent sheaf on a Noetherian scheme is closed, and in fact the support of
  any coherent sheaf is closed;
* for `m ∈ M`, the support of the corresponding global section of `M̃` is
  `V(Ann_A m)`.

The support is compatible with isomorphisms and with restriction along open immersions, which
reduces the closedness statement to the affine case.  For coherence we use the project
definition (a cover by affine opens on which `F` is associated to a finitely generated module);
with it no Noetherian hypothesis is needed for closedness.
-/

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry PrimeSpectrum

universe u

/-- The **support** of a sheaf of `𝒪_X`-modules: the points at which its stalk is nonzero,
i.e. the support of its underlying sheaf of abelian groups. -/
def moduleSheafSupport {X : Scheme.{u}} (F : X.Modules) : Set X :=
  sheafSupport ⟨F.presheaf, F.isSheaf⟩

theorem mem_moduleSheafSupport_iff {X : Scheme.{u}} (F : X.Modules) (x : X) :
    x ∈ moduleSheafSupport F ↔ Nontrivial (F.presheaf.stalk x) :=
  Iff.rfl

/-- Isomorphic module sheaves have the same support. -/
theorem moduleSheafSupport_congr {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    moduleSheafSupport F = moduleSheafSupport G := by
  ext x
  let i := (TopCat.Presheaf.stalkFunctor Ab x).mapIso ((Scheme.Modules.toPresheaf X).mapIso e)
  let φ : F.presheaf.stalk x ≃ G.presheaf.stalk x := ((forget Ab).mapIso i).toEquiv
  simp only [mem_moduleSheafSupport_iff]
  exact ⟨fun _ ↦ φ.symm.nontrivial, fun _ ↦ φ.nontrivial⟩

/-- The support of the restriction of a module sheaf along an open immersion is the preimage
of its support. -/
theorem moduleSheafSupport_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (F : Y.Modules) : moduleSheafSupport (F.restrict f) = f ⁻¹' moduleSheafSupport F := by
  ext x
  let i := (Scheme.Modules.restrictStalkNatIso f x).app F
  let φ : (F.restrict f).presheaf.stalk x ≃ F.presheaf.stalk (f x) := ((forget Ab).mapIso i).toEquiv
  simp only [Set.mem_preimage, mem_moduleSheafSupport_iff]
  exact ⟨fun _ ↦ φ.symm.nontrivial, fun _ ↦ φ.nontrivial⟩

/-- **Support of `M̃`.** On `Spec A`, the support of `M̃` is the set of primes `𝔭` with
`M_𝔭 ≠ 0`. -/
theorem moduleSheafSupport_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    moduleSheafSupport (tilde M) =
      {p : PrimeSpectrum R | Nontrivial (LocalizedModule p.asIdeal.primeCompl M)} := by
  refine Set.ext fun (p : PrimeSpectrum R) ↦ ?_
  let φ := affineTildeStalkIso M p
  change Nontrivial ((tilde M).presheaf.stalk p) ↔
    Nontrivial (LocalizedModule p.asIdeal.primeCompl M)
  exact ⟨fun h ↦ @Equiv.nontrivial _ _ φ.toEquiv h,
    fun h ↦ @Equiv.nontrivial _ _ φ.toEquiv.symm h⟩

/-- **Support of `M̃` for finitely generated `M`.** If `M` is a finitely generated `A`-module,
then `Supp(M̃) = V(Ann_A M)`. -/
theorem moduleSheafSupport_tilde_eq_zeroLocus {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    moduleSheafSupport (tilde M) = zeroLocus (Module.annihilator R M) := by
  rw [moduleSheafSupport_tilde, ← Module.support_eq_zeroLocus]
  rfl

/-- **The support of a coherent sheaf is closed.** -/
theorem isClosed_moduleSheafSupport_of_isCoherent {X : Scheme.{u}} (F : X.Modules)
    (hF : IsCoherent F) : IsClosed (moduleSheafSupport F) := by
  obtain ⟨ι, U, hU, hM⟩ := hF
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.symm ▸ Opens.mem_top x : x ∈ ⨆ i, (U i : X.Opens))
  obtain ⟨M, hfin, ⟨e⟩⟩ := hM i
  let f := (U i).2.fromSpec
  have : IsOpenImmersion f := (U i).2.isOpenImmersion_fromSpec
  have hclosed : IsClosed (f ⁻¹' moduleSheafSupport F) := by
    rw [← moduleSheafSupport_restrict, ← moduleSheafSupport_congr e]
    change IsClosed (moduleSheafSupport (tilde M))
    rw [moduleSheafSupport_tilde_eq_zeroLocus]
    exact isClosed_zeroLocus _
  obtain ⟨y, rfl⟩ : x ∈ Set.range f := by rwa [(U i).2.range_fromSpec]
  refine ⟨f '' (f ⁻¹' moduleSheafSupport F)ᶜ, ?_, f.isOpenEmbedding.isOpenMap _
    hclosed.isOpen_compl, ⟨y, hx, rfl⟩⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hz

/-- **The support of a coherent sheaf on a Noetherian scheme is closed** (Hartshorne's
formulation).  The Noetherian hypothesis is not needed: coherence is defined by an affine cover
on which the sheaf is associated to finitely generated modules, see
`isClosed_moduleSheafSupport_of_isCoherent`. -/
theorem isClosed_moduleSheafSupport_of_isCoherent_of_isNoetherian {X : Scheme.{u}}
    [IsNoetherian X] (F : X.Modules) (hF : IsCoherent F) :
    IsClosed (moduleSheafSupport F) :=
  isClosed_moduleSheafSupport_of_isCoherent F hF

set_option backward.isDefEq.respectTransparency.types false in
/-- **Support of a global section of `M̃`.** For `m ∈ M`, the support of the corresponding
global section of `M̃` is `V(Ann_A m)`. -/
theorem sectionSupport_tilde_toOpen_top {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (m : M) :
    Subtype.val '' sectionSupport ⟨(tilde M).presheaf, (tilde M).isSheaf⟩ ⊤
        ((tilde.toOpen M ⊤).hom m) =
      zeroLocus (Submodule.span R {m}).annihilator := by
  refine Set.ext fun (p : PrimeSpectrum R) ↦ ?_
  have hgerm : (tilde M).presheaf.germ ⊤ p trivial ((tilde.toOpen M ⊤).hom m) =
      (tilde.toStalk M p).hom m := rfl
  have key : (tilde M).presheaf.germ ⊤ p trivial ((tilde.toOpen M ⊤).hom m) ≠ 0 ↔
      (Submodule.span R {m}).annihilator ≤ p.asIdeal := by
    rw [hgerm, ne_eq, IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl]
    simp only [SetLike.le_def, Submodule.mem_annihilator_span_singleton, not_exists]
    exact ⟨fun h r hr ↦ not_not.mp fun hp ↦ h ⟨r, hp⟩ hr,
      fun h s hs ↦ s.2 (h hs)⟩
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact key.mp hx
  · intro hp
    exact ⟨⟨p, trivial⟩, key.mpr hp, rfl⟩

end Hartshorne
