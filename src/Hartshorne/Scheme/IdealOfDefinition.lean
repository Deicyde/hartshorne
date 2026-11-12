/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.NoetherianFormalScheme
import Hartshorne.Scheme.SheafSupport
import Hartshorne.Scheme.AffineFormalThickenings
import Hartshorne.Scheme.ModuleSheafTensor

/-!
# Ideals of definition

Hartshorne, *Algebraic Geometry*, II.9, definition of an ideal of definition (p. 196).

Let `(T, R)` be a ringed space, with `R` a sheaf of commutative rings on `T`.

* `Hartshorne.IdealSubsheaf R`: an ideal subsheaf of `R`, stored as a sub-`R`-module of `R`
  regarded as a module over itself (a `PresheafOfModules.Submodule` of the unit module) whose
  sections are local, so that it is itself a sheaf of `R`-modules.
* `Hartshorne.IdealSubsheaf.toModules J` and `Hartshorne.IdealSubsheaf.ι J`: the `R`-module sheaf
  `J` and its inclusion (a monomorphism) into `R`.
* `Hartshorne.IdealSubsheaf.ideal J V`: the ideal `J(V) ⊆ R(V)` of sections over `V`; these are
  stable under restriction (`IdealSubsheaf.ideal_le_comap`) and local
  (`IdealSubsheaf.mem_ideal_of_locally`). Conversely `Hartshorne.IdealSubsheaf.ofIdeals` turns a
  restriction-stable local family of ideals into an ideal subsheaf; ideal subsheaves are ordered
  by inclusion of their ideals (`IdealSubsheaf.le_iff`), and `J ^ k` is the ideal subsheaf of
  sections lying locally in `J(V) ^ k` (`IdealSubsheaf.ideal_pow`, `IdealSubsheaf.pow_one`).
* `Hartshorne.IdealSubsheaf.quotient J`: the quotient sheaf of rings `R / J`, the sheaf associated
  to `V ↦ R(V) ⧸ J(V)`, with the projection `IdealSubsheaf.quotientπ J : R ⟶ R / J`;
  `IdealSubsheaf.quotientAb J` is its underlying sheaf of abelian groups and
  `IdealSubsheaf.quotientSheafedSpace J` the ringed space `(T, R / J)`.
* `Hartshorne.IsIdealOfDefinition X J`: for a Noetherian formal scheme `X`, the ideal subsheaf `J`
  of `𝒪_X` is an ideal of definition: `Supp (𝒪_X / J)` is all of `X`, and the ringed space
  `(X, 𝒪_X / J)` is isomorphic to a Noetherian scheme.

A ringed space isomorphic to a scheme is a locally ringed space, so the second condition says that
`(X, 𝒪_X / J)` is a locally ringed space which is a Noetherian scheme.
`Hartshorne.IsIdealOfDefinition.quotientScheme` is this Noetherian scheme, whose underlying ringed
space is `(X, 𝒪_X / J)` itself (`IsIdealOfDefinition.quotientScheme_toSheafedSpace`).
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

/-- A family of submodules of a sheaf of modules on a topological space which is stable under
restriction and local defines a sheaf. -/
private theorem isSheaf_submodule_of_local' {T : TopCat.{u}}
    {R' : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} {M : SheafOfModules.{u} R'}
    (N : M.val.Submodule)
    (hN : ∀ (U : Opens T) (s : M.val.obj (op U)),
      (∀ x ∈ U, ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧
        M.val.map (homOfLE hVU).op s ∈ N.obj (op V)) → s ∈ N.obj (op U)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology T) N.toPresheafOfModules.presheaf := by
  change TopCat.Presheaf.IsSheaf _
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let M' : TopCat.Sheaf AddCommGrpCat.{u} T := ⟨M.val.presheaf, M.isSheaf⟩
  let sf' : ∀ i, ToType (M'.obj.obj (op (U i))) := fun i ↦ (sf i).1
  have hsf' : TopCat.Presheaf.IsCompatible M'.obj U sf' := fun i j ↦
    congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hsu⟩ := M'.existsUnique_gluing U sf' hsf'
  have hmem : s ∈ N.obj (op (iSup U)) := by
    apply hN
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨U i, le_iSup U i, hi, ?_⟩
    have := hs i
    change M.val.map (Opens.leSupr U i).op s = (sf i).1 at this
    change M.val.map (Opens.leSupr U i).op s ∈ _
    rw [this]
    exact (sf i).2
  refine ⟨⟨s, hmem⟩, fun i ↦ Subtype.ext (hs i), fun t ht ↦ Subtype.ext (hsu t.1 fun i ↦ ?_)⟩
  exact congrArg Subtype.val (ht i)

variable {T : TopCat.{u}} (R : TopCat.Sheaf CommRingCat.{u} T)

/-- **Ideal subsheaves** of a sheaf of rings `R` on `T`: a sub-`R`-module sheaf of `R`, regarded
as a module over itself. It is stored as a family of submodules `J(V) ⊆ R(V)` of the unit
`R`-module, stable under restriction, whose sections are local (a section lying in `J` near every
point lies in `J`), which makes `J` itself a sheaf of `R`-modules (`IdealSubsheaf.toModules`). -/
structure IdealSubsheaf where
  /-- The submodules `J(V) ⊆ R(V)` of the unit `R`-module, stable under restriction. -/
  carrier : (SheafOfModules.unit (ringCatSheafOf R)).val.Submodule
  /-- A section of `R` lying in `J` near every point lies in `J`. -/
  isLocal : ∀ (U : Opens T) (s : (SheafOfModules.unit (ringCatSheafOf R)).val.obj (op U)),
    (∀ x ∈ U, ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧
      (SheafOfModules.unit (ringCatSheafOf R)).val.map (homOfLE hVU).op s ∈ carrier.obj (op V)) →
    s ∈ carrier.obj (op U)

namespace IdealSubsheaf

variable {R} (J : IdealSubsheaf R)

/-- The ideal subsheaf `J` as a sheaf of `R`-modules. -/
def toModules : SheafOfModules.{u} (ringCatSheafOf R) :=
  ⟨J.carrier.toPresheafOfModules, isSheaf_submodule_of_local' J.carrier J.isLocal⟩

/-- The inclusion `J ↪ R` of `R`-module sheaves. -/
def ι : J.toModules ⟶ SheafOfModules.unit (ringCatSheafOf R) :=
  ⟨J.carrier.ι⟩

instance : Mono J.ι :=
  haveI := (SheafOfModules.fullyFaithfulForget (ringCatSheafOf R)).faithful
  (SheafOfModules.forget (ringCatSheafOf R)).mono_of_mono_map
    (inferInstanceAs (Mono J.carrier.ι))

/-- The ideal `J(V) ⊆ R(V)` of sections of `J` over `V`. -/
def ideal (V : Opens T) : Ideal (R.presheaf.obj (op V)) :=
  J.carrier.obj (op V)

lemma mem_ideal_iff (V : Opens T) (s : R.presheaf.obj (op V)) :
    s ∈ J.ideal V ↔ s ∈ J.carrier.obj (op V) :=
  Iff.rfl

/-- The ideals `J(V)` are stable under restriction. -/
lemma ideal_le_comap {V W : Opens T} (h : W ≤ V) :
    J.ideal V ≤ (J.ideal W).comap (R.presheaf.map (homOfLE h).op).hom :=
  fun _ hs => J.carrier.map (homOfLE h).op hs

/-- The ideals `J(V)` are local: a section lying in `J` near every point lies in `J`. -/
lemma mem_ideal_of_locally {U : Opens T} (s : R.presheaf.obj (op U))
    (hs : ∀ x ∈ U, ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧
      R.presheaf.map (homOfLE hVU).op s ∈ J.ideal V) :
    s ∈ J.ideal U :=
  J.isLocal U s hs

/-- Two ideal subsheaves with the same ideals of sections are equal. -/
@[ext]
lemma ext {J J' : IdealSubsheaf R} (h : ∀ V, J.ideal V = J'.ideal V) : J = J' := by
  obtain ⟨c, _⟩ := J
  obtain ⟨c', _⟩ := J'
  congr 1
  exact PresheafOfModules.Submodule.ext fun V => h V.unop

instance : PartialOrder (IdealSubsheaf R) :=
  PartialOrder.lift (fun J => J.carrier) fun J J' h => by
    obtain ⟨c, _⟩ := J
    obtain ⟨c', _⟩ := J'
    cases h
    rfl

lemma le_iff {J J' : IdealSubsheaf R} : J ≤ J' ↔ ∀ V, J.ideal V ≤ J'.ideal V :=
  ⟨fun h V => h (op V), fun h V => h V.unop⟩

variable (R) in
/-- **Representation bridge.** A family of ideals `I(V) ⊆ R(V)`, stable under restriction and
local, as an ideal subsheaf of `R`. -/
def ofIdeals (I : ∀ V : Opens T, Ideal (R.presheaf.obj (op V)))
    (hI : ∀ {V W : Opens T} (h : W ≤ V), I V ≤ (I W).comap (R.presheaf.map (homOfLE h).op).hom)
    (hloc : ∀ {U : Opens T} (s : R.presheaf.obj (op U)),
      (∀ x ∈ U, ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧ R.presheaf.map (homOfLE hVU).op s ∈ I V) →
        s ∈ I U) :
    IdealSubsheaf R where
  carrier :=
    { obj V := I V.unop
      map f := hI (leOfHom f.unop) }
  isLocal _ s hs := hloc s hs

@[simp]
lemma ideal_ofIdeals (I : ∀ V : Opens T, Ideal (R.presheaf.obj (op V)))
    (hI : ∀ {V W : Opens T} (h : W ≤ V), I V ≤ (I W).comap (R.presheaf.map (homOfLE h).op).hom)
    (hloc : ∀ {U : Opens T} (s : R.presheaf.obj (op U)),
      (∀ x ∈ U, ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧ R.presheaf.map (homOfLE hVU).op s ∈ I V) →
        s ∈ I U) (V : Opens T) :
    (ofIdeals R I hI hloc).ideal V = I V :=
  rfl

/-- The `k`-th power `J ^ k` of an ideal subsheaf: the sections lying, near every point, in the
`k`-th power of the ideal of sections of `J`. -/
instance : Pow (IdealSubsheaf R) ℕ where
  pow J k := ofIdeals R (sheafIdealPow R J.ideal J.ideal_le_comap k)
    (sheafIdealPow_le_comap R J.ideal J.ideal_le_comap k)
    (mem_sheafIdealPow_of_locally R J.ideal J.ideal_le_comap k)

lemma ideal_pow (k : ℕ) (V : Opens T) :
    (J ^ k).ideal V = sheafIdealPow R J.ideal J.ideal_le_comap k V :=
  rfl

@[simp]
lemma pow_one : J ^ 1 = J := by
  ext V s
  rw [ideal_pow]
  constructor
  · intro hs
    refine J.mem_ideal_of_locally s fun x hx => ?_
    obtain ⟨W, h, hxW, hsW⟩ := hs x hx
    exact ⟨W, h, hxW, by simpa using hsW⟩
  · intro hs x hx
    refine ⟨V, le_rfl, hx, ?_⟩
    rw [_root_.pow_one, show (homOfLE (le_refl V)).op = 𝟙 (op V) from rfl,
      CategoryTheory.Functor.map_id]
    exact hs

/-- **The quotient sheaf of rings** `R / J`: the sheaf associated to the presheaf
`V ↦ R(V) ⧸ J(V)`. -/
def quotient : TopCat.Sheaf CommRingCat.{u} T :=
  idealQuotientSheaf R J.ideal J.ideal_le_comap

/-- The projection of presheaves `R(V) → R(V) ⧸ J(V)`. -/
def quotientPresheafπ : R.presheaf ⟶ idealQuotientPresheaf R J.ideal J.ideal_le_comap where
  app V := CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal V.unop))
  naturality V W i := by
    ext s
    rfl

/-- The projection `R ⟶ R / J` of sheaves of rings. -/
def quotientπ : R ⟶ J.quotient :=
  (sheafificationIso R).hom ≫
    (presheafToSheaf (Opens.grothendieckTopology T) CommRingCat.{u}).map J.quotientPresheafπ

/-- The sheaf of abelian groups underlying `R / J`. -/
abbrev quotientAb : TopCat.Sheaf AddCommGrpCat.{u} T :=
  (sheafCompose (Opens.grothendieckTopology T) (forget₂ RingCat AddCommGrpCat.{u})).obj
    ((sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat RingCat.{u})).obj
      J.quotient)

/-- The ringed space `(T, R / J)`. -/
def quotientSheafedSpace : SheafedSpace CommRingCat.{u} where
  carrier := T
  presheaf := J.quotient.presheaf
  IsSheaf := J.quotient.property

end IdealSubsheaf

/-- **Ideals of definition** (Hartshorne II.9, p. 196). An ideal subsheaf `J` of the structure
sheaf `𝒪_X` of a Noetherian formal scheme `X` (a sub-`𝒪_X`-module sheaf of `𝒪_X`) is an ideal of
definition when `Supp (𝒪_X / J)` is the whole underlying space of `X`, and the ringed space
`(X, 𝒪_X / J)` is a Noetherian scheme: it is isomorphic, as a ringed space, to a Noetherian
scheme (and is in particular a locally ringed space). -/
structure IsIdealOfDefinition (X : NoetherianFormalScheme.{u})
    (J : IdealSubsheaf X.toLocallyRingedSpace.sheaf) : Prop where
  /-- The support of `𝒪_X / J` is all of `X`. -/
  support_eq_univ : sheafSupport J.quotientAb = Set.univ
  /-- The ringed space `(X, 𝒪_X / J)` is a Noetherian scheme. -/
  isNoetherianScheme : ∃ (Y : Scheme.{u}) (_ : IsNoetherian Y),
    Nonempty (Y.toSheafedSpace ≅ J.quotientSheafedSpace)

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J)

/-- A chosen Noetherian scheme isomorphic to the ringed space `(X, 𝒪_X / J)`. -/
def noetherianScheme : Scheme.{u} :=
  h.isNoetherianScheme.choose

instance : IsNoetherian h.noetherianScheme :=
  h.isNoetherianScheme.choose_spec.choose

/-- The chosen isomorphism of ringed spaces between `noetherianScheme` and `(X, 𝒪_X / J)`. -/
def noetherianSchemeIso : h.noetherianScheme.toSheafedSpace ≅ J.quotientSheafedSpace :=
  h.isNoetherianScheme.choose_spec.choose_spec.some

/-- The inverse of `noetherianSchemeIso`, as a morphism of presheafed spaces. -/
private def quotientIsoInv :
    J.quotientSheafedSpace.toPresheafedSpace ⟶ h.noetherianScheme.toPresheafedSpace :=
  (SheafedSpace.forgetToPresheafedSpace.mapIso h.noetherianSchemeIso).inv

private instance : IsIso (quotientIsoInv h) :=
  ⟨⟨(SheafedSpace.forgetToPresheafedSpace.mapIso h.noetherianSchemeIso).hom,
    (SheafedSpace.forgetToPresheafedSpace.mapIso h.noetherianSchemeIso).inv_hom_id,
    (SheafedSpace.forgetToPresheafedSpace.mapIso h.noetherianSchemeIso).hom_inv_id⟩⟩

private instance : PresheafedSpace.IsOpenImmersion (quotientIsoInv h) :=
  PresheafedSpace.IsOpenImmersion.ofIsIso _

/-- **The scheme `(X, 𝒪_X / J)`** of an ideal of definition: the ringed space `(X, 𝒪_X / J)`
with the scheme structure transported from `noetherianScheme`. -/
def quotientScheme : Scheme.{u} :=
  PresheafedSpace.IsOpenImmersion.toScheme h.noetherianScheme (quotientIsoInv h)

/-- The underlying ringed space of `quotientScheme` is `(X, 𝒪_X / J)`. -/
lemma quotientScheme_toSheafedSpace :
    h.quotientScheme.toSheafedSpace = J.quotientSheafedSpace :=
  rfl

/-- The scheme `(X, 𝒪_X / J)` of an ideal of definition is Noetherian. -/
instance : IsNoetherian h.quotientScheme where
  toIsLocallyNoetherian :=
    isLocallyNoetherian_of_isOpenImmersion
      (X := PresheafedSpace.IsOpenImmersion.toScheme h.noetherianScheme (quotientIsoInv h))
      (PresheafedSpace.IsOpenImmersion.toSchemeHom h.noetherianScheme (quotientIsoInv h))
  toCompactSpace := by
    have : CompactSpace ((SheafedSpace.forget _).obj h.noetherianScheme.toSheafedSpace) :=
      inferInstanceAs (CompactSpace h.noetherianScheme)
    exact (TopCat.homeoOfIso ((SheafedSpace.forget _).mapIso h.noetherianSchemeIso)).compactSpace

end IsIdealOfDefinition

end Hartshorne
