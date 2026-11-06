/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally free and invertible module sheaves

Hartshorne, *Algebraic Geometry*, II.5 (p. 109).

An `𝒪_X`-module `F` on a scheme `X` is *free* if it is isomorphic to a direct sum of copies of
`𝒪_X` (Mathlib's `SheafOfModules.free I`, the coproduct of copies of the unit indexed by a type
`I`). It is *locally free* if `X` is covered by open sets `U` such that the restriction `F|_U` is
a free `𝒪_U`-module, *locally free of rank `r`* if each such restriction can be taken to be a
direct sum of `r` copies of `𝒪_U`, and *invertible* if it is locally free of rank one.

The rank of `F` at a point `x` is the number of copies (a cardinal, possibly infinite) needed on
any open neighbourhood of `x` on which `F` is free. It is well defined: on an affine open
`Spec A` contained in two such neighbourhoods, two free presentations give isomorphic free
`A`-modules `A ^ (⊕ I) ≅ A ^ (⊕ J)`, and `A` is a nonzero commutative ring, so `#I = #J`. Hence
the rank of a locally free module is locally constant, and constant when `X` is connected.

Local freeness is phrased, as in Hartshorne, through restrictions `F|_U` to open subschemes.
Mathlib's `SheafOfModules.IsLocallyFree` expresses the same idea through local generators on the
over-site; it carries no rank, and its comparison with the present definition is not needed here.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

namespace Scheme.Modules

/-- An `𝒪_X`-module is *free* if it is isomorphic to a direct sum of copies of `𝒪_X`. -/
def IsFree (F : X.Modules) : Prop :=
  ∃ I : Type u, Nonempty (F ≅ SheafOfModules.free I)

/-- An `𝒪_X`-module is *locally free* if `X` is covered by open sets `U` for which the
restriction `F|_U` is a free `𝒪_U`-module. -/
def IsLocallyFree (F : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (F.restrict U.ι).IsFree

/-- An `𝒪_X`-module is *locally free of rank `r`* if `X` is covered by open sets `U` for which
`F|_U` is isomorphic to a direct sum of `r` copies of `𝒪_U`. -/
def IsLocallyFreeOfRank (F : X.Modules) (r : ℕ) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (F.restrict U.ι ≅ SheafOfModules.free (ULift.{u} (Fin r)))

/-- An `𝒪_X`-module is *invertible* if it is locally free of rank one. -/
def IsInvertible (F : X.Modules) : Prop :=
  F.IsLocallyFreeOfRank 1

/-- Restricting a free module along an open immersion gives the free module on the same
index type. -/
def restrictFreeIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (I : Type u) :
    (restrictFunctor f).obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  let G : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} Y.ringCatSheaf :=
    restrictFunctor f
  have : PreservesColimitsOfShape (Discrete I) G :=
    (restrictAdjunction f).leftAdjoint_preservesColimits.{u, u}.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso G I (restrictUnitIso f).symm).symm

/-- Over a nonzero commutative ring `A`, if the free modules `𝒪 ^ (⊕ I)` and `𝒪 ^ (⊕ J)` on
`Spec A` are isomorphic, then `I` and `J` have the same cardinality. -/
theorem cardinal_mk_eq_of_free_iso_spec (A : CommRingCat.{u}) [Nontrivial A] {I J : Type u}
    (e : (SheafOfModules.free I : (Spec A).Modules) ≅ SheafOfModules.free J) :
    Cardinal.mk I = Cardinal.mk J := by
  let e' : (tilde.functor A).obj (ModuleCat.of A (I →₀ A)) ≅
      (tilde.functor A).obj (ModuleCat.of A (J →₀ A)) :=
    tildeFinsupp I ≪≫ e ≪≫ (tildeFinsupp J).symm
  have h := ((tilde.fullyFaithfulFunctor (R := A)).preimageIso e').toLinearEquiv.rank_eq
  simpa using h

/-- Two free presentations of `F` on open neighbourhoods of a common point have index types of
the same cardinality. -/
theorem cardinal_mk_eq_of_restrict_iso {F : X.Modules} {U V : X.Opens} {I J : Type u}
    (α : F.restrict U.ι ≅ SheafOfModules.free I) (β : F.restrict V.ι ≅ SheafOfModules.free J)
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) :
    Cardinal.mk I = Cardinal.mk J := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((U ⊓ V : X.Opens) : Set X) from ⟨hxU, hxV⟩) (U ⊓ V).2
  have hWU : W ≤ U := fun y hy => (hWUV hy).1
  have hWV : W ≤ V := fun y hy => (hWUV hy).2
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nontrivial Γ(X, W) := Scheme.component_nontrivial X W
  let gU : Spec Γ(X, W) ⟶ U := hW.isoSpec.inv ≫ X.homOfLE hWU
  let gV : Spec Γ(X, W) ⟶ V := hW.isoSpec.inv ≫ X.homOfLE hWV
  have hg : gU ≫ U.ι = gV ≫ V.ι := by
    simp [gU, gV]
  let eU : F.restrict (gU ≫ U.ι) ≅ SheafOfModules.free I :=
    (restrictFunctorComp gU U.ι).app F ≪≫ (restrictFunctor gU).mapIso α ≪≫
      restrictFreeIso gU I
  let eV : F.restrict (gV ≫ V.ι) ≅ SheafOfModules.free J :=
    (restrictFunctorComp gV V.ι).app F ≪≫ (restrictFunctor gV).mapIso β ≪≫
      restrictFreeIso gV J
  exact cardinal_mk_eq_of_free_iso_spec Γ(X, W)
    (eU.symm ≪≫ (restrictFunctorCongr hg).app F ≪≫ eV)

open Classical in
/-- The rank of an `𝒪_X`-module at a point `x`: the cardinal number of copies of `𝒪_U` in a
free presentation `F|_U ≅ 𝒪_U ^ (⊕ I)` on some open neighbourhood `U` of `x` (and `0` if there
is none). By `rankAt_eq` it does not depend on the choice of presentation. -/
def rankAt (F : X.Modules) (x : X) : Cardinal.{u} :=
  if h : ∃ (U : X.Opens) (I : Type u), x ∈ U ∧ Nonempty (F.restrict U.ι ≅ SheafOfModules.free I)
  then Cardinal.mk h.choose_spec.choose else 0

/-- The rank is well defined: on any open `U` with `F|_U ≅ 𝒪_U ^ (⊕ I)`, the rank at every
point of `U` is `#I`. -/
theorem rankAt_eq (F : X.Modules) {U : X.Opens} {I : Type u}
    (α : F.restrict U.ι ≅ SheafOfModules.free I) {x : X} (hx : x ∈ U) :
    F.rankAt x = Cardinal.mk I := by
  have h : ∃ (U : X.Opens) (I : Type u), x ∈ U ∧
      Nonempty (F.restrict U.ι ≅ SheafOfModules.free I) := ⟨U, I, hx, ⟨α⟩⟩
  rw [rankAt, dif_pos h]
  obtain ⟨hx', ⟨α'⟩⟩ := h.choose_spec.choose_spec
  exact cardinal_mk_eq_of_restrict_iso α' α hx' hx

/-- **The rank of a locally free module is locally constant** (Hartshorne II.5, p. 109). -/
theorem isLocallyConstant_rankAt (F : X.Modules) (hF : F.IsLocallyFree) :
    IsLocallyConstant F.rankAt := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, hxU, I, ⟨α⟩⟩ := hF x
  exact ⟨U, U.2, hxU, fun y hy => (F.rankAt_eq α hy).trans (F.rankAt_eq α hxU).symm⟩

/-- **The rank of a locally free module on a connected scheme is constant.** -/
theorem rankAt_eq_of_connectedSpace [ConnectedSpace X] (F : X.Modules) (hF : F.IsLocallyFree)
    (x y : X) : F.rankAt x = F.rankAt y :=
  (F.isLocallyConstant_rankAt hF).apply_eq_of_preconnectedSpace x y

/-- A module is locally free of rank `r` exactly when it is locally free with rank `r` at every
point. -/
theorem isLocallyFreeOfRank_iff (F : X.Modules) (r : ℕ) :
    F.IsLocallyFreeOfRank r ↔ F.IsLocallyFree ∧ ∀ x : X, F.rankAt x = r := by
  constructor
  · intro hF
    refine ⟨fun x => ?_, fun x => ?_⟩
    · obtain ⟨U, hxU, ⟨α⟩⟩ := hF x
      exact ⟨U, hxU, _, ⟨α⟩⟩
    · obtain ⟨U, hxU, ⟨α⟩⟩ := hF x
      rw [F.rankAt_eq α hxU]
      simp
  · rintro ⟨hF, hr⟩ x
    obtain ⟨U, hxU, I, ⟨α⟩⟩ := hF x
    have hI : Cardinal.mk I = Cardinal.mk (ULift.{u} (Fin r)) := by
      rw [← F.rankAt_eq α hxU, hr x]
      simp
    obtain ⟨e⟩ := Cardinal.eq.mp hI
    exact ⟨U, hxU, ⟨α ≪≫ SheafOfModules.freeFunctor.mapIso e.toIso⟩⟩

/-- An invertible module is locally free with rank one at every point. -/
theorem isInvertible_iff (F : X.Modules) :
    F.IsInvertible ↔ F.IsLocallyFree ∧ ∀ x : X, F.rankAt x = 1 :=
  F.isLocallyFreeOfRank_iff 1

end Scheme.Modules

end

end AlgebraicGeometry
