/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CartierClassPicard
import Hartshorne.Scheme.TotalQuotientIntegral

/-!
# Cartier classes and the Picard group of an integral scheme

Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.15 (p. 145).

If `X` is an integral scheme, every invertible sheaf `L` is isomorphic to an invertible
sub-`O_X`-module of the sheaf `K_X` of total quotient rings, which on an integral scheme is the
constant sheaf `K(X)` (`exists_invertibleTotalQuotientSubmodule_iso`). By Proposition 6.13(a)
every such submodule is `O_X(D)` for a Cartier divisor `D` (`exists_cartierDivisor_sheaf_iso`), so
the injective homomorphism `CaCl X → Pic X` of Corollary 6.14 is also surjective
(`cartierClassToPicard_surjective`), hence an isomorphism (`cartierClassEquivPicard`).

Hartshorne embeds `L` into `L ⊗ K_X`, a constant sheaf of one-dimensional `K(X)`-vector spaces.
Here we fix a trivialization `e` of `L` on an open neighbourhood `V₀` of the generic point and send
a section `s` of `L` over `U` to the rational function `s / e`, namely the germ at the generic point
of the coordinate of `s|_{U ∩ V₀}` with respect to `e`; this is the composite of `L → L ⊗ K_X` with
the identification `L ⊗ K_X ≅ K_X` given by `e`. The resulting morphism `L ⟶ K_X` of
`O_X`-modules is injective on sections because `L` is locally isomorphic to `O_X` and regular
functions on a nonempty open set of an integral scheme are determined by their germs at the generic
point. Its image is then an invertible submodule of `K_X` isomorphic to `L`.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

namespace Modules

/-- The coordinate map `L(V) → O_X(V)` of a trivialization `e : L|_U ≅ O_U` of an `O_X`-module,
over an open set `V ⊆ U`. -/
def frameCoord {L : X.Modules} {U : X.Opens} (e : L.over U ≅ SheafOfModules.unit _)
    {V : X.Opens} (h : V ≤ U) : L.val.obj (op V) →ₗ[Γ(X, V)] Γ(X, V) :=
  (e.hom.val.app (op (Over.mk (homOfLE h)))).hom

/-- The coordinate map of a trivialization commutes with restriction. -/
theorem frameCoord_map {L : X.Modules} {U : X.Opens} (e : L.over U ≅ SheafOfModules.unit _)
    {V W : X.Opens} (h : V ≤ U) (hWV : W ≤ V) (s : L.val.obj (op V)) :
    frameCoord e (hWV.trans h) (L.val.map (homOfLE hWV).op s) =
      X.presheaf.map (homOfLE hWV).op (frameCoord e h s) :=
  ConcreteCategory.congr_hom (e.hom.val.naturality
    (Over.homMk (homOfLE hWV) : Over.mk (homOfLE (hWV.trans h)) ⟶ Over.mk (homOfLE h)).op) s

/-- The coordinate map of a trivialization is injective. -/
theorem frameCoord_injective {L : X.Modules} {U : X.Opens}
    (e : L.over U ≅ SheafOfModules.unit _) {V : X.Opens} (h : V ≤ U) :
    Function.Injective (frameCoord e h) := by
  have : IsIso e.hom.val := (inferInstance : IsIso ((SheafOfModules.forget _).map e.hom))
  have : IsIso (e.hom.val.app (op (Over.mk (homOfLE h)))) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ _).map e.hom.val))
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- An invertible `O_X`-module is isomorphic to `O_X` on a neighbourhood of every point. -/
theorem exists_over_iso_unit {L : X.Modules} (hL : L.IsInvertible) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (L.over U ≅ SheafOfModules.unit _) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := (Modules.isInvertible_iff_ringed _).1 hL x
  exact ⟨U, hxU, ⟨e ≪≫ coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit _)⟩⟩

end Modules

/-- The image of a morphism `L ⟶ K_X` of `O_X`-modules, as a family of submodules of the sections
of `K_X`. -/
def totalQuotientRangeSubmodule {L : X.Modules} (φ : L ⟶ X.totalQuotientModule) :
    X.totalQuotientModule.val.Submodule where
  obj U := LinearMap.range (φ.val.app U).hom
  map f := by
    rintro _ ⟨s, rfl⟩
    exact ⟨L.val.map f s, PresheafOfModules.naturality_apply φ.val f s⟩

/-- A morphism `L ⟶ K_X`, viewed as a morphism onto its image. -/
def toTotalQuotientRangeSubmodule {L : X.Modules} (φ : L ⟶ X.totalQuotientModule) :
    L.val ⟶ (totalQuotientRangeSubmodule φ).toPresheafOfModules where
  app U := ModuleCat.ofHom (φ.val.app U).hom.rangeRestrict
  naturality f := by
    ext s
    exact Subtype.ext (PresheafOfModules.naturality_apply φ.val f s)

/-- A morphism `L ⟶ K_X` that is injective on sections is an isomorphism onto its image. -/
theorem isIso_toTotalQuotientRangeSubmodule {L : X.Modules} (φ : L ⟶ X.totalQuotientModule)
    (hφ : ∀ U, Function.Injective (φ.val.app U)) : IsIso (toTotalQuotientRangeSubmodule φ) := by
  have : Mono (toTotalQuotientRangeSubmodule φ) :=
    PresheafOfModules.mono_of_injective fun U s s' h ↦ hφ U (congrArg Subtype.val h)
  have : Epi (toTotalQuotientRangeSubmodule φ) :=
    PresheafOfModules.epi_of_surjective fun U t ↦ by
      obtain ⟨_, s, rfl⟩ := t
      exact ⟨s, rfl⟩
  exact isIso_of_mono_of_epi _

/-- If an invertible `O_X`-module `L` admits a morphism to `K_X` that is injective on sections,
then `L` is isomorphic to an invertible submodule of `K_X`, namely its image. -/
theorem exists_invertibleTotalQuotientSubmodule_iso_of_injective {L : X.Modules}
    (hL : L.IsInvertible) (φ : L ⟶ X.totalQuotientModule)
    (hφ : ∀ U, Function.Injective (φ.val.app U)) :
    ∃ M : X.InvertibleTotalQuotientSubmodule, Nonempty (M.toModules ≅ L) := by
  have := isIso_toTotalQuotientRangeSubmodule φ hφ
  let ψ : L.val ≅ (totalQuotientRangeSubmodule φ).toPresheafOfModules :=
    asIso (toTotalQuotientRangeSubmodule φ)
  have hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (totalQuotientRangeSubmodule φ).toPresheafOfModules.presheaf :=
    (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso ψ)).1 L.isSheaf
  let N : X.Modules := ⟨(totalQuotientRangeSubmodule φ).toPresheafOfModules, hsheaf⟩
  let χ : L ≅ N := (SheafOfModules.fullyFaithfulForget _).preimageIso ψ
  have hN : N.IsInvertible := by
    rw [Modules.isInvertible_iff_ringed] at hL ⊢
    intro x
    obtain ⟨U, hxU, ⟨e⟩⟩ := hL x
    exact ⟨U, hxU, ⟨(SheafOfModules.overFunctor _ U).mapIso χ.symm ≪≫ e⟩⟩
  exact ⟨⟨totalQuotientRangeSubmodule φ, hsheaf, hN⟩, ⟨χ.symm⟩⟩

/-- On an irreducible scheme, `K_X` has a single section over an open set not containing the
generic point. -/
theorem totalQuotientSheaf_subsingleton_of_genericPoint_notMem [IrreducibleSpace X]
    {U : X.Opens} (h : genericPoint X ∉ U) :
    Subsingleton (X.totalQuotientSheaf.obj.obj (op U)) :=
  CommRingCat.subsingleton_of_isTerminal
    (X.totalQuotientSheaf.isTerminalOfEqEmpty (opens_eq_bot_of_genericPoint_notMem h))

variable [IsIntegral X]

/-- On an integral scheme, two sections of `K_X` agree when they define the same rational
function. -/
theorem totalQuotientSheaf_ext_of_isIntegral {U : X.Opens}
    {t t' : X.totalQuotientSheaf.obj.obj (op U)}
    (h : ∀ hU : genericPoint X ∈ U, totalQuotientSheafEquivFunctionField U hU t =
      totalQuotientSheafEquivFunctionField U hU t') : t = t' := by
  by_cases hU : genericPoint X ∈ U
  · exact (totalQuotientSheafEquivFunctionField U hU).injective (h hU)
  · have := totalQuotientSheaf_subsingleton_of_genericPoint_notMem hU
    exact Subsingleton.elim _ _

namespace Modules

/-- On an integral scheme, a section `s` of an invertible module over `U` vanishes if, near every
point of `U`, some restriction of `s` to an open set containing the generic point vanishes. -/
theorem eq_zero_of_map_eq_zero_of_isInvertible {L : X.Modules} (hL : L.IsInvertible)
    {U : X.Opens} (s : L.val.obj (op U))
    (h : ∀ x ∈ U, ∃ (U' : X.Opens) (hU' : U' ≤ U), genericPoint X ∈ U' ∧
      L.val.map (homOfLE hU').op s = 0) : s = 0 := by
  choose W hxW e using fun x : U ↦ exists_over_iso_unit hL x.1
  choose U' hU' hηU' hs using fun x : U ↦ h x.1 x.2
  let L' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨L.val.presheaf, L.isSheaf⟩
  have cover : U ≤ ⨆ x : U, W x ⊓ U := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _, hx⟩
  refine L'.eq_of_locally_eq' (fun x : U ↦ W x ⊓ U) U (fun x ↦ homOfLE inf_le_right) cover s 0
    fun x ↦ ?_
  change L.val.map (homOfLE inf_le_right).op s = L.val.map (homOfLE inf_le_right).op 0
  rw [map_zero]
  obtain ⟨e⟩ := e x
  apply frameCoord_injective e (inf_le_left : W x ⊓ U ≤ W x)
  rw [map_zero]
  have hle : W x ⊓ U ⊓ U' x ≤ W x ⊓ U := inf_le_left
  have hη : genericPoint X ∈ W x ⊓ U ⊓ U' x :=
    ⟨⟨genericPoint_mem_opens_of_mem (hxW x), genericPoint_mem_opens_of_mem x.2⟩, hηU' x⟩
  have : Nonempty (W x ⊓ U ⊓ U' x : X.Opens) := ⟨⟨_, hη⟩⟩
  apply map_injective_of_isIntegral X (homOfLE hle)
  rw [map_zero, ← frameCoord_map e inf_le_left hle, ← PresheafOfModules.map_comp_apply]
  rw [show (homOfLE (inf_le_right : W x ⊓ U ≤ U)).op ≫ (homOfLE hle).op =
    (homOfLE (hU' x)).op ≫ (homOfLE (inf_le_right : W x ⊓ U ⊓ U' x ≤ U' x)).op from rfl,
    PresheafOfModules.map_comp_apply, hs x, map_zero, map_zero]

open Classical in
/-- Given a trivialization `e` of `L` on an open set `V₀` containing the generic point, the
rational function `s / e` attached to a section `s` of `L` over `U`: the germ at the generic point
of the coordinate of `s|_{U ∩ V₀}`, as a section of `K_X` over `U`. -/
def toTotalQuotientApp {L : X.Modules} {V₀ : X.Opens} (e : L.over V₀ ≅ SheafOfModules.unit _)
    (hη : genericPoint X ∈ V₀) (U : X.Opens) (s : L.val.obj (op U)) :
    X.totalQuotientSheaf.obj.obj (op U) :=
  if h : genericPoint X ∈ U then
    (totalQuotientSheafEquivFunctionField U h).symm
      (X.presheaf.germ (U ⊓ V₀) (genericPoint X)
        (Opens.mem_inf.2 ⟨h, hη⟩ : genericPoint X ∈ U ⊓ V₀)
        (frameCoord e inf_le_right (L.val.map (homOfLE inf_le_left).op s)))
  else 0

variable {L : X.Modules} {V₀ : X.Opens} (e : L.over V₀ ≅ SheafOfModules.unit _)
    (hη : genericPoint X ∈ V₀)

theorem toTotalQuotientApp_spec {U : X.Opens} (h : genericPoint X ∈ U) (s : L.val.obj (op U)) :
    totalQuotientSheafEquivFunctionField U h (toTotalQuotientApp e hη U s) =
      X.presheaf.germ (U ⊓ V₀) (genericPoint X)
        (Opens.mem_inf.2 ⟨h, hη⟩ : genericPoint X ∈ U ⊓ V₀)
        (frameCoord e inf_le_right (L.val.map (homOfLE inf_le_left).op s)) := by
  rw [toTotalQuotientApp, dif_pos h, RingEquiv.apply_symm_apply]

theorem toTotalQuotientApp_add {U : X.Opens} (s s' : L.val.obj (op U)) :
    toTotalQuotientApp e hη U (s + s') =
      toTotalQuotientApp e hη U s + toTotalQuotientApp e hη U s' := by
  refine totalQuotientSheaf_ext_of_isIntegral fun h ↦ ?_
  rw [map_add, toTotalQuotientApp_spec, toTotalQuotientApp_spec, toTotalQuotientApp_spec, map_add,
    map_add, map_add]

theorem toTotalQuotientApp_smul {U : X.Opens} (r : Γ(X, U)) (s : L.val.obj (op U)) :
    toTotalQuotientApp e hη U (r • s) = X.toK U r * toTotalQuotientApp e hη U s := by
  refine totalQuotientSheaf_ext_of_isIntegral fun h ↦ ?_
  rw [map_mul, toTotalQuotientApp_spec, toTotalQuotientApp_spec,
    show X.toK U r = X.toTotalQuotientSheaf.hom.app (op U) r from rfl,
    totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf, PresheafOfModules.map_smul,
    LinearMap.map_smul, smul_eq_mul, map_mul]
  congr 1
  exact X.presheaf.germ_res_apply _ _ _ r

theorem toTotalQuotientApp_map {U V : X.Opens} (hVU : V ≤ U) (s : L.val.obj (op U)) :
    toTotalQuotientApp e hη V (L.val.map (homOfLE hVU).op s) =
      X.totalQuotientSheaf.obj.map (homOfLE hVU).op (toTotalQuotientApp e hη U s) := by
  refine totalQuotientSheaf_ext_of_isIntegral fun h ↦ ?_
  rw [totalQuotientSheafEquivFunctionField_map hVU h, toTotalQuotientApp_spec,
    toTotalQuotientApp_spec]
  have hle : V ⊓ V₀ ≤ U ⊓ V₀ := inf_le_inf_right _ hVU
  rw [← X.presheaf.germ_res_apply (homOfLE hle) _
      (Opens.mem_inf.2 ⟨h, hη⟩ : genericPoint X ∈ V ⊓ V₀),
    ← frameCoord_map e inf_le_right hle, ← PresheafOfModules.map_comp_apply,
    ← PresheafOfModules.map_comp_apply]
  rfl

theorem toTotalQuotientApp_eq_zero (hL : L.IsInvertible) {U : X.Opens} (s : L.val.obj (op U))
    (hs : toTotalQuotientApp e hη U s = 0) : s = 0 := by
  refine eq_zero_of_map_eq_zero_of_isInvertible hL s fun x hx ↦ ?_
  have hU : genericPoint X ∈ U := genericPoint_mem_opens_of_mem hx
  refine ⟨U ⊓ V₀, inf_le_left, ⟨hU, hη⟩, ?_⟩
  apply frameCoord_injective e (inf_le_right : U ⊓ V₀ ≤ V₀)
  apply germ_injective_of_isIntegral (X := X) (U := U ⊓ V₀) (genericPoint X) ⟨hU, hη⟩
  rw [← toTotalQuotientApp_spec e hη hU, hs, map_zero, map_zero, map_zero]

/-- Given a trivialization `e` of `L` on an open set containing the generic point, the morphism
`L ⟶ K_X` of `O_X`-modules sending a section `s` to the rational function `s / e`. -/
def toTotalQuotientModule (e : L.over V₀ ≅ SheafOfModules.unit _)
    (hη : genericPoint X ∈ V₀) : L ⟶ X.totalQuotientModule :=
  ⟨{ app := fun U ↦
        let f : L.val.obj U →ₗ[X.ringCatSheaf.obj.obj U] X.totalQuotientModule.val.obj U :=
          { toFun := toTotalQuotientApp e hη U.unop
            map_add' := toTotalQuotientApp_add e hη
            map_smul' := fun r s ↦ toTotalQuotientApp_smul e hη r s }
        ConcreteCategory.ofHom (C := ModuleCat (X.ringCatSheaf.obj.obj U)) (X := L.val.obj U)
          (Y := X.totalQuotientModule.val.obj U) f
     naturality := fun {U V} f ↦ by
        ext s
        exact toTotalQuotientApp_map e hη (leOfHom f.unop) s }⟩

/-- On an integral scheme, the morphism `L ⟶ K_X`, `s ↦ s / e`, from an invertible module is
injective on sections. -/
theorem toTotalQuotientModule_injective (hL : L.IsInvertible) (U : X.Opensᵒᵖ) :
    Function.Injective ((toTotalQuotientModule e hη).val.app U) :=
  (injective_iff_map_eq_zero ((toTotalQuotientModule e hη).val.app U).hom).2
    fun s hs ↦ toTotalQuotientApp_eq_zero e hη hL s hs

end Modules

/-- **Hartshorne II.6, proof of Proposition 6.15.** On an integral scheme `X`, every invertible
sheaf is isomorphic to an invertible sub-`O_X`-module of the sheaf `K_X` of total quotient rings (the
constant sheaf `K(X)`). -/
theorem exists_invertibleTotalQuotientSubmodule_iso {L : X.Modules} (hL : L.IsInvertible) :
    ∃ M : X.InvertibleTotalQuotientSubmodule, Nonempty (M.toModules ≅ L) := by
  obtain ⟨V₀, hη, ⟨e⟩⟩ := Modules.exists_over_iso_unit hL (genericPoint X)
  exact exists_invertibleTotalQuotientSubmodule_iso_of_injective hL _
    (Modules.toTotalQuotientModule_injective e hη hL)

/-- **Hartshorne II.6, proof of Proposition 6.15.** On an integral scheme `X`, every invertible
sheaf is isomorphic to `O_X(D)` for some Cartier divisor `D`. -/
theorem exists_cartierDivisor_sheaf_iso {L : X.Modules} (hL : L.IsInvertible) :
    ∃ D : X.CartierDivisor, Nonempty (D.sheaf ≅ L) := by
  obtain ⟨M, ⟨χ⟩⟩ := exists_invertibleTotalQuotientSubmodule_iso hL
  obtain ⟨D, rfl⟩ := CartierDivisor.toInvertibleSubmodule_surjective M
  exact ⟨D, ⟨χ⟩⟩

open Hartshorne Hartshorne.Ringed in
/-- **Hartshorne II.6, Proposition 6.15.** On an integral scheme, the homomorphism
`CaCl X → Pic X`, `[D] ↦ [O_X(D)]`, is surjective. -/
theorem cartierClassToPicard_surjective : Function.Surjective X.cartierClassToPicard := by
  intro c
  obtain ⟨L, hL, hc⟩ := Pic.mk_surjective (Additive.toMul c)
  obtain ⟨D, ⟨χ⟩⟩ := exists_cartierDivisor_sheaf_iso ((Modules.isInvertible_iff_ringed L).2 hL)
  refine ⟨X.cartierDivisorClassHom D, ?_⟩
  rw [cartierClassToPicard_apply, ← ofMul_toMul c, ← hc]
  exact congrArg Additive.ofMul ((Pic.mk_eq_mk_iff _ _).2 ⟨χ⟩)

variable (X) in
/-- **Hartshorne II.6, Proposition 6.15.** On an integral scheme, the homomorphism
`CaCl X → Pic X`, `[D] ↦ [O_X(D)]`, is bijective. -/
theorem cartierClassToPicard_bijective : Function.Bijective X.cartierClassToPicard :=
  ⟨X.cartierClassToPicard_injective, cartierClassToPicard_surjective⟩

open Hartshorne.Ringed in
variable (X) in
/-- **Hartshorne II.6, Proposition 6.15.** On an integral scheme, `[D] ↦ [O_X(D)]` is an
isomorphism `CaCl X ≃ Pic X` (written additively). -/
def cartierClassEquivPicard : X.CartierClassGroup ≃+ Additive (Pic X.sheaf) :=
  AddEquiv.ofBijective X.cartierClassToPicard (cartierClassToPicard_bijective X)

/-- The isomorphism `CaCl X ≃ Pic X` is the homomorphism `[D] ↦ [O_X(D)]`. -/
theorem cartierClassEquivPicard_apply (c : X.CartierClassGroup) :
    X.cartierClassEquivPicard c = X.cartierClassToPicard c :=
  rfl

end

end AlgebraicGeometry.Scheme
