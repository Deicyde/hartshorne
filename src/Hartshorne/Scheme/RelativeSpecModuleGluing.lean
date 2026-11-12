/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeSpec
import Hartshorne.Scheme.ModuleGluingDirected
import Hartshorne.Scheme.LocallyFreeInvertible

/-!
# Gluing tilde modules over a relative spectrum

Let `A` be a quasi-coherent `𝒪_Y`-algebra, with relative spectrum `p : Spec_Y A ⟶ Y`, covered by
the pieces `Spec A(U)` over the affine opens `U` of `Y`. Suppose given an `A(U)`-module `N(U)` for
every affine open `U`, and for every basic open inclusion `D(r) ⊆ U` a semilinear map
`ρ : N(U) ⟶ N(D(r))` which is a localization at the powers of the image of `r` in `A(U)`,
compatibly with composition. Then the sheaves `N(U)~` on the pieces glue to an `𝒪`-module on
`Spec_Y A` whose restriction to each piece is `N(U)~`. This is the construction of the
quasi-coherent module on `Spec_Y A` attached to a quasi-coherent `A`-module (the essential
surjectivity part of Hartshorne II, Exercise 5.17(e), in the form needed here).

## Main definitions and results

* `Hartshorne.TildeRestrict.iso`: for a localization `φ : R ⟶ S = R[1/s]` and a localization map
  `ρ : N ⟶ N'` of an `R`-module `N` to an `S`-module `N'`, the isomorphism
  `(Ñ)|_{Spec S} ≅ Ñ'`, with `iso_hom_app_top_toOpen` computing it on global sections.
* `Hartshorne.TildeRestrict.hom_ext`: morphisms out of a quasi-coherent module on an affine
  scheme are determined by their effect on global sections.
* `Hartshorne.RelSpecModuleData`: the data `(N, ρ)` above.
* `Hartshorne.RelSpecModuleData.glue`, `RelSpecModuleData.ψ`: the glued module and its
  restrictions to the pieces.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

noncomputable section

namespace Hartshorne

namespace TildeRestrict

/-- An additive map between modules over a localization `S = R[1/s]` which commutes with the
scalars coming from `R` commutes with all scalars of `S`. -/
theorem map_smul_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (s : R) [IsLocalization.Away s S] {M N : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (g : M →+ N)
    (hg : ∀ (a : R) (x : M), g (algebraMap R S a • x) = algebraMap R S a • g x)
    (c : S) (x : M) : g (c • x) = c • g x := by
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) c
  have hu : IsUnit (algebraMap R S (s ^ k)) :=
    IsLocalization.map_units S (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)
  have hspec := IsLocalization.mk'_spec S a (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)
  apply hu.smul_left_cancel.mp
  rw [← hg, smul_smul, smul_smul, mul_comm, hspec, hg]

/-- Morphisms out of a module `P` on `Spec R` with `Γ(P)~ ≅ P` (a quasi-coherent module) are
determined by their effect on global sections. -/
theorem hom_ext {R : CommRingCat.{u}} {P Q : (Spec R).Modules} [IsIso P.fromTildeΓ]
    {g h : P ⟶ Q} (H : ∀ x : Γ(P, ⊤), g.app ⊤ x = h.app ⊤ x) : g = h := by
  rw [← cancel_epi P.fromTildeΓ]
  apply (tilde.adjunction.homEquiv _ Q).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [← Scheme.Modules.tilde_app_top_toOpen, ← Scheme.Modules.tilde_app_top_toOpen]
  exact H _

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)] (s : R)
  (hs : Spec.map φ ''ᵁ ⊤ = PrimeSpectrum.basicOpen s)
  (hloc : letI := φ.hom.toAlgebra; IsLocalization.Away s S)
  {N : ModuleCat.{u} R} {N' : ModuleCat.{u} S} (ρ : N ⟶ (ModuleCat.restrictScalars φ.hom).obj N')
  [hρ : IsLocalizedModule (Submonoid.powers s) ρ.hom]

include hs in
theorem isLocalizedModule_toOpen :
    IsLocalizedModule (Submonoid.powers s) (tilde.toOpen N (Spec.map φ ''ᵁ ⊤)).hom := by
  rw [hs]
  infer_instance

/-- The `R`-linear identification of the sections of `Ñ` over the image `D(s)` of `Spec S` with
`N'`, extending `ρ`. -/
def sectionsEquivR : (modulesSpecToSheaf.obj (tilde N)).presheaf.obj (op (Spec.map φ ''ᵁ ⊤)) ≃ₗ[R]
    (ModuleCat.restrictScalars φ.hom).obj N' :=
  letI := isLocalizedModule_toOpen φ s hs (N := N)
  IsLocalizedModule.linearEquiv (Submonoid.powers s) (tilde.toOpen N (Spec.map φ ''ᵁ ⊤)).hom ρ.hom

theorem sectionsEquivR_toOpen (n : N) :
    sectionsEquivR φ s hs ρ ((tilde.toOpen N (Spec.map φ ''ᵁ ⊤)).hom n) = ρ.hom n := by
  have := isLocalizedModule_toOpen φ s hs (N := N)
  exact IsLocalizedModule.linearEquiv_apply _ _ _ n

/-- The `S`-linear identification of the global sections of `(Ñ)|_{Spec S}` with `N'`. -/
def sectionsEquiv :
    (modulesSpecToSheaf.obj ((tilde N).restrict (Spec.map φ))).presheaf.obj (op ⊤) ≃ₗ[S] N' where
  toFun x := sectionsEquivR φ s hs ρ x
  invFun y := (sectionsEquivR φ s hs ρ).symm y
  left_inv x := (sectionsEquivR φ s hs ρ).symm_apply_apply x
  right_inv y := (sectionsEquivR φ s hs ρ).apply_symm_apply y
  map_add' x y := map_add (sectionsEquivR φ s hs ρ) x y
  map_smul' c x := by
    let := φ.hom.toAlgebra
    refine map_smul_of_isLocalization (M := (modulesSpecToSheaf.obj
      ((tilde N).restrict (Spec.map φ))).presheaf.obj (op ⊤)) (N := N') s
      (sectionsEquivR φ s hs ρ).toAddMonoidHom (fun a y => ?_) c x
    have h1 := Scheme.Modules.restrictAppIso_smul_Spec (M := tilde N) φ (U := ⊤) a y
    change sectionsEquivR φ s hs ρ (φ a • y) = φ a • sectionsEquivR φ s hs ρ y
    exact (congrArg (sectionsEquivR φ s hs ρ) h1).trans
      ((sectionsEquivR φ s hs ρ).map_smul a _)

/-- **Restriction of `Ñ` to a basic open**: for a localization `φ : R ⟶ S = R[1/s]` with
`Spec S ⟶ Spec R` the open immersion onto `D(s)`, and a localization map `ρ : N ⟶ N'` at the
powers of `s`, `(Ñ)|_{Spec S} ≅ Ñ'`. -/
def iso : (tilde N).restrict (Spec.map φ) ≅ tilde N' :=
  haveI : IsIso ((tilde N).restrict (Spec.map φ)).fromTildeΓ := inferInstance
  (asIso ((tilde N).restrict (Spec.map φ)).fromTildeΓ).symm ≪≫
    (tilde.functor S).mapIso (sectionsEquiv φ s hs hloc ρ).toModuleIso

theorem iso_hom : (iso φ s hs hloc ρ).hom = inv ((tilde N).restrict (Spec.map φ)).fromTildeΓ ≫
    tilde.map (sectionsEquiv φ s hs hloc ρ).toModuleIso.hom := rfl

theorem iso_hom_app_top (x : Γ((tilde N).restrict (Spec.map φ), ⊤)) :
    (iso φ s hs hloc ρ).hom.app ⊤ x = (tilde.toOpen N' ⊤).hom (sectionsEquivR φ s hs ρ x) := by
  let P := (tilde N).restrict (Spec.map φ)
  have hfrom : ∀ y, P.fromTildeΓ.app ⊤ ((tilde.toOpen _ ⊤).hom y) = y := by
    intro y
    have := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app P ⊤) y
    exact this.trans (by simp)
  have hinv : (inv P.fromTildeΓ).app ⊤ x =
      (tilde.toOpen ((modulesSpecToSheaf.obj P).presheaf.obj (op ⊤)) ⊤).hom x := by
    calc (inv P.fromTildeΓ).app ⊤ x = (inv P.fromTildeΓ).app ⊤ (P.fromTildeΓ.app ⊤
          ((tilde.toOpen ((modulesSpecToSheaf.obj P).presheaf.obj (op ⊤)) ⊤).hom x)) := by
            rw [hfrom x]
      _ = _ := by
            have h := ConcreteCategory.congr_hom (congrArg (fun k => Scheme.Modules.Hom.app k ⊤)
              (IsIso.hom_inv_id P.fromTildeΓ))
              ((tilde.toOpen ((modulesSpecToSheaf.obj P).presheaf.obj (op ⊤)) ⊤).hom x)
            simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h
            exact h
  have hmap := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (sectionsEquiv φ s hs hloc ρ).toModuleIso.hom ⊤) x
  rw [iso_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hinv]
  exact hmap

theorem iso_hom_app_top_toOpen (n : N) :
    (iso φ s hs hloc ρ).hom.app ⊤ ((tilde.toOpen N (Spec.map φ ''ᵁ ⊤)).hom n) =
      (tilde.toOpen N' ⊤).hom (ρ.hom n) := by
  exact (iso_hom_app_top φ s hs hloc ρ _).trans
    (congrArg (tilde.toOpen N' ⊤).hom (sectionsEquivR_toOpen φ s hs ρ n))

end TildeRestrict

variable {Y : Scheme.{u}} (A : QuasiCoherentAlgebra Y)

instance : Quiver.IsThin A.gluingData.cover.I₀ :=
  inferInstanceAs (Quiver.IsThin Y.AffineZariskiSite)

/-- **A quasi-coherent module over a quasi-coherent algebra `A`**, recorded through its modules of
sections over the affine opens: an `A(U)`-module `N(U)` for every affine open `U ⊆ Y` and, for
every basic open inclusion `U = D(r) ⊆ V`, a semilinear map `N(V) ⟶ N(U)` which is a localization
at the powers of the image of `r` in `A(V)`, compatibly with composition. -/
structure RelSpecModuleData where
  /-- The module of sections over an affine open. -/
  N : ∀ U : Y.AffineZariskiSite, ModuleCat.{u} (A.sections.obj (op U))
  /-- The restriction maps. -/
  ρ : ∀ {U V : Y.AffineZariskiSite} (i : U ⟶ V),
    N V ⟶ (ModuleCat.restrictScalars (A.sections.map i.op).hom).obj (N U)
  ρ_comp : ∀ {U V W : Y.AffineZariskiSite} (i : U ⟶ V) (j : V ⟶ W) (n : N W),
    (ρ (i ≫ j)).hom n = (ρ i).hom ((ρ j).hom n)
  isLocalizedModule : ∀ {U V : Y.AffineZariskiSite} (i : U ⟶ V) (r : Γ(Y, V.1)),
    Y.basicOpen r = U.1 →
      IsLocalizedModule (Submonoid.powers (A.structureMap.app (op V) r)) (ρ i).hom

namespace RelSpecModuleData

variable {A}

instance isOpenImmersion_specMap {U V : Y.AffineZariskiSite} (i : U ⟶ V) :
    IsOpenImmersion (Spec.map (A.sections.map i.op)) :=
  inferInstanceAs (IsOpenImmersion (A.gluingData.functor.map i))

/-- A section `r` of `Y` over `V` with `U = D(r)`, for a basic open inclusion `U ⟶ V`. -/
def transElt {U V : Y.AffineZariskiSite} (i : U ⟶ V) : Γ(Y, V.1) := (leOfHom i).choose

theorem basicOpen_transElt {U V : Y.AffineZariskiSite} (i : U ⟶ V) :
    Y.basicOpen (transElt i) = U.1 :=
  (leOfHom i).choose_spec

theorem image_top_eq {U V : Y.AffineZariskiSite} (i : U ⟶ V) (r : Γ(Y, V.1))
    (hr : Y.basicOpen r = U.1) :
    Spec.map (A.sections.map i.op) ''ᵁ ⊤ =
      PrimeSpectrum.basicOpen (A.structureMap.app (op V) r) := by
  obtain rfl : U = V.basicOpen r := Subtype.ext hr.symm
  obtain rfl : i = homOfLE (V.basicOpen_le r) := Subsingleton.elim _ _
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact Scheme.AffineZariskiSite.opensRange_relativeGluingData_map _ _ A.coequifibered r

theorem isLocalization {U V : Y.AffineZariskiSite} (i : U ⟶ V) (r : Γ(Y, V.1))
    (hr : Y.basicOpen r = U.1) :
    letI := (A.sections.map i.op).hom.toAlgebra
    IsLocalization.Away (A.structureMap.app (op V) r) (A.sections.obj (op U)) := by
  obtain rfl : U = V.basicOpen r := Subtype.ext hr.symm
  obtain rfl : i = homOfLE (V.basicOpen_le r) := Subsingleton.elim _ _
  exact Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp
    A.coequifibered V r

theorem specMap_comp {U V W : Y.AffineZariskiSite} (i : U ⟶ V) (j : V ⟶ W) :
    Spec.map (A.sections.map (i ≫ j).op) =
      Spec.map (A.sections.map i.op) ≫ Spec.map (A.sections.map j.op) := by
  rw [op_comp, Functor.map_comp, Spec.map_comp]

variable (D : RelSpecModuleData A)

/-- The transition isomorphisms `N(V)~|_{Spec A(U)} ≅ N(U)~`. -/
def θ {U V : Y.AffineZariskiSite} (i : U ⟶ V) :
    (tilde (D.N V)).restrict (Spec.map (A.sections.map i.op)) ≅ tilde (D.N U) :=
  haveI := D.isLocalizedModule i (transElt i) (basicOpen_transElt i)
  TildeRestrict.iso (A.sections.map i.op) (A.structureMap.app (op V) (transElt i))
    (image_top_eq i _ (basicOpen_transElt i)) (isLocalization i _ (basicOpen_transElt i)) (D.ρ i)

theorem θ_hom_app_top_toOpen {U V : Y.AffineZariskiSite} (i : U ⟶ V) (n : D.N V) :
    (D.θ i).hom.app ⊤ ((tilde.toOpen (D.N V) (Spec.map (A.sections.map i.op) ''ᵁ ⊤)).hom n) =
      (tilde.toOpen (D.N U) ⊤).hom ((D.ρ i).hom n) :=
  haveI := D.isLocalizedModule i (transElt i) (basicOpen_transElt i)
  TildeRestrict.iso_hom_app_top_toOpen _ _ _ _ _ n

/-- The global sections of `N(V)~|_{Spec A(U)}` are generated, up to the units `s ^ k`, by the
sections `n / 1` for `n ∈ N(V)`, and morphisms are linear: so they are determined by their values on
the sections `n / 1`. -/
theorem hom_ext_toOpen {U V : Y.AffineZariskiSite} (i : U ⟶ V) {Q : (Spec (A.sections.obj (op U))).Modules}
    {g h : (tilde (D.N V)).restrict (Spec.map (A.sections.map i.op)) ⟶ Q}
    (hQ : ∀ (a : A.sections.obj (op U)) (q : Γ(Q, ⊤)), IsUnit a → a • q = 0 → q = 0)
    (H : ∀ n : D.N V,
      g.app ⊤ ((tilde.toOpen (D.N V) (Spec.map (A.sections.map i.op) ''ᵁ ⊤)).hom n) =
        h.app ⊤ ((tilde.toOpen (D.N V) (Spec.map (A.sections.map i.op) ''ᵁ ⊤)).hom n)) :
    g = h := by
  apply TildeRestrict.hom_ext
  intro x
  let s := A.structureMap.app (op V) (transElt i)
  have := TildeRestrict.isLocalizedModule_toOpen (A.sections.map i.op) s
    (image_top_eq i _ (basicOpen_transElt i)) (N := D.N V)
  obtain ⟨⟨n, ⟨_, k, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers s)
    (tilde.toOpen (D.N V) (Spec.map (A.sections.map i.op) ''ᵁ ⊤)).hom x
  have key : ∀ g' : (tilde (D.N V)).restrict (Spec.map (A.sections.map i.op)) ⟶ Q,
      g'.app ⊤ ((tilde.toOpen (D.N V) (Spec.map (A.sections.map i.op) ''ᵁ ⊤)).hom n) =
        (A.sections.map i.op (s ^ k)) • g'.app ⊤ x := by
    intro g'
    rw [← hx]
    have h1 := Scheme.Modules.restrictAppIso_smul_Spec (M := tilde (D.N V))
      (A.sections.map i.op) (U := ⊤) (s ^ k) x
    exact (congrArg (g'.app ⊤) h1.symm).trans
      (((modulesSpecToSheaf.map g').1.app (op ⊤)).hom.map_smul _ x)
  have hu : IsUnit (A.sections.map i.op (s ^ k)) := by
    let := (A.sections.map i.op).hom.toAlgebra
    have := isLocalization (A := A) i _ (basicOpen_transElt i)
    exact IsLocalization.map_units (A.sections.obj (op U)) (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)
  have h2 : (A.sections.map i.op (s ^ k)) • (g.app ⊤ x - h.app ⊤ x) = 0 := by
    rw [smul_sub, ← key, ← key, H, sub_self]
  exact sub_eq_zero.mp (hQ _ _ hu h2)

/-- The cocycle condition for the transition isomorphisms `θ`. -/
theorem θ_comp {U V W : Y.AffineZariskiSite} (i : U ⟶ V) (j : V ⟶ W) :
    (D.θ (i ≫ j)).hom =
      (Scheme.Modules.restrictFunctorCongr (specMap_comp i j)).hom.app (tilde (D.N W)) ≫
        (Scheme.Modules.restrictFunctorComp (Spec.map (A.sections.map i.op))
          (Spec.map (A.sections.map j.op))).hom.app (tilde (D.N W)) ≫
        (Scheme.Modules.restrictFunctor (Spec.map (A.sections.map i.op))).map (D.θ j).hom ≫
        (D.θ i).hom := by
  apply D.hom_ext_toOpen (i ≫ j)
  · intro a q ha hq
    exact ha.smul_left_cancel.mp (hq.trans (smul_zero a).symm)
  · intro n
    refine (D.θ_hom_app_top_toOpen (i ≫ j) n).trans ?_
    refine (congrArg (tilde.toOpen (D.N U) ⊤).hom (D.ρ_comp i j n)).trans ?_
    have h1 : (D.θ j).hom.app (Spec.map (A.sections.map i.op) ''ᵁ ⊤)
        ((tilde.toOpen (D.N W) (Spec.map (A.sections.map j.op) ''ᵁ
          (Spec.map (A.sections.map i.op) ''ᵁ ⊤))).hom n) =
        (tilde.toOpen (D.N V) (Spec.map (A.sections.map i.op) ''ᵁ ⊤)).hom ((D.ρ j).hom n) := by
      have h2 : (D.θ j).hom.app (Spec.map (A.sections.map i.op) ''ᵁ ⊤)
          (((tilde (D.N W)).restrict (Spec.map (A.sections.map j.op))).presheaf.map
            (homOfLE (le_top : Spec.map (A.sections.map i.op) ''ᵁ ⊤ ≤ ⊤)).op
            ((tilde.toOpen (D.N W) (Spec.map (A.sections.map j.op) ''ᵁ ⊤)).hom n)) =
          (tilde (D.N V)).presheaf.map
            (homOfLE (le_top : Spec.map (A.sections.map i.op) ''ᵁ ⊤ ≤ ⊤)).op
            ((D.θ j).hom.app ⊤ ((tilde.toOpen (D.N W) (Spec.map (A.sections.map j.op) ''ᵁ ⊤)).hom n)) :=
        ConcreteCategory.congr_hom ((D.θ j).hom.mapPresheaf.naturality
          (homOfLE (le_top : Spec.map (A.sections.map i.op) ''ᵁ ⊤ ≤ ⊤)).op) _
      rw [θ_hom_app_top_toOpen] at h2
      exact h2
    refine ((congrArg ((D.θ i).hom.app ⊤) h1).trans (D.θ_hom_app_top_toOpen i _)).symm.trans ?_
    rfl

/-- The descent datum of the sheaves `N(U)~` along the cover of `Spec_Y A` by the pieces
`Spec A(U)`. -/
def dataTr : DirectedModuleGluing.DataTr A.gluingData.cover where
  M U := tilde (D.N U)
  tr i := Spec.map (A.sections.map i.op)
  tr_open i := isOpenImmersion_specMap i
  tr_eq _ := rfl
  tr_comp i j := specMap_comp i j
  θ i := D.θ i
  θ_comp i j := D.θ_comp i j

/-- **The glued module** on `Spec_Y A`. -/
def glue : A.relSpec.Modules := D.dataTr.glue

/-- The restriction of the glued module to the piece `Spec A(U)` is `N(U)~`. -/
def ψ (U : Y.AffineZariskiSite) : D.glue.restrict (A.ι U) ≅ tilde (D.N U) := D.dataTr.ψ U

end RelSpecModuleData

end Hartshorne
