/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeDifferentials
import Hartshorne.Scheme.LocallyFreeInvertible
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Differentials on affine schemes

Hartshorne, *Algebraic Geometry*, II.8, Remark 8.9.2 and Example 8.12.1 (pp. 175–176).

For a ring map `A → B`, the relative differential sheaf of `Spec B ⟶ Spec A` is identified with
the sheaf `(Ω_{B/A})^~` associated to the Kähler module, and under this identification the
canonical derivation of the sheaf is induced by the universal derivation `d : B → Ω_{B/A}`.
As a corollary, the relative differential sheaf of affine space `Spec A[x_i] ⟶ Spec A` is free on
the global sections `d x_i`.

The proof constructs a derivation `𝒪 ⟶ (Ω_{B/A})^~` stalkwise, using that `Ω_{B_𝔭/A}` is the
localization of `Ω_{B/A}` at `𝔭`; it vanishes on the inverse image of `𝒪_{Spec A}` because the
structure map factors through the subsheaf of functions with vanishing derivative.  This pair
corepresents relative derivations: a derivation on `Spec B` is determined by its values on the
global functions coming from `B`, and the tilde–global-sections adjunction turns the induced
`A`-derivation of `B` into the required linear map.  The isomorphism is then the unique one given
by the universal property of the relative differential sheaf.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SpecKaehler

variable (A : Type u) {B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The universal derivation of `B_𝔭`, with values in the localization `(Ω_{B/A})_𝔭`. -/
noncomputable def pointD (x : PrimeSpectrum B) :
    Localization.AtPrime x.asIdeal →+ LocalizedModule x.asIdeal.primeCompl Ω[B⁄A] :=
  AddMonoidHom.comp
    (LinearMap.toAddMonoidHom (IsLocalizedModule.iso x.asIdeal.primeCompl
      (KaehlerDifferential.map A A B (Localization.AtPrime x.asIdeal))).symm.toLinearMap)
    (KaehlerDifferential.D A (Localization.AtPrime x.asIdeal)).toLinearMap.toAddMonoidHom

theorem pointD_algebraMap (x : PrimeSpectrum B) (b : B) :
    pointD A x (algebraMap B _ b) = LocalizedModule.mk (KaehlerDifferential.D A B b) 1 := by
  simp only [pointD, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    Derivation.coeFn_coe]
  rw [← KaehlerDifferential.map_D A A B (Localization.AtPrime x.asIdeal)]
  exact IsLocalizedModule.iso_symm_apply _ _ _

theorem pointIso_symm_smul (x : PrimeSpectrum B) (y : Localization.AtPrime x.asIdeal)
    (w : Ω[Localization.AtPrime x.asIdeal⁄A]) :
    (IsLocalizedModule.iso x.asIdeal.primeCompl
      (KaehlerDifferential.map A A B (Localization.AtPrime x.asIdeal))).symm (y • w) =
      y • (IsLocalizedModule.iso x.asIdeal.primeCompl
      (KaehlerDifferential.map A A B (Localization.AtPrime x.asIdeal))).symm w := by
  have := IsLocalization.linearMap_compatibleSMul x.asIdeal.primeCompl
    (Localization.AtPrime x.asIdeal) (Ω[Localization.AtPrime x.asIdeal⁄A])
    (LocalizedModule x.asIdeal.primeCompl Ω[B⁄A])
  exact LinearMap.map_smul_of_tower (IsLocalizedModule.iso x.asIdeal.primeCompl
      (KaehlerDifferential.map A A B (Localization.AtPrime x.asIdeal))).symm.toLinearMap y w

theorem pointD_mul (x : PrimeSpectrum B) (y z : Localization.AtPrime x.asIdeal) :
    pointD A x (y * z) = y • pointD A x z + z • pointD A x y := by
  simp only [pointD, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    Derivation.coeFn_coe, Derivation.leibniz, map_add, pointIso_symm_smul]

theorem pointD_mk (x : PrimeSpectrum B) (b : B) (s : x.asIdeal.primeCompl) :
    pointD A x (Localization.mk b s) =
      LocalizedModule.mk ((s : B) • KaehlerDifferential.D A B b - b • KaehlerDifferential.D A B s)
        (s * s) := by
  have key : algebraMap B (Localization.AtPrime x.asIdeal) s * Localization.mk b s =
      algebraMap B _ b := by
    rw [mul_comm, Localization.mk_eq_mk', IsLocalization.mk'_spec]
  have h := congrArg (pointD A x) key
  rw [pointD_mul, pointD_algebraMap, pointD_algebraMap,
    LocalizedModule.mk_smul_mk, IsScalarTower.algebraMap_smul, mul_one] at h
  have hs := IsLocalizedModule.map_units (S := x.asIdeal.primeCompl)
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl Ω[B⁄A]) s
  rw [Module.End.isUnit_iff] at hs
  apply hs.injective
  simp only [Module.algebraMap_end_apply]
  rw [eq_sub_of_add_eq h, LocalizedModule.smul'_mk, sub_eq_add_neg,
    ← LocalizedModule.mk_neg, LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, Submonoid.coe_mul, OneMemClass.coe_one]
  module

open Opposite TopologicalSpace

/-- The Kähler module as a module over the commutative-ring object. -/
noncomputable abbrev kaehlerModule : ModuleCat (CommRingCat.of B) :=
  ModuleCat.of (CommRingCat.of B) Ω[B⁄A]

/-- The derivation on sections, computed stalkwise. -/
noncomputable def sectionD (U : (Spec (CommRingCat.of B)).Opens) :
    (Spec (CommRingCat.of B)).presheaf.obj (op U) →+
      (tilde (kaehlerModule A (B := B))).val.obj (op U) where
  toFun s := ⟨fun x => pointD A x.1 (s.1 x), fun x => by
    obtain ⟨V, m, i, r, g, w⟩ := s.2 x
    refine ⟨V, m, i, g • KaehlerDifferential.D A B r - r • KaehlerDifferential.D A B g, g * g,
      fun y => ?_⟩
    obtain ⟨hg, hy⟩ := w y
    exact ⟨_, (congrArg (pointD A (y.1 : PrimeSpectrum B)) hy).trans
      (pointD_mk A (y.1 : PrimeSpectrum B) r ⟨g, hg⟩)⟩⟩
  map_zero' := Subtype.ext (funext fun x => map_zero (pointD A x.1))
  map_add' s t := Subtype.ext (funext fun x => map_add (pointD A x.1) (s.1 x) (t.1 x))

/-- The structure morphism `Spec B ⟶ Spec A`. -/
noncomputable abbrev specMap : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- Sections whose stalkwise derivative vanishes. -/
def kerSubring (U : (Spec (CommRingCat.of B)).Opens) :
    Subring ((Spec (CommRingCat.of B)).presheaf.obj (op U)) where
  carrier := {s | ∀ x : U, pointD A x.1 (s.1 x) = 0}
  mul_mem' {a b} ha hb x := (pointD_mul A x.1 (a.1 x) (b.1 x)).trans (by
    rw [ha x, hb x, smul_zero, smul_zero, add_zero])
  one_mem' x := by
    change pointD A x.1 1 = 0
    simp [pointD]
  add_mem' {a b} ha hb x := (map_add (pointD A x.1) (a.1 x) (b.1 x)).trans (by
    rw [ha x, hb x, add_zero])
  zero_mem' x := map_zero (pointD A x.1)
  neg_mem' {a} ha x := (map_neg (pointD A x.1) (a.1 x)).trans (by rw [ha x, neg_zero])

/-- The presheaf of sections with vanishing derivative. -/
noncomputable def kerPresheaf : TopCat.Presheaf CommRingCat (Spec (CommRingCat.of B)) where
  obj U := CommRingCat.of (kerSubring A U.unop)
  map {_ _} i := CommRingCat.ofHom (((Spec (CommRingCat.of B)).presheaf.map i).hom.restrict _ _
    (fun _ hs x => hs ⟨x.1, i.unop.le x.2⟩))
  map_id _ := rfl
  map_comp _ _ := rfl

theorem kerPresheaf_isSheaf : (kerPresheaf A (B := B)).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hsf' : TopCat.Presheaf.IsCompatible (Spec (CommRingCat.of B)).presheaf U
      (fun i => (sf i).1) := fun i j => congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hsu⟩ := (Spec (CommRingCat.of B)).sheaf.existsUnique_gluing U _ hsf'
  have hmem : s ∈ kerSubring A (iSup U) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    have := congrArg (fun t => pointD A x.1 (t.1 ⟨x.1, hi⟩)) (hs i)
    exact this.trans ((sf i).2 ⟨x.1, hi⟩)
  exact ⟨⟨s, hmem⟩, fun i => Subtype.ext (hs i),
    fun t ht => Subtype.ext (hsu t.1 fun i => congrArg Subtype.val (ht i))⟩

/-- The sheaf of sections with vanishing derivative. -/
noncomputable def kerSheaf : TopCat.Sheaf CommRingCat (Spec (CommRingCat.of B)) :=
  ⟨kerPresheaf A, kerPresheaf_isSheaf A⟩

/-- Its inclusion into the structure sheaf. -/
noncomputable def kerSheafι : kerSheaf A (B := B) ⟶ (Spec (CommRingCat.of B)).sheaf :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (R := kerSubring A U.unop)
        (S := (Spec (CommRingCat.of B)).presheaf.obj U) (kerSubring A U.unop).subtype
      naturality _ _ _ := rfl }

theorem pointD_mk_algebraMap (y : PrimeSpectrum B) (a h : A)
    (hh : algebraMap A B h ∈ y.asIdeal.primeCompl) :
    pointD A y (Localization.mk (algebraMap A B a) ⟨algebraMap A B h, hh⟩) = 0 := by
  rw [pointD_mk]
  simp

theorem c_app_mem (V : (Spec (CommRingCat.of A)).Opens)
    (t : (Spec (CommRingCat.of A)).presheaf.obj (op V)) :
    (specMap A (B := B)).c.app (op V) t ∈
      kerSubring A ((TopologicalSpace.Opens.map (specMap A (B := B)).base).obj V) := by
  intro y
  obtain ⟨W, m, i, a, h, w⟩ := t.2 ⟨PrimeSpectrum.comap (algebraMap A B) y.1, y.2⟩
  obtain ⟨hh, ht⟩ := w ⟨_, m⟩
  have := pointD_mk_algebraMap A y.1 a h hh
  convert this using 2
  exact (congrArg (StructureSheaf.Localizations.comapFun (algebraMap A B).toSemilinearMap y.1)
    ht).trans (StructureSheaf.Localizations.comapFun_mk _ _ _ _)

/-- The structure map of `Spec B ⟶ Spec A` factors through the vanishing subsheaf. -/
noncomputable def cFactor : (Spec (CommRingCat.of A)).sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat (specMap A (B := B)).base).obj (kerSheaf A) :=
  ObjectProperty.homMk
    { app V := CommRingCat.ofHom (R := (Spec (CommRingCat.of A)).presheaf.obj V)
        (S := kerSubring A ((TopologicalSpace.Opens.map (specMap A (B := B)).base).obj V.unop))
        (((specMap A (B := B)).c.app V).hom.codRestrict _ (fun t => c_app_mem A V.unop t))
      naturality _ _ _ := rfl }

theorem inverseImageStructureSheafMap_eq :
    Scheme.inverseImageStructureSheafMap (specMap A (B := B)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat (specMap A (B := B)).base).homEquiv
        _ _).symm (cFactor A) ≫ kerSheafι A := by
  rw [Scheme.inverseImageStructureSheafMap, ← Adjunction.homEquiv_naturality_right_symm]
  rfl

theorem inverseImageStructureSheafMap_mem (U : (Spec (CommRingCat.of B)).Opensᵒᵖ)
    (a : (Scheme.inverseImageStructureSheaf (specMap A (B := B))).obj.obj U) :
    (Scheme.inverseImageStructureSheafMap (specMap A (B := B))).hom.app U a ∈
      kerSubring A U.unop := by
  have h := congrArg (fun φ => φ.hom.app U a) (inverseImageStructureSheafMap_eq A (B := B))
  simp only at h
  rw [h]
  exact Subtype.property _

/-- The derivation `𝒪_{Spec B} ⟶ (Ω_{B/A})^~` induced stalkwise by `d : B → Ω_{B/A}`. -/
noncomputable def tildeDerivation :
    (tilde (kaehlerModule A (B := B))).val.Derivation'
      (Scheme.inverseImageStructureSheafMap (specMap A (B := B))).hom where
  d {U} := sectionD A U.unop
  d_mul {_} a b := Subtype.ext (funext fun x => pointD_mul A x.1 (a.1 x) (b.1 x))
  d_map _ _ := rfl
  d_app {U} a := Subtype.ext (funext fun x => inverseImageStructureSheafMap_mem A U a x)

/-- Restriction of a global function, viewed through `B ≅ Γ(Spec B, ⊤)`. -/
noncomputable abbrev globalRes (U : (Spec (CommRingCat.of B)).Opens) (b : B) :
    (Spec (CommRingCat.of B)).presheaf.obj (op U) :=
  (Spec (CommRingCat.of B)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)

/-- The section `f / g` on the basic open `D(g)`. -/
noncomputable abbrev constSec (f g : B) :
    (Spec (CommRingCat.of B)).presheaf.obj (op (PrimeSpectrum.basicOpen g)) :=
  StructureSheaf.const f g (PrimeSpectrum.basicOpen g) le_rfl

theorem const_mul_globalRes (f g : B) :
    constSec f g * globalRes (PrimeSpectrum.basicOpen g) g =
      globalRes (PrimeSpectrum.basicOpen g) f := by
  apply Subtype.ext
  funext x
  exact LocalizedModule.mk_mul_mk.trans
    (LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def, mul_comm]⟩)

variable {A} in
/-- Two relative derivations agreeing on the global functions coming from `B` coincide. -/
theorem derivation_ext {M : (Spec (CommRingCat.of B)).Modules}
    (D₁ D₂ : M.val.Derivation' (Scheme.inverseImageStructureSheafMap (specMap A (B := B))).hom)
    (h : ∀ b : B, D₁.d (X := op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) =
      D₂.d (X := op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) :
    D₁ = D₂ := by
  have hρ : ∀ (V : (Spec (CommRingCat.of B)).Opens) (c : B),
      D₁.d (globalRes V c) = D₂.d (globalRes V c) := fun V c =>
    (D₁.d_map V.leTop.op _).trans ((congrArg _ (h c)).trans (D₂.d_map V.leTop.op _).symm)
  have key : ∀ (f g : B) (t : (Spec (CommRingCat.of B)).presheaf.obj
      (op (PrimeSpectrum.basicOpen g))), t = constSec f g → D₁.d t = D₂.d t := by
    rintro f g t rfl
    have e₁ := (congrArg D₁.d (const_mul_globalRes f g)).symm.trans (D₁.d_mul _ _)
    have e₂ := (congrArg D₂.d (const_mul_globalRes f g)).symm.trans (D₂.d_mul _ _)
    have e := e₁.symm.trans ((hρ _ f).trans e₂)
    let c : (Spec (CommRingCat.of B)).ringCatSheaf.obj.obj (op (PrimeSpectrum.basicOpen g)) :=
      constSec f g
    let r : (Spec (CommRingCat.of B)).ringCatSheaf.obj.obj (op (PrimeSpectrum.basicOpen g)) :=
      globalRes (PrimeSpectrum.basicOpen g) g
    have e' := (congrArg (fun z => c • z + r • D₁.d (constSec f g)) (hρ _ g)).symm.trans e
    have e'' : r • D₁.d (constSec f g) = r • D₂.d (constSec f g) := add_left_cancel e'
    exact M.isSMulRegular_of_le_basicOpen (f := g) le_rfl e''
  ext U s
  apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj M).2
  intro x hxU
  obtain ⟨g, hxg, hgU, f, hf⟩ := StructureSheaf.exists_const _ s x hxU
  refine ⟨PrimeSpectrum.basicOpen g, hgU, hxg, ?_⟩
  exact ((D₁.d_map (homOfLE hgU).op s).symm.trans (key f g _ hf.symm)).trans
    (D₂.d_map (homOfLE hgU).op s)

theorem tildeDerivation_d_globalRes (U : (Spec (CommRingCat.of B)).Opens) (b : B) :
    (tildeDerivation A).d (X := op U) (globalRes U b) =
      ((tilde.toOpen (kaehlerModule A) U).hom (KaehlerDifferential.D A B b) :
        (tilde (kaehlerModule A (B := B))).val.obj (op U)) :=
  Subtype.ext (funext fun x => pointD_algebraMap A x.1 b)

theorem tildeDerivation_d_top (b : B) :
    (tildeDerivation A).d (X := op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) =
      ((tilde.toOpen (kaehlerModule A) ⊤).hom (KaehlerDifferential.D A B b) :
        (tilde (kaehlerModule A (B := B))).val.obj (op ⊤)) :=
  Subtype.ext (funext fun x => pointD_algebraMap A x.1 b)

theorem app_top_toOpen {M : (Spec (CommRingCat.of B)).Modules}
    (α : tilde (kaehlerModule A (B := B)) ⟶ M) (m : Ω[B⁄A]) :
    α.val.app (op ⊤) ((tilde.toOpen (kaehlerModule A) ⊤).hom m) =
      (tilde.adjunction.homEquiv (kaehlerModule A) M α) m := by
  exact (ConcreteCategory.congr_hom (tilde.adjunction.homEquiv_unit _ _ α) m).symm

theorem d_top_algebraMap {M : (Spec (CommRingCat.of B)).Modules}
    (D : M.val.Derivation' (Scheme.inverseImageStructureSheafMap (specMap A (B := B))).hom)
    (a : A) :
    D.d (X := op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap A B a)) = 0 := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat (specMap A (B := B)).base
  have h₁ : adj.homEquiv _ _ (Scheme.inverseImageStructureSheafMap (specMap A (B := B))) =
      ObjectProperty.homMk (specMap A (B := B)).c :=
    (adj.homEquiv _ _).apply_symm_apply _
  have h₂ := congrArg (fun φ => φ.hom.app (op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))
    ((adj.homEquiv_unit _ _ _).symm.trans h₁)
  have h₃ := congrArg (fun φ => φ a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
  simp only at h₂ h₃
  exact (congrArg D.d (h₃.trans h₂.symm)).trans (D.d_app _)

theorem postcomp_injective {M : (Spec (CommRingCat.of B)).Modules}
    (α₁ α₂ : tilde (kaehlerModule A (B := B)) ⟶ M)
    (h : (tildeDerivation A).postcomp α₁.val = (tildeDerivation A).postcomp α₂.val) :
    α₁ = α₂ := by
  apply (tilde.adjunction.homEquiv (kaehlerModule A) M).injective
  apply ModuleCat.hom_ext
  refine LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation A B) fun b => ?_
  have hb := PresheafOfModules.Derivation.congr_d h
    (X := op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
  exact (app_top_toOpen A α₁ _).symm.trans
    ((congrArg (fun z => α₁.val.app (op ⊤) z) (tildeDerivation_d_top A b)).symm.trans
      (hb.trans ((congrArg (fun z => α₂.val.app (op ⊤) z) (tildeDerivation_d_top A b)).trans
        (app_top_toOpen A α₂ _))))

set_option backward.isDefEq.respectTransparency false in
theorem postcomp_surjective {M : (Spec (CommRingCat.of B)).Modules}
    (D : M.val.Derivation' (Scheme.inverseImageStructureSheafMap (specMap A (B := B))).hom) :
    ∃ α : tilde (kaehlerModule A (B := B)) ⟶ M, (tildeDerivation A).postcomp α.val = D := by
  let N := (moduleSpecΓFunctor (R := CommRingCat.of B)).obj M
  let _ : Module A N := Module.compHom N (algebraMap A B)
  have _ : IsScalarTower A (CommRingCat.of B) N := IsScalarTower.of_compHom A (CommRingCat.of B) N
  let ι := (Scheme.ΓSpecIso (CommRingCat.of B)).inv
  let δ : Derivation A B N :=
    { toFun := fun b => D.d (X := op ⊤) (ι b)
      map_add' := fun b c => (congrArg D.d (map_add ι.hom b c)).trans (map_add D.d _ _)
      map_smul' := fun a b => by
        have e : ι (a • b) = ι (algebraMap A B a) * ι b := by
          rw [Algebra.smul_def, map_mul]
        refine (congrArg D.d e).trans ((D.d_mul _ _).trans ?_)
        rw [d_top_algebraMap, smul_zero, add_zero]
        rfl
      map_one_eq_zero' := (congrArg D.d (map_one ι.hom)).trans (D.d_one _)
      leibniz' := fun a b => (congrArg D.d (map_mul ι.hom a b)).trans (D.d_mul _ _) }
  let lin : kaehlerModule A ⟶ N :=
    ConcreteCategory.ofHom (C := ModuleCat (CommRingCat.of B)) (X := kaehlerModule A) (Y := N)
      δ.liftKaehlerDifferential
  refine ⟨(tilde.adjunction.homEquiv (kaehlerModule A) M).symm lin, ?_⟩
  apply derivation_ext
  intro b
  refine (congrArg (fun z => ((tilde.adjunction.homEquiv (kaehlerModule A) M).symm lin).val.app
    (op ⊤) z) (tildeDerivation_d_top A b)).trans ((app_top_toOpen A _ _).trans ?_)
  rw [Equiv.apply_symm_apply]
  exact δ.liftKaehlerDifferential_comp_D b

/-- The sheafified Kähler module corepresents relative derivations on `Spec B`. -/
noncomputable def tildeCorepresentable :
    (Scheme.relativeDerivationsFunctor (specMap A (B := B))).CorepresentableBy
      (tilde (kaehlerModule A (B := B))) where
  homEquiv := Equiv.ofBijective (fun α => (tildeDerivation A).postcomp α.val)
    ⟨fun _ _ h => postcomp_injective A _ _ h, fun D => postcomp_surjective A D⟩
  homEquiv_comp _ _ := rfl

end AlgebraicGeometry.SpecKaehler

namespace AlgebraicGeometry

open SpecKaehler Opposite

variable (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Hartshorne II, Remark 8.9.2: for a ring map `A → B`, the relative differential sheaf of
`Spec B ⟶ Spec A` is the sheaf associated to the Kähler module `Ω_{B/A}`. -/
noncomputable def Scheme.relativeDifferentialsSpecIso :
    Scheme.relativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≅
      tilde (ModuleCat.of (CommRingCat.of B) Ω[B⁄A]) :=
  (Scheme.relativeDifferentialsCorepresentable _).uniqueUpToIso (tildeCorepresentable A)

/-- The isomorphism carries the canonical derivation of the relative differential sheaf to the
derivation of `(Ω_{B/A})^~` induced stalkwise by the universal derivation of `B`. -/
theorem Scheme.relativeDifferentialsSpecIso_derivation :
    (Scheme.relativeDifferentialsDerivation
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).postcomp
        (Scheme.relativeDifferentialsSpecIso A B).hom.val = tildeDerivation A := by
  have he : Scheme.relativeDifferentialsHomEquiv _ _ (Scheme.relativeDifferentialsSpecIso A B).hom =
      (tildeCorepresentable A).homEquiv (𝟙 _) := by
    change (Scheme.relativeDifferentialsHomEquiv _ _)
      ((Scheme.relativeDifferentialsHomEquiv _ _).symm
        ((tildeCorepresentable A).homEquiv (𝟙 _))) = _
    exact (Scheme.relativeDifferentialsHomEquiv _ _).apply_symm_apply _
  refine ((Scheme.relativeDifferentialsHomEquiv_apply _ _ _).symm.trans he).trans ?_
  ext U a
  rfl

/-- Under `Scheme.relativeDifferentialsSpecIso`, the canonical derivation of the relative
differential sheaf is the universal derivation `d : B → Ω_{B/A}`, on every open set. -/
theorem Scheme.relativeDifferentialsSpecIso_hom_d (U : (Spec (CommRingCat.of B)).Opens) (b : B) :
    (Scheme.relativeDifferentialsSpecIso A B).hom.val.app (op U)
      ((Scheme.relativeDifferentialsDerivation
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).d (X := op U)
        ((Spec (CommRingCat.of B)).presheaf.map U.leTop.op
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) =
      ((tilde.toOpen (ModuleCat.of (CommRingCat.of B) Ω[B⁄A]) U).hom
        (KaehlerDifferential.D A B b) :
          (tilde (ModuleCat.of (CommRingCat.of B) Ω[B⁄A])).val.obj (op U)) :=
  (PresheafOfModules.Derivation.congr_d
    (Scheme.relativeDifferentialsSpecIso_derivation A B) _).trans
    (tildeDerivation_d_globalRes A U b)

/-- The global section `d b` of the relative differential sheaf attached to a global function. -/
noncomputable def Scheme.relativeDifferentialsDSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : Γ(X, ⊤)) : (Scheme.relativeDifferentials f).sections :=
  PresheafOfModules.sectionsMk
    (fun U => (Scheme.relativeDifferentialsDerivation f).d (X.presheaf.map U.unop.leTop.op b))
    (fun _ _ i => ((Scheme.relativeDifferentialsDerivation f).d_map i _).symm.trans
      (congrArg _ ((ConcreteCategory.comp_apply _ _ b).symm.trans
        (ConcreteCategory.congr_hom (X.presheaf.map_comp _ _).symm b))))

end AlgebraicGeometry

namespace AlgebraicGeometry.SpecKaehler

open Opposite

@[deprecated Scheme.Modules.tildeSection (since := "2026-11-09")]
alias tildeSection := Scheme.Modules.tildeSection

variable (A σ : Type u) [CommRing A]

theorem sectionsMap_dSection (b : MvPolynomial σ A) :
    SheafOfModules.sectionsMap (Scheme.relativeDifferentialsSpecIso A (MvPolynomial σ A)).hom
      (Scheme.relativeDifferentialsDSection _ ((Scheme.ΓSpecIso _).inv b)) =
      Scheme.Modules.tildeSection (KaehlerDifferential.D A (MvPolynomial σ A) b) :=
  PresheafOfModules.sections_ext _ _ fun U =>
    Scheme.relativeDifferentialsSpecIso_hom_d A (MvPolynomial σ A) U.unop b

@[deprecated Scheme.Modules.tilde_app_toOpen (since := "2026-11-09")]
alias app_toOpen := Scheme.Modules.tilde_app_toOpen

/-- The relative differentials of `A[x_i] / A`, read as `Ω~`, are free on the `d x_i`: a special
case of `Scheme.Modules.isIso_freeHomEquiv_symm_tildeSection` for the basis `d x_i`. -/
theorem tilde_free_isIso :
    IsIso ((tilde (kaehlerModule A (B := MvPolynomial σ A))).freeHomEquiv.symm
      (fun i => Scheme.Modules.tildeSection
        (KaehlerDifferential.D A (MvPolynomial σ A) (MvPolynomial.X i)))) := by
  have e : (fun i => Scheme.Modules.tildeSection (N := kaehlerModule A (B := MvPolynomial σ A))
      (KaehlerDifferential.D A (MvPolynomial σ A) (MvPolynomial.X i))) =
      fun i => Scheme.Modules.tildeSection (N := kaehlerModule A (B := MvPolynomial σ A))
        (KaehlerDifferential.mvPolynomialBasis A σ i) :=
    funext fun i => by rw [KaehlerDifferential.mvPolynomialBasis_apply]
  rw [e]
  exact Scheme.Modules.isIso_freeHomEquiv_symm_tildeSection
    (R := CommRingCat.of (MvPolynomial σ A)) (N := kaehlerModule A)
    (KaehlerDifferential.mvPolynomialBasis A σ)

end AlgebraicGeometry.SpecKaehler

namespace AlgebraicGeometry

open SpecKaehler

variable (A σ : Type u) [CommRing A]

set_option backward.isDefEq.respectTransparency false in
/-- Hartshorne II, Example 8.12.1: the relative differential sheaf of affine space
`Spec A[x_i | i ∈ σ] ⟶ Spec A` is free on the global sections `d x_i`. -/
theorem Scheme.relativeDifferentials_mvPolynomial_free :
    IsIso ((Scheme.relativeDifferentials
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial σ A))))).freeHomEquiv.symm
        (fun i => Scheme.relativeDifferentialsDSection _
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial σ A))).inv (MvPolynomial.X i)))) := by
  have := tilde_free_isIso A σ
  have h : (Scheme.relativeDifferentials
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial σ A))))).freeHomEquiv.symm
        (fun i => Scheme.relativeDifferentialsDSection _
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial σ A))).inv (MvPolynomial.X i))) =
      (tilde (kaehlerModule A (B := MvPolynomial σ A))).freeHomEquiv.symm
        (fun i => Scheme.Modules.tildeSection
          (KaehlerDifferential.D A (MvPolynomial σ A) (MvPolynomial.X i))) ≫
        (Scheme.relativeDifferentialsSpecIso A (MvPolynomial σ A)).inv := by
    rw [Iso.eq_comp_inv, SheafOfModules.freeHomEquiv_symm_comp]
    congr 1
    funext i
    exact sectionsMap_dSection A σ _
  rw [h]
  infer_instance

/-- Hartshorne II, Example 8.12.1 for affine `n`-space `𝔸ⁿ_A = Spec A[x₁, …, xₙ]`: its relative
differential sheaf over `Spec A` is free on `d x₁, …, d xₙ`. -/
theorem Scheme.relativeDifferentials_affineSpace_free (n : ℕ) :
    IsIso ((Scheme.relativeDifferentials (Spec.map
      (CommRingCat.ofHom (algebraMap A (MvPolynomial (ULift.{u} (Fin n)) A))))).freeHomEquiv.symm
        (fun i => Scheme.relativeDifferentialsDSection _
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) A))).inv
            (MvPolynomial.X i)))) :=
  Scheme.relativeDifferentials_mvPolynomial_free A (ULift.{u} (Fin n))

end AlgebraicGeometry
