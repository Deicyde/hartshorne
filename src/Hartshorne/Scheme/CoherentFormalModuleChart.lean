/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModuleLocality
import Hartshorne.Scheme.AlgebraizableFormalScheme

/-!
# A coherent formal module is complete

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.6(a) (pp. 197–198): for an ideal of
definition `J` of a Noetherian formal scheme `X` and a coherent `𝒪_X`-module `F`, the canonical
map `F ⟶ lim_n F / J ^ (n + 1) F` is an isomorphism
(`Hartshorne.IsIdealOfDefinition.isIso_toLimitPowQuotient`).

Inverse images of ideals (`IdealSubsheaf` namespace):

* `Hartshorne.IdealSubsheaf.comap f K`: for a morphism `f : B ⟶ A` of locally ringed spaces and an
  ideal subsheaf `K` of `𝒪_B`, the ideal subsheaf of `𝒪_A` of sections whose image in `𝒪_B`
  lies in `K`; `comap_comp`, `comap_id`, `comap_mono`, `pow_comap_le` (`(f⁻¹ K) ^ k ⊆ f⁻¹ (K ^ k)`)
  and `comap_pow_of_iso` (equality along an isomorphism).
* `Hartshorne.IdealSubsheaf.comap_le_vanishingIdealSubsheaf`: for `f` surjective on points, the
  inverse image of an ideal of sections with non-unit germs again has non-unit germs;
  `IdealSubsheaf.restrict_vanishingIdealSubsheaf`: that ideal restricts to opens.

Transport along an isomorphism `e : A ≅ B` of locally ringed spaces, with `e⁻¹_*` the pushforward
of modules along `e⁻¹ : B ⟶ A` (`IdealSubsheaf.pushforwardModule`):

* `Hartshorne.IdealSubsheaf.mem_smulSubmodule_of_mem_comap`,
  `IdealSubsheaf.mem_comap_smulSubmodule_of_mem`: `e⁻¹_*` carries `K M` onto `(e⁻¹ K) (e⁻¹_* M)`.
* `Hartshorne.IdealSubsheaf.epi_pushforward_map`: `e⁻¹_*` preserves epimorphisms.
* `Hartshorne.IdealSubsheaf.isIso_toLimitPowQuotient_pushforward`: if `M` is complete for `K`, then
  `e⁻¹_* M` is complete for `e⁻¹ K`.

The completion `Ŷ` of a Noetherian scheme `Y` along a closed subscheme (`QuasicoherentIdealSubsheaf`
namespace):

* `Hartshorne.QuasicoherentIdealSubsheaf.isIdealOfDefinition_formalCompletionIdealSubsheaf`: the
  kernel of `𝒪_{Ŷ} ⟶ 𝒪_{Y_1}` is an ideal of definition of `Ŷ`; `(Ŷ, 𝒪_{Ŷ} / J)` is `Y_1`
  (`QuasicoherentIdealSubsheaf.infinitesimalNeighborhoodOneRestrictIso`).

On a chart `e : U ≅ Ŷ` of `X` (`IsIdealOfDefinition` namespace):

* `Hartshorne.IsIdealOfDefinition.exists_pow_comap_le_restrict`,
  `IsIdealOfDefinition.exists_pow_restrict_le_comap`: `J|_U` and the inverse image of
  `ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})` have mutually cofinal powers, by Proposition 9.5(a) on `X` and on `Ŷ`.
* `Hartshorne.IsIdealOfDefinition.isIso_toLimitPowQuotient_chart`: the transported completion of a
  coherent module is complete for `J|_U`.

Proof outline. Completeness is local (`IdealSubsheaf.isIso_toLimitPowQuotient_of_iSup_eq_top`) and
invariant under isomorphism of modules, so it suffices to treat `e⁻¹_* Ĝ` on a chart. The
completion `Ĝ` is complete for `ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})`
(`QuasicoherentIdealSubsheaf.isIso_toLimitPowQuotient_moduleCompletion`); this transports along
`e`, and cofinality replaces the transported ideal by `J|_U`.
-/

noncomputable section
open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne
universe u

namespace IdealSubsheaf

variable {A B C : LocallyRingedSpace.{u}}

/-- The map `𝒪_A(V) ⟶ 𝒪_B(f⁻¹ V)` of a morphism of locally ringed spaces commutes with
restriction. -/
private lemma c_app_res (f : B ⟶ A) {V W : Opens A} (h : W ≤ V) (s : A.presheaf.obj (op V)) :
    f.c.app (op W) (A.presheaf.map (homOfLE h).op s) =
      B.presheaf.map (homOfLE ((Opens.map f.base).monotone h)).op (f.c.app (op V) s) :=
  NatTrans.naturality_apply f.c (homOfLE h).op s

/-- **The inverse image of an ideal subsheaf along a morphism** `f : B ⟶ A` of locally ringed
spaces: over an open `V` of `A`, the sections `s` of `𝒪_A` whose image in `𝒪_B(f⁻¹ V)` lies in
`K(f⁻¹ V)`. -/
def comap (f : B ⟶ A) (K : IdealSubsheaf B.sheaf) : IdealSubsheaf A.sheaf :=
  ofIdeals _ (fun V => (K.ideal ((Opens.map f.base).obj V)).comap (f.c.app (op V)).hom)
    (fun {V W} hWV s hs => by
      have := K.ideal_le_comap ((Opens.map f.base).monotone hWV) hs
      show f.c.app (op W) (A.presheaf.map (homOfLE hWV).op s) ∈
        K.ideal ((Opens.map f.base).obj W)
      exact (c_app_res f hWV s).symm ▸ this)
    (fun {U} s hs => by
      refine K.mem_ideal_of_locally _ fun y hy => ?_
      obtain ⟨V, hVU, hyV, hsV⟩ := hs (f.base y) hy
      refine ⟨(Opens.map f.base).obj V, (Opens.map f.base).monotone hVU, hyV, ?_⟩
      have : f.c.app (op V) (A.presheaf.map (homOfLE hVU).op s) ∈
          K.ideal ((Opens.map f.base).obj V) := hsV
      exact (c_app_res f hVU s) ▸ this)

lemma mem_comap_ideal_iff (f : B ⟶ A) (K : IdealSubsheaf B.sheaf) (V : Opens A)
    (s : A.presheaf.obj (op V)) :
    s ∈ (comap f K).ideal V ↔ f.c.app (op V) s ∈ K.ideal ((Opens.map f.base).obj V) :=
  Iff.rfl

lemma comap_mono (f : B ⟶ A) {K K' : IdealSubsheaf B.sheaf} (h : K ≤ K') :
    comap f K ≤ comap f K' :=
  le_iff.mpr fun _ _ hs => le_iff.mp h _ hs

lemma comap_comp (f : C ⟶ B) (g : B ⟶ A) (K : IdealSubsheaf C.sheaf) :
    comap (f ≫ g) K = comap g (comap f K) :=
  IdealSubsheaf.ext fun _ => rfl

lemma le_comap_id (K : IdealSubsheaf A.sheaf) : K ≤ comap (𝟙 A) K :=
  le_iff.mpr fun _ _ hs => hs

/-- `(f⁻¹ K) ^ k ⊆ f⁻¹ (K ^ k)`. -/
lemma pow_comap_le (f : B ⟶ A) (K : IdealSubsheaf B.sheaf) (k : ℕ) :
    comap f K ^ k ≤ comap f (K ^ k) := by
  refine le_iff.mpr fun V s hs y hy => ?_
  obtain ⟨W, hWV, hyW, hsW⟩ := hs (f.base y) hy
  refine ⟨(Opens.map f.base).obj W, (Opens.map f.base).monotone hWV, hyW, ?_⟩
  have h1 : f.c.app (op W) (A.presheaf.map (homOfLE hWV).op s) ∈
      K.ideal ((Opens.map f.base).obj W) ^ k := Ideal.le_comap_pow (f.c.app (op W)).hom k hsW
  exact (c_app_res f hWV s) ▸ h1

/-- **Inverse images of ideals of non-units.** If `f : B ⟶ A` is surjective on points and every
section of `K` has non-unit germs, then so does every section of `f⁻¹ K`: a section of `𝒪_A`
which is a unit near `f y` maps to a unit near `y`. -/
lemma comap_le_vanishingIdealSubsheaf (f : B ⟶ A) (hf : Function.Surjective f.base)
    {K : IdealSubsheaf B.sheaf} (hK : K ≤ vanishingIdealSubsheaf B) :
    comap f K ≤ vanishingIdealSubsheaf A := by
  refine le_iff.mpr fun V s hs => (mem_vanishingIdealSubsheaf_iff s).mpr fun x hx hu => ?_
  obtain ⟨W, i, hxW, hW⟩ := A.toRingedSpace.isUnit_res_of_isUnit_germ V s x hx hu
  obtain ⟨y, rfl⟩ := hf x
  have h1 : IsUnit (f.c.app (op W) (A.presheaf.map (homOfLE (leOfHom i)).op
      (show A.presheaf.obj (op V) from s))) := hW.map _
  replace h1 := (c_app_res f (leOfHom i) s) ▸ h1
  have h2 : IsUnit (B.presheaf.germ ((Opens.map f.base).obj W) y hxW
      (B.presheaf.map (homOfLE ((Opens.map f.base).monotone (leOfHom i))).op
        (f.c.app (op V) s))) := h1.map _
  have h3 : B.presheaf.germ ((Opens.map f.base).obj W) y hxW
      (B.presheaf.map (homOfLE ((Opens.map f.base).monotone (leOfHom i))).op
        (f.c.app (op V) s)) = B.presheaf.germ ((Opens.map f.base).obj V) y hx (f.c.app (op V) s) :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  replace h2 := h3 ▸ h2
  exact (mem_vanishingIdealSubsheaf_iff (X := B) _).mp (le_iff.mp hK _ hs) y _ h2

lemma restrict_mono {X : LocallyRingedSpace.{u}} {U : TopCat.{u}} {f : U ⟶ X.toTopCat}
    (h : Topology.IsOpenEmbedding f) {J J' : IdealSubsheaf X.sheaf} (hJ : J ≤ J') :
    J.restrict h ≤ J'.restrict h :=
  le_iff.mpr fun _ => le_iff.mp hJ _

/-- **Non-units on an open subspace**: the ideal of sections with non-unit germs on `U` is the
restriction of that on `X`. -/
lemma restrict_vanishingIdealSubsheaf {X : LocallyRingedSpace.{u}} {U : TopCat.{u}}
    {f : U ⟶ X.toTopCat} (h : Topology.IsOpenEmbedding f) :
    (vanishingIdealSubsheaf X).restrict h = vanishingIdealSubsheaf (X.restrict h) := by
  ext V s
  refine (mem_vanishingIdealSubsheaf_iff (X := X) (V := h.functor.obj V) s).trans
    (Iff.trans ?_ (mem_vanishingIdealSubsheaf_iff (X := X.restrict h) s).symm)
  constructor
  · intro hs x hx hu
    obtain ⟨W, i, hxW, hW⟩ := (X.restrict h).toRingedSpace.isUnit_res_of_isUnit_germ V s x hx hu
    have h2 : IsUnit (X.presheaf.germ (h.functor.obj W) (f x) ⟨x, hxW, rfl⟩
        ((X.restrict h).presheaf.map i.op s)) := hW.map _
    have h3 : X.presheaf.germ (h.functor.obj W) (f x) ⟨x, hxW, rfl⟩
        ((X.restrict h).presheaf.map i.op s) =
        X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ s :=
      X.presheaf.germ_res_apply (h.functor.map i) (f x) ⟨x, hxW, rfl⟩ s
    exact hs (f x) ⟨x, hx, rfl⟩ (h3 ▸ h2)
  · rintro hs _ ⟨x, hx, rfl⟩ hu
    obtain ⟨W, i, hxW, hW⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ _ s (f x) ⟨x, hx, rfl⟩ hu
    let W' : Opens U := (Opens.map f).obj W ⊓ V
    have hle : h.functor.obj W' ≤ W := by
      rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
      exact hz
    have h1 : IsUnit (X.presheaf.map (homOfLE hle).op (X.presheaf.map i.op s)) := hW.map _
    have e : X.presheaf.map (homOfLE hle).op (X.presheaf.map i.op s) =
        (X.restrict h).presheaf.map (homOfLE (inf_le_right : W' ≤ V)).op s :=
      (X.presheaf.map_comp_apply i.op (homOfLE hle).op s).symm
    have h2 : IsUnit ((X.restrict h).presheaf.germ W' x ⟨hxW, hx⟩
        ((X.restrict h).presheaf.map (homOfLE (inf_le_right : W' ≤ V)).op s)) :=
      (e ▸ h1).map _
    have h3 : (X.restrict h).presheaf.germ W' x ⟨hxW, hx⟩
        ((X.restrict h).presheaf.map (homOfLE (inf_le_right : W' ≤ V)).op s) =
        (X.restrict h).presheaf.germ V x hx s :=
      (X.restrict h).presheaf.germ_res_apply (homOfLE inf_le_right) x ⟨hxW, hx⟩ s
    exact hs x hx (h3 ▸ h2)

end IdealSubsheaf

namespace QuasicoherentIdealSubsheaf

variable {Y : Scheme.{u}} (I : QuasicoherentIdealSubsheaf Y)

/-- The sections of `J = ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})` have non-unit germs: a section which is a unit
near a point maps to a unit of `𝒪_{Y_1}` near that point, while it maps to `0`. -/
lemma formalCompletionIdealSubsheaf_le_vanishingIdealSubsheaf :
    I.formalCompletionIdealSubsheaf ≤ vanishingIdealSubsheaf I.formalCompletion := by
  refine IdealSubsheaf.le_iff.mpr fun V a ha =>
    (mem_vanishingIdealSubsheaf_iff (X := I.formalCompletion) a).mpr fun y hy hu => ?_
  obtain ⟨W, i, hyW, hW⟩ := I.formalCompletion.toRingedSpace.isUnit_res_of_isUnit_germ V a y hy hu
  have h0 : (I.formalCompletionπ 0).hom.app (op W)
      (I.formalCompletionSheaf.presheaf.map (homOfLE (leOfHom i)).op a) = 0 :=
    I.formalCompletionIdeal_le_comap (leOfHom i) ha
  have h1 : IsUnit ((I.formalCompletionπ 0).hom.app (op W)
      (I.formalCompletionSheaf.presheaf.map (homOfLE (leOfHom i)).op a)) := hW.map _
  rw [h0] at h1
  have hnt : Nontrivial ((I.infinitesimalNeighborhood (0 + 1)).presheaf.obj
      (op ((I.isOpenEmbedding_infinitesimalNeighborhoodFromOne 0).functor.obj W))) :=
    @LocallyRingedSpace.component_nontrivial _ _ ⟨⟨_, y, hyW, rfl⟩⟩
  exact @not_isUnit_zero _ _ hnt h1

/-- `𝒪_{Ŷ} / J ≅ 𝒪_{Y_1}`, as sheaves of rings on `|Y|`. -/
def quotientFormalCompletionIdealSubsheafIso [IsLocallyNoetherian Y] :
    I.formalCompletionIdealSubsheaf.quotient ≅ I.formalCompletionSheafObj 0 :=
  eqToIso (congrArg IdealSubsheaf.quotient I.formalCompletionIdealSubsheaf.pow_one).symm ≪≫
    I.formalCompletionQuotientIso 0

/-- The scheme `Y_1` restricted along the homeomorphism `Y ⟶ Y_1`: a scheme with underlying space
`|Y|` and structure sheaf `𝒪_{Y_1}` read on `|Y|`. -/
abbrev infinitesimalNeighborhoodOneRestrict : Scheme.{u} :=
  (I.infinitesimalNeighborhood (0 + 1)).restrict
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne 0)

instance [IsNoetherian Y] : IsNoetherian I.infinitesimalNeighborhoodOneRestrict := by
  have : IsLocallyNoetherian (I.infinitesimalNeighborhood (0 + 1)) :=
    LocallyOfFiniteType.isLocallyNoetherian (I.infinitesimalNeighborhoodι (0 + 1))
  have : IsLocallyNoetherian I.infinitesimalNeighborhoodOneRestrict :=
    isLocallyNoetherian_of_isOpenImmersion (Scheme.ofRestrict _ _)
  have : CompactSpace (I.infinitesimalNeighborhood 1) :=
    (I.infinitesimalNeighborhoodι 1).isClosedEmbedding.compactSpace
  have : CompactSpace I.infinitesimalNeighborhoodOneRestrict :=
    inferInstanceAs (CompactSpace (I.infinitesimalNeighborhood 1))
  exact {}

/-- `(Ŷ, 𝒪_{Ŷ} / J)` is the scheme `Y_1`, as a ringed space. -/
def infinitesimalNeighborhoodOneRestrictIso [IsLocallyNoetherian Y] :
    I.infinitesimalNeighborhoodOneRestrict.toSheafedSpace ≅
      I.formalCompletionIdealSubsheaf.quotientSheafedSpace :=
  InducedCategory.isoMk (PresheafedSpace.isoOfComponents (Iso.refl _)
    ((sheafToPresheaf _ _).mapIso (I.quotientFormalCompletionIdealSubsheafIso).symm))

/-- **`J = ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})` is an ideal of definition** of the completion `Ŷ` of a
Noetherian scheme along a closed subscheme: `Supp (𝒪_{Ŷ} / J) = Ŷ`, as the sections of `J` have
non-unit germs, and `(Ŷ, 𝒪_{Ŷ} / J)` is the Noetherian scheme `Y_1`. -/
theorem isIdealOfDefinition_formalCompletionIdealSubsheaf [IsNoetherian Y] :
    IsIdealOfDefinition I.toNoetherianFormalScheme I.formalCompletionIdealSubsheaf where
  support_eq_univ := sheafSupport_quotientAb_of_le_vanishingIdealSubsheaf
    (X := I.formalCompletion) I.formalCompletionIdealSubsheaf_le_vanishingIdealSubsheaf
  isNoetherianScheme := ⟨I.infinitesimalNeighborhoodOneRestrict, inferInstance,
    ⟨I.infinitesimalNeighborhoodOneRestrictIso⟩⟩

end QuasicoherentIdealSubsheaf

/-! ### Transport of completeness along an isomorphism of locally ringed spaces -/

namespace IdealSubsheaf

variable {A B : LocallyRingedSpace.{u}}

lemma comap_id (K : IdealSubsheaf A.sheaf) : comap (𝟙 A) K = K :=
  IdealSubsheaf.ext fun _ => rfl

/-- Along an isomorphism, `f⁻¹ (K ^ k) = (f⁻¹ K) ^ k`. -/
lemma comap_pow_of_iso (e : A ≅ B) (K : IdealSubsheaf B.sheaf) (k : ℕ) :
    comap e.inv (K ^ k) = comap e.inv K ^ k := by
  refine le_antisymm ?_ (pow_comap_le _ _ k)
  have h1 : K ^ k ≤ comap e.hom (comap e.inv K ^ k) := by
    calc K ^ k = comap e.hom (comap e.inv K) ^ k := by rw [← comap_comp, e.inv_hom_id, comap_id]
      _ ≤ comap e.hom (comap e.inv K ^ k) := pow_comap_le _ _ k
  calc comap e.inv (K ^ k) ≤ comap e.inv (comap e.hom (comap e.inv K ^ k)) := comap_mono _ h1
    _ = comap e.inv K ^ k := by rw [← comap_comp, e.hom_inv_id, comap_id]

/-- The pushforward `f_* M` of a module along a morphism `f : B ⟶ A` of locally ringed spaces, as a
module over `𝒪_A` in the form used for ideal subsheaves. -/
abbrev pushforwardModule (f : B ⟶ A) (M : SheafOfModules.{u} (ringCatSheafOf B.sheaf)) :
    SheafOfModules.{u} (ringCatSheafOf A.sheaf) :=
  (structureModulePushforward f).obj M

variable (f : B ⟶ A) (K : IdealSubsheaf B.sheaf) (M : SheafOfModules.{u} (ringCatSheafOf B.sheaf))

/-- `(f⁻¹ K)(V) (f_* M)(V) ⊆ K(f⁻¹ V) M(f⁻¹ V)`. -/
lemma sectionsSmul_comap_le (V : Opens A) {s : (pushforwardModule f M).val.obj (op V)}
    (hs : s ∈ (comap f K).sectionsSmul (pushforwardModule f M) V) :
    (show M.val.obj (op ((Opens.map f.base).obj V)) from s) ∈
      K.sectionsSmul M ((Opens.map f.base).obj V) := by
  refine Submodule.smul_induction_on hs (fun r hr m _ => ?_) (fun a b ha hb => add_mem ha hb)
  change (show (ringCatSheafOf B.sheaf).obj.obj (op ((Opens.map f.base).obj V)) from
    f.c.app (op V) r) • (show M.val.obj (op ((Opens.map f.base).obj V)) from m) ∈ _
  exact Submodule.smul_mem_smul hr trivial

/-- A section of `f_* M` lying in `(f⁻¹ K) (f_* M)` lies in `K M`. -/
lemma mem_smulSubmodule_of_mem_comap (V : Opens A) (s : (pushforwardModule f M).val.obj (op V))
    (hs : s ∈ ((comap f K).smulSubmodule (pushforwardModule f M)).obj (op V)) :
    (show M.val.obj (op ((Opens.map f.base).obj V)) from s) ∈
      (K.smulSubmodule M).obj (op ((Opens.map f.base).obj V)) := by
  intro y hy
  obtain ⟨W, hWV, hxW, hsW⟩ := hs (f.base y) hy
  exact ⟨(Opens.map f.base).obj W, (Opens.map f.base).monotone hWV, hxW,
    sectionsSmul_comap_le f K M W hsW⟩

/-- For an isomorphism, `𝒪_A(V) ⟶ 𝒪_B(f⁻¹ V)` is surjective. -/
lemma surjective_inv_c_app (e : A ≅ B) (V : Opens A) : Function.Surjective (e.inv.c.app (op V)) :=
  have : IsIso e.inv.c := PresheafedSpace.c_isIso_of_iso
    (f := ((LocallyRingedSpace.forgetToSheafedSpace ⋙
      SheafedSpace.forgetToPresheafedSpace).mapIso e).inv)
  (ConcreteCategory.bijective_of_isIso (e.inv.c.app (op V))).2

/-- Along an isomorphism, `K(f⁻¹ V) M(f⁻¹ V) ⊆ (f⁻¹ K)(V) (f_* M)(V)`. -/
lemma sectionsSmul_le_comap (e : A ≅ B) (V : Opens A)
    {s : M.val.obj (op ((Opens.map e.inv.base).obj V))}
    (hs : s ∈ K.sectionsSmul M ((Opens.map e.inv.base).obj V)) :
    (show (pushforwardModule e.inv M).val.obj (op V) from s) ∈
      (comap e.inv K).sectionsSmul (pushforwardModule e.inv M) V := by
  refine Submodule.smul_induction_on hs (fun r hr m _ => ?_) (fun a b ha hb => add_mem ha hb)
  obtain ⟨r', rfl⟩ := surjective_inv_c_app e V r
  change (show (ringCatSheafOf A.sheaf).obj.obj (op V) from r') •
    (show (pushforwardModule e.inv M).val.obj (op V) from m) ∈ _
  exact Submodule.smul_mem_smul (show r' ∈ (comap e.inv K).ideal V from hr) trivial

/-- Along an isomorphism, a section of `M` lying in `K M` lies in `(f⁻¹ K) (f_* M)`. -/
lemma mem_comap_smulSubmodule_of_mem (e : A ≅ B) (V : Opens A)
    (s : M.val.obj (op ((Opens.map e.inv.base).obj V)))
    (hs : s ∈ (K.smulSubmodule M).obj (op ((Opens.map e.inv.base).obj V))) :
    (show (pushforwardModule e.inv M).val.obj (op V) from s) ∈
      ((comap e.inv K).smulSubmodule (pushforwardModule e.inv M)).obj (op V) := by
  intro x hx
  have hy : e.hom.base x ∈ (Opens.map e.inv.base).obj V := by
    change e.inv.base (e.hom.base x) ∈ V
    rwa [LocallyRingedSpace.iso_hom_base_inv_base_apply]
  obtain ⟨W', hW'V, hyW', hsW'⟩ := hs _ hy
  let W : Opens A := (Opens.map e.hom.base).obj W' ⊓ V
  have hle : (Opens.map e.inv.base).obj W ≤ W' := by
    intro z hz
    have : e.hom.base (e.inv.base z) ∈ W' := hz.1
    rwa [LocallyRingedSpace.iso_inv_base_hom_base_apply] at this
  refine ⟨W, inf_le_right, ⟨hyW', hx⟩, ?_⟩
  have h1 := K.map_mem_sectionsSmul M hle hsW'
  have h2 : M.val.restrictₛₗ (homOfLE hle).op (M.val.restrictₛₗ (homOfLE hW'V).op s) =
      M.val.restrictₛₗ (homOfLE ((Opens.map e.inv.base).monotone
        (inf_le_right : W ≤ V))).op s :=
    (M.val.map_comp_apply (homOfLE hW'V).op (homOfLE hle).op s).symm
  rw [h2] at h1
  exact sectionsSmul_le_comap K M e W h1

/-- The pushforward along an isomorphism of locally ringed spaces preserves epimorphisms: an
epimorphism of sheaves of modules is locally surjective, and the isomorphism carries
neighbourhoods to neighbourhoods. -/
lemma epi_pushforward_map (e : A ≅ B) {M N : SheafOfModules.{u} (ringCatSheafOf B.sheaf)}
    (g : M ⟶ N) [Epi g] : Epi ((structureModulePushforward e.inv).map g) := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf _).map ((structureModulePushforward e.inv).map g)).hom := by
    refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun V t x hx => ?_
    have hy : e.hom.base x ∈ (Opens.map e.inv.base).obj V := by
      change e.inv.base (e.hom.base x) ∈ V
      rwa [LocallyRingedSpace.iso_hom_base_inv_base_apply]
    obtain ⟨W', hW'V, hyW', s, hs⟩ :=
      sheafOfModules_exists_local_lift g (U := (Opens.map e.inv.base).obj V) t hy
    let W : Opens A := (Opens.map e.hom.base).obj W' ⊓ V
    have hle : (Opens.map e.inv.base).obj W ≤ W' := by
      intro z hz
      have : e.hom.base (e.inv.base z) ∈ W' := hz.1
      rwa [LocallyRingedSpace.iso_inv_base_hom_base_apply] at this
    refine ⟨W, inf_le_right, ⟨M.val.presheaf.map (homOfLE hle).op s, ?_⟩, ⟨hyW', hx⟩⟩
    have e1 := PresheafOfModules.naturality_apply g.val (homOfLE hle).op s
    rw [hs] at e1
    exact e1.trans ((N.val.map_comp_apply (homOfLE hW'V).op (homOfLE hle).op t).symm)
  have : Epi ((SheafOfModules.toSheaf _).map ((structureModulePushforward e.inv).map g)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hls
  exact (SheafOfModules.toSheaf _).epi_of_epi_map this

/-- **Completeness transports along an isomorphism of locally ringed spaces.** If `e : A ≅ B` and
`M` is complete for `K` on `B`, then `e⁻¹_* M` is complete for the inverse image of `K`. -/
theorem isIso_toLimitPowQuotient_pushforward (e : A ≅ B) [IsIso (K.toLimitPowQuotient M)] :
    IsIso ((comap e.inv K).toLimitPowQuotient (pushforwardModule e.inv M)) := by
  let P := structureModulePushforward e.inv
  have : (PresheafOfModules.pushforward.{u} (structureRingCatSheafHom e.inv).hom).IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top _)
  have : (SheafOfModules.pushforward.{u} (structureRingCatSheafHom e.inv)).IsRightAdjoint :=
    (SheafOfModules.PullbackConstruction.adjunction.{u} _).isRightAdjoint
  let Q : ℕ → SheafOfModules.{u} (ringCatSheafOf A.sheaf) :=
    fun n => pushforwardModule e.inv (K.powQuotient M n)
  let π : ∀ n, pushforwardModule e.inv M ⟶ Q n :=
    fun n => P.map (K.powQuotientπ M n)
  have : ∀ n, Epi (π n) := fun n => epi_pushforward_map e _
  have hz : ∀ n, (comap e.inv K ^ (n + 1)).smulι (pushforwardModule e.inv M) ≫ π n = 0 :=
    fun n => by
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
      ext ⟨s, hs⟩
      rw [← comap_pow_of_iso] at hs
      exact K.powQuotientπ_app_eq_zero M n _
        (mem_smulSubmodule_of_mem_comap e.inv (K ^ (n + 1)) M V.unop s hs)
  have hex : ∀ n (W : Opens A) (s : (pushforwardModule e.inv M).val.obj (op W)),
      (π n).val.app (op W) s = 0 →
        s ∈ ((comap e.inv K).powSubmodule (pushforwardModule e.inv M) n).obj (op W) := by
    intro n W s hs
    have h1 := K.mem_powSubmodule_of_powQuotientπ_app_eq_zero M n _ hs
    have h2 := mem_comap_smulSubmodule_of_mem (K ^ (n + 1)) M e W s h1
    rw [comap_pow_of_iso] at h2
    exact h2
  let t : ∀ n, Q (n + 1) ⟶ Q n := fun n => P.map (K.powQuotientMap M n)
  have ht : ∀ n, π (n + 1) ≫ t n = π n := fun n =>
    (P.map_comp _ _).symm.trans (congrArg P.map (K.powQuotientπ_powQuotientMap M n))
  refine ((comap e.inv K).isIso_toLimitPowQuotient_iff_of_kernel π hz hex t ht).mpr ⟨?_⟩
  have : P.IsRightAdjoint :=
    inferInstanceAs (SheafOfModules.pushforward.{u} (structureRingCatSheafHom e.inv)).IsRightAdjoint
  have hPl : PreservesLimitsOfShape ℕᵒᵖ P := inferInstance
  have hl : IsLimit (P.mapCone (K.powQuotientCone M)) :=
    (PreservesLimit.preserves (F := P) (K := K.powQuotientDiagram M) (self := hPl.preservesLimit)
      (K.isLimitPowQuotientConeOfIsIso M)).some
  let Ψ : K.powQuotientDiagram M ⋙ P ⟶ Functor.ofOpSequence (X := Q) t :=
    NatTrans.ofOpSequence (fun n => 𝟙 _) (fun n => by
      have h1 : (K.powQuotientDiagram M).map (homOfLE (n.le_add_right 1)).op =
          K.powQuotientMap M n := Functor.ofOpSequence_map_homOfLE_succ _ n
      have h2 : (Functor.ofOpSequence (X := Q) t).map (homOfLE (n.le_add_right 1)).op = t n :=
        Functor.ofOpSequence_map_homOfLE_succ _ n
      change P.map ((K.powQuotientDiagram M).map _) ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [h1]
      exact (Category.comp_id _).trans ((Category.id_comp _).trans h2).symm)
  have : IsIso Ψ := by
    have : ∀ n : ℕᵒᵖ, IsIso (Ψ.app n) := fun ⟨n⟩ => inferInstanceAs (IsIso (𝟙 _))
    exact NatIso.isIso_of_isIso_app _
  exact ((IsLimit.postcomposeHomEquiv (asIso Ψ) _).symm hl).ofIsoLimit
    (Cone.ext (Iso.refl _) fun ⟨n⟩ => by
      change P.map (K.powQuotientπ M n) ≫ 𝟙 _ = 𝟙 _ ≫ π n
      rw [Category.comp_id, Category.id_comp])

end IdealSubsheaf

namespace IsIdealOfDefinition

open IdealSubsheaf

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J) {U : Opens X.carrier} {Y : Scheme.{u}} [IsNoetherian Y]
  {I : QuasicoherentIdealSubsheaf Y} (e : X.restrict U.isOpenEmbedding ≅ I.formalCompletion)

omit [AlgebraicGeometry.IsNoetherian Y] in
include h in
/-- On a chart `e : U ≅ Ŷ`, a power of the inverse image of `ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})` lies in
`J|_U`: that inverse image consists of sections with non-unit germs, and a power of the ideal of
such sections lies in `J` (Proposition 9.5(a), through `J_red`). -/
theorem exists_pow_comap_le_restrict :
    ∃ a, 0 < a ∧
      comap e.inv I.formalCompletionIdealSubsheaf ^ a ≤ J.restrict U.isOpenEmbedding := by
  obtain ⟨a, ha, hle⟩ :=
    exists_pow_le h (sheafSupport_quotientAb_vanishingIdealSubsheaf (X := X.toLocallyRingedSpace))
  refine ⟨a, ha, ?_⟩
  have h1 : comap e.inv I.formalCompletionIdealSubsheaf ≤
      (vanishingIdealSubsheaf X.toLocallyRingedSpace).restrict U.isOpenEmbedding := by
    rw [restrict_vanishingIdealSubsheaf]
    exact comap_le_vanishingIdealSubsheaf e.inv
      (fun x => ⟨e.hom.base x, LocallyRingedSpace.iso_hom_base_inv_base_apply e x⟩)
      I.formalCompletionIdealSubsheaf_le_vanishingIdealSubsheaf
  calc _ ≤ ((vanishingIdealSubsheaf X.toLocallyRingedSpace).restrict U.isOpenEmbedding) ^ a :=
        pow_le_pow_left h1 a
    _ = (vanishingIdealSubsheaf X.toLocallyRingedSpace ^ a).restrict U.isOpenEmbedding :=
        restrict_pow _ _ a
    _ ≤ J.restrict U.isOpenEmbedding := restrict_mono _ hle

include h in
/-- On a chart `e : U ≅ Ŷ`, a power of `J|_U` lies in the inverse image of
`ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})`: transported to `Ŷ`, `J|_U` consists of sections with non-unit germs,
and the kernel is an ideal of definition of `Ŷ` (Proposition 9.5(a)). -/
theorem exists_pow_restrict_le_comap :
    ∃ b, 0 < b ∧
      J.restrict U.isOpenEmbedding ^ b ≤ comap e.inv I.formalCompletionIdealSubsheaf := by
  have h1 : comap e.hom (J.restrict U.isOpenEmbedding) ≤
      vanishingIdealSubsheaf I.formalCompletion := by
    refine comap_le_vanishingIdealSubsheaf e.hom
      (fun y => ⟨e.inv.base y, LocallyRingedSpace.iso_inv_base_hom_base_apply e y⟩) ?_
    rw [← restrict_vanishingIdealSubsheaf]
    exact restrict_mono _ h.le_vanishingIdealSubsheaf
  obtain ⟨b, hb, hle⟩ := exists_pow_le I.isIdealOfDefinition_formalCompletionIdealSubsheaf
    (sheafSupport_quotientAb_of_le_vanishingIdealSubsheaf h1)
  refine ⟨b, hb, ?_⟩
  have h2 : J.restrict U.isOpenEmbedding ≤
      comap e.inv (comap e.hom (J.restrict U.isOpenEmbedding)) := by
    rw [← comap_comp, e.hom_inv_id]
    exact le_comap_id _
  calc _ ≤ comap e.inv (comap e.hom (J.restrict U.isOpenEmbedding)) ^ b := pow_le_pow_left h2 b
    _ ≤ comap e.inv (comap e.hom (J.restrict U.isOpenEmbedding) ^ b) := pow_comap_le _ _ b
    _ ≤ comap e.inv I.formalCompletionIdealSubsheaf := comap_mono _ hle

omit [AlgebraicGeometry.IsNoetherian Y] in
include h in
/-- **Completeness on a chart.** Let `e : U ≅ Ŷ` be a chart of `X` onto the completion of a
Noetherian scheme `Y` along `I`, and `G` a coherent `𝒪_Y`-module. Then the transport `e⁻¹_* Ĝ` of
the completion `Ĝ` is complete for `J|_U`: `Ĝ` is complete for `ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})`, the
pushforward along the isomorphism carries this to completeness for the inverse image ideal, and
that ideal and `J|_U` have mutually cofinal powers. -/
theorem isIso_toLimitPowQuotient_chart [IsNoetherian Y] (G : Y.Modules) (hG : IsCoherent G) :
    IsIso ((J.restrict U.isOpenEmbedding).toLimitPowQuotient
      (pushforwardModule e.inv (I.moduleCompletion' G))) := by
  have : G.IsQuasicoherent := hG.isQuasicoherent
  have h1 : IsIso (I.formalCompletionIdealSubsheaf.toLimitPowQuotient (I.moduleCompletion' G)) :=
    I.isIso_toLimitPowQuotient_moduleCompletion G
  have h2 : IsIso ((comap e.inv I.formalCompletionIdealSubsheaf).toLimitPowQuotient
      (pushforwardModule e.inv (I.moduleCompletion' G))) :=
    @isIso_toLimitPowQuotient_pushforward _ I.formalCompletion I.formalCompletionIdealSubsheaf
      (I.moduleCompletion' G) e h1
  obtain ⟨a, ha, hab⟩ := h.exists_pow_comap_le_restrict e
  obtain ⟨b, hb, hba⟩ := h.exists_pow_restrict_le_comap e
  refine (isIso_toLimitPowQuotient_iff_of_cofinal (fun n => ?_) (fun n => ?_)).mp h2
  · obtain ⟨k, hk⟩ := exists_pow_succ_le_pow_succ ha hab n
    exact ⟨k, smulSubmodule_mono _ hk⟩
  · obtain ⟨k, hk⟩ := exists_pow_succ_le_pow_succ hb hba n
    exact ⟨k, smulSubmodule_mono _ hk⟩

end IsIdealOfDefinition

/-- **A coherent formal module is complete** (Hartshorne II.9, Proposition 9.6(a), the
isomorphism `F ≅ lim F / J ^ (n + 1) F`). For an ideal of definition `J` of a Noetherian formal
scheme `X` and a coherent `𝒪_X`-module `F`, the canonical map `F ⟶ lim_n F / J ^ (n + 1) F` is an
isomorphism: completeness is local, and on each chart of `F` it holds by
`IsIdealOfDefinition.isIso_toLimitPowQuotient_chart`. -/
theorem IsIdealOfDefinition.isIso_toLimitPowQuotient {X : NoetherianFormalScheme.{u}}
    {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf} (h : IsIdealOfDefinition X J)
    {F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)}
    (hF : IsCoherentFormalModule F) : IsIso (J.toLimitPowQuotient F) := by
  obtain ⟨ι, -, U, hU, hchart⟩ := hF
  refine J.isIso_toLimitPowQuotient_of_iSup_eq_top F U hU fun i => ?_
  obtain ⟨Y, hY, I, e, G, hG, ⟨ψ⟩⟩ := hchart i
  have := h.isIso_toLimitPowQuotient_chart e G hG
  exact (J.restrict (U i).isOpenEmbedding).isIso_toLimitPowQuotient_of_iso ψ.symm

end Hartshorne
