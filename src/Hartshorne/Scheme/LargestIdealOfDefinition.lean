/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.IdealOfDefinition

/-!
# The largest ideal of definition

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.5(b) (p. 197).

* `Hartshorne.vanishingIdealSubsheaf X`: for a locally ringed space `X`, the ideal subsheaf of
  `𝒪_X` of sections vanishing at every point, i.e. whose germ at every point `x` lies in the
  maximal ideal of `𝒪_{X,x}`. On a Noetherian formal scheme this is the candidate `J_red`.
* `Hartshorne.IsIdealOfDefinition.le_vanishingIdealSubsheaf`: every ideal of definition `J` is
  contained in `J_red` (only `Supp (𝒪_X / J) = X` is used).
* `Hartshorne.IsIdealOfDefinition.isReduced_quotientScheme_iff`: for an ideal of definition `J`,
  the scheme `(X, 𝒪_X / J)` is reduced if and only if `J = J_red`.
* `Hartshorne.IsIdealOfDefinition.isGreatest_of_isIdealOfDefinition_vanishingIdealSubsheaf`:
  once `J_red` is an ideal of definition, it is the largest one, and it is the only ideal of
  definition with reduced quotient scheme.

Proof outline. If `Supp (𝒪_X / J) = X` then `1 ∉ J` near any point, so no section of `J` has a
unit germ, i.e. `J ⊆ J_red`. On the Noetherian scheme `Y = (X, 𝒪_X / J)`, the image of a section
of `J_red` has non-unit germs everywhere (a unit germ would give `g t - 1 ∈ J ⊆ J_red` near the
point, with `g t ∈ J_red`), hence empty principal open; on a reduced scheme this forces it to be
zero, so `J_red ⊆ J`. Conversely if `J = J_red`, a nilpotent section of `𝒪_X / J` is locally the
image of a section `s` with `s ^ n ∈ J_red`, and since maximal ideals are prime, `s ∈ J_red`.

The remaining part of Proposition 9.5(b), that `J_red` is an ideal of definition (in particular
that ideals of definition exist), is not proved here.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology

namespace Hartshorne

universe u

namespace IdealSubsheaf

variable {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T} (J : IdealSubsheaf R)

/-! The following private lemmas are copied from `Hartshorne.Scheme.IdealsOfDefinitionCofinal`,
where they are private. -/

private lemma quotientπ_hom_eq :
    J.quotientπ.hom = J.quotientPresheafπ ≫ toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap) := by
  rw [toSheafify_naturality]
  rfl

private lemma quotientπ_app_apply (U : Opens T) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op U) s = (toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap)).app (op U)
        (Ideal.Quotient.mk (J.ideal U) s) := by
  rw [quotientπ_hom_eq]
  rfl

/-- The kernel of `R(U) → (R / J)(U)` is `J(U)`. -/
private lemma quotientπ_app_eq_zero_iff (U : Opens T) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op U) s = 0 ↔ s ∈ J.ideal U := by
  constructor
  · intro hs
    rw [quotientπ_app_apply] at hs
    have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology T)
      (toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap)) (X := op U)
        (Ideal.Quotient.mk (J.ideal U) s) 0 (hs.trans (map_zero _).symm)
    refine J.mem_ideal_of_locally s fun x hx => ?_
    obtain ⟨V, f, hf, hxV⟩ := hmem x hx
    refine ⟨V, leOfHom f, hxV, ?_⟩
    have hf' : (idealQuotientPresheaf R J.ideal J.ideal_le_comap).map f.op
        (Ideal.Quotient.mk (J.ideal U) s) =
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap).map f.op 0 := hf
    rw [map_zero] at hf'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hf'
  · intro hs
    rw [quotientπ_app_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hs]
    exact map_zero _

/-- The projection `R ⟶ R / J` is locally surjective. -/
private lemma exists_quotientπ_app_eq (U : Opens T) (t : J.quotient.presheaf.obj (op U)) (x : T)
    (hx : x ∈ U) :
    ∃ (V : Opens T) (hVU : V ≤ U) (s : R.presheaf.obj (op V)), x ∈ V ∧
      J.quotientπ.hom.app (op V) s = J.quotient.presheaf.map (homOfLE hVU).op t := by
  obtain ⟨V, hVU, ⟨q, hq⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff
    (toSheafify (Opens.grothendieckTopology T)
      (idealQuotientPresheaf R J.ideal J.ideal_le_comap))).mp
    (inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) _)) U t x hx
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨V, hVU, s, hxV, by rw [quotientπ_app_apply]; exact hq⟩

/-- The projection `R ⟶ R / J` commutes with restriction. -/
private lemma quotientπ_app_res {U V : Opens T} (h : V ≤ U) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op V) (R.presheaf.map (homOfLE h).op s) =
      J.quotient.presheaf.map (homOfLE h).op (J.quotientπ.hom.app (op U) s) :=
  NatTrans.naturality_apply J.quotientπ.hom _ s

/-- If `1 ∈ J(V)` then `R / J` vanishes near every point of `V`. -/
private lemma notMem_sheafSupport_of_one_mem {V : Opens T} {x : T} (hx : x ∈ V)
    (h1 : (1 : R.presheaf.obj (op V)) ∈ J.ideal V) :
    x ∉ sheafSupport J.quotientAb := by
  intro hsupp
  have hsub : ∀ (W : Opens T) (_ : W ≤ V), Subsingleton (J.quotient.presheaf.obj (op W)) := by
    intro W hWV
    have h0 := (J.quotientπ_app_eq_zero_iff W (R.presheaf.map (homOfLE hWV).op 1)).mpr
      (J.ideal_le_comap hWV h1)
    rw [map_one, map_one] at h0
    exact subsingleton_of_zero_eq_one h0.symm
  obtain ⟨a, b, hab⟩ := hsupp
  apply hab
  obtain ⟨W₁, h₁, hx₁, s₁, rfl⟩ := J.quotientAb.presheaf.exists_le_germ_eq a hx
  obtain ⟨W₂, h₂, hx₂, s₂, rfl⟩ := J.quotientAb.presheaf.exists_le_germ_eq b hx
  have e₁ : s₁ = 0 := @Subsingleton.elim _ (hsub W₁ h₁) _ _
  have e₂ : s₂ = 0 := @Subsingleton.elim _ (hsub W₂ h₂) _ _
  rw [e₁, e₂, map_zero, map_zero]

end IdealSubsheaf

section vanishing

variable (X : LocallyRingedSpace.{u})

/-- The ideal of sections of `𝒪_X(V)` whose germ at every point of `V` lies in the maximal
ideal of the stalk. -/
private def vanishingIdeal (V : Opens X) : Ideal (X.presheaf.obj (op V)) :=
  ⨅ x : V, (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)).comap (X.presheaf.germ V x.1 x.2).hom

variable {X}

private lemma mem_vanishingIdeal {V : Opens X} (s : X.presheaf.obj (op V)) :
    s ∈ vanishingIdeal X V ↔
      ∀ (x : X) (hx : x ∈ V), ¬ IsUnit (X.presheaf.germ V x hx s) := by
  rw [vanishingIdeal, Submodule.mem_iInf]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · have := h ⟨x, hx⟩
    rwa [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
  · rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact h x x.2

variable (X) in
private lemma germ_sheaf_res {U V : Opens X} (h : V ≤ U) (x : X) (hx : x ∈ V)
    (s : X.sheaf.presheaf.obj (op U)) :
    X.presheaf.germ V x hx (X.sheaf.presheaf.map (homOfLE h).op s) =
      X.presheaf.germ U x (h hx) s :=
  X.presheaf.germ_res_apply (homOfLE h) x hx s

variable (X)

/-- **The ideal of sections vanishing at every point** of a locally ringed space `X`: the ideal
subsheaf of `𝒪_X` whose sections over `V` are the `s ∈ 𝒪_X(V)` whose germ at every point
`x ∈ V` lies in the maximal ideal of the local ring `𝒪_{X,x}`. On a Noetherian formal scheme this
is the largest ideal of definition `J_red` of Hartshorne II, Proposition 9.5(b). -/
def vanishingIdealSubsheaf : IdealSubsheaf X.sheaf :=
  IdealSubsheaf.ofIdeals X.sheaf (vanishingIdeal X)
    (fun {V W} h s hs => by
      refine (mem_vanishingIdeal (X := X) _).mpr fun x hx => ?_
      rw [germ_sheaf_res X h x hx s]
      exact (mem_vanishingIdeal (X := X) s).mp hs x (h hx))
    (fun {U} s hs => by
      refine (mem_vanishingIdeal (X := X) s).mpr fun x hx => ?_
      obtain ⟨V, hVU, hxV, hsV⟩ := hs x hx
      have := (mem_vanishingIdeal (X := X) _).mp hsV x hxV
      rwa [germ_sheaf_res X hVU x hxV s] at this)

variable {X}

lemma mem_vanishingIdealSubsheaf_iff {V : Opens X} (s : X.presheaf.obj (op V)) :
    s ∈ (vanishingIdealSubsheaf X).ideal V ↔
      ∀ (x : X) (hx : x ∈ V), ¬ IsUnit (X.presheaf.germ V x hx s) :=
  mem_vanishingIdeal s

/-- **`J_red` has full support**: for any locally ringed space `X`, the support of
`𝒪_X / J_red` is all of `X`, since `1` has a unit germ everywhere and so lies in no `J_red(V)`
with `V` nonempty. -/
theorem sheafSupport_quotientAb_vanishingIdealSubsheaf :
    sheafSupport (vanishingIdealSubsheaf X).quotientAb = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  set J := vanishingIdealSubsheaf X
  let one : J.quotientAb.presheaf.obj (op ⊤) := J.quotientπ.hom.app (op ⊤) 1
  refine ⟨⟨J.quotientAb.presheaf.germ ⊤ x trivial one,
    J.quotientAb.presheaf.germ ⊤ x trivial 0, fun h => ?_⟩⟩
  obtain ⟨V, hxV, iV, iV', hres⟩ :=
    J.quotientAb.presheaf.germ_eq x (U := ⊤) (V := ⊤) trivial trivial _ _ h
  have h0 : J.quotient.presheaf.map (homOfLE (leOfHom iV)).op
      (J.quotientπ.hom.app (op ⊤) 1) = 0 := by
    rw [map_zero] at hres
    exact hres
  rw [← J.quotientπ_app_res, map_one, J.quotientπ_app_eq_zero_iff] at h0
  exact (mem_vanishingIdealSubsheaf_iff (X := X) _).mp h0 x hxV
    ((map_one (X.presheaf.germ V x hxV).hom).symm ▸ isUnit_one)

end vanishing

section openImmersion

/-! ### Charts of `(X, 𝒪_X / J_red)` from reduced schemes

Let `g : W ⟶ X` be a morphism of locally ringed spaces from a reduced scheme `W`. Its structure
map kills `J_red`, so it factors through a morphism of ringed spaces `W ⟶ (X, 𝒪_X / J_red)`
with the same underlying map. When `g` is an open embedding with surjective stalk maps, this
factorization is an open immersion. -/

variable {X : LocallyRingedSpace.{u}} {W : Scheme.{u}} (g : W.toLocallyRingedSpace ⟶ X)

/-- A morphism of locally ringed spaces from a reduced scheme kills `J_red`. -/
private lemma c_app_eq_zero_of_mem_vanishingIdealSubsheaf [IsReduced W] {V : Opens X}
    (s : X.presheaf.obj (op V)) (hs : s ∈ (vanishingIdealSubsheaf X).ideal V) :
    g.c.app (op V) s = 0 := by
  have hb : X.toRingedSpace.basicOpen s = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxV : x ∈ V := X.toRingedSpace.basicOpen_le s hx
    rw [RingedSpace.mem_basicOpen _ s x hxV] at hx
    exact absurd hx ((mem_vanishingIdealSubsheaf_iff (X := X) s).mp hs x hxV)
  have e := LocallyRingedSpace.preimage_basicOpen g s
  rw [hb] at e
  let V' : W.Opens := (Opens.map g.base).obj V
  refine (AlgebraicGeometry.basicOpen_eq_bot_iff (X := W) (U := V') (g.c.app (op V) s)).mp ?_
  exact e.symm

private lemma isSheaf_pushforward :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (g.base _* W.presheaf) :=
  TopCat.Sheaf.pushforward_sheaf_of_sheaf g.base W.IsSheaf

variable [IsReduced W]

/-- The map of presheaves `𝒪_X(V) ⧸ J_red(V) → 𝒪_W(g⁻¹ V)` induced by `g`. -/
private def quotientPresheafLift :
    idealQuotientPresheaf X.sheaf (vanishingIdealSubsheaf X).ideal
        (vanishingIdealSubsheaf X).ideal_le_comap ⟶ g.base _* W.presheaf where
  app V := CommRingCat.ofHom (Ideal.Quotient.lift ((vanishingIdealSubsheaf X).ideal V.unop)
    (g.c.app V).hom (fun s hs => c_app_eq_zero_of_mem_vanishingIdealSubsheaf g s hs))
  naturality V V' i := by
    ext x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective
      (x : X.sheaf.presheaf.obj V ⧸ (vanishingIdealSubsheaf X).ideal V.unop)
    exact NatTrans.naturality_apply g.c i s

/-- The map of sheaves of rings `𝒪_X / J_red ⟶ g_* 𝒪_W` induced by `g`. -/
private def quotientLift :
    (vanishingIdealSubsheaf X).quotient.presheaf ⟶ g.base _* W.presheaf :=
  sheafifyLift (Opens.grothendieckTopology X) (quotientPresheafLift g) (isSheaf_pushforward g)

private lemma quotientLift_app_quotientπ {V : Opens X} (s : X.sheaf.presheaf.obj (op V)) :
    (quotientLift g).app (op V) ((vanishingIdealSubsheaf X).quotientπ.hom.app (op V) s) =
      g.c.app (op V) s := by
  rw [IdealSubsheaf.quotientπ_app_apply]
  change (toSheafify (Opens.grothendieckTopology X) _ ≫ quotientLift g).app (op V)
    (Ideal.Quotient.mk _ s) = _
  rw [quotientLift, toSheafify_sheafifyLift]
  rfl

/-- The morphism of ringed spaces `W ⟶ (X, 𝒪_X / J_red)` through which `g` factors. -/
private def toQuotient :
    W.toSheafedSpace ⟶ (vanishingIdealSubsheaf X).quotientSheafedSpace :=
  InducedCategory.homMk { base := g.base, c := quotientLift g }

private lemma toQuotient_stalkMap_germ (w : W) (V : Opens X) (hw : g.base w ∈ V)
    (s : X.sheaf.presheaf.obj (op V)) :
    (toQuotient g).hom.stalkMap w ((vanishingIdealSubsheaf X).quotient.presheaf.germ V
        (g.base w) hw ((vanishingIdealSubsheaf X).quotientπ.hom.app (op V) s)) =
      g.stalkMap w (X.presheaf.germ V (g.base w) hw s) := by
  refine (PresheafedSpace.stalkMap_germ_apply (toQuotient g).hom V w hw _).trans ?_
  refine Eq.trans ?_ (LocallyRingedSpace.stalkMap_germ_apply g V w hw s).symm
  exact congrArg _ (quotientLift_app_quotientπ g s)

/-- If `g` is an open embedding with surjective stalk maps, its factorization through
`(X, 𝒪_X / J_red)` is an open immersion. -/
private lemma isOpenImmersion_toQuotient (hg : IsOpenEmbedding g.base)
    (hsurj : ∀ w, Function.Surjective (g.stalkMap w)) :
    SheafedSpace.IsOpenImmersion (toQuotient g) := by
  set J := vanishingIdealSubsheaf X
  have hiso : ∀ w, IsIso ((toQuotient g).hom.stalkMap w) := by
    intro w
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · refine (injective_iff_map_eq_zero ((toQuotient g).hom.stalkMap w).hom).mpr fun a ha => ?_
      obtain ⟨V, hw, t, rfl⟩ := J.quotient.presheaf.exists_germ_eq a
      revert ha
      change ∀ _ : (toQuotient g).hom.stalkMap w (J.quotient.presheaf.germ V (g.base w) hw t) = 0,
        J.quotient.presheaf.germ V (g.base w) hw t = 0
      intro ha
      obtain ⟨V', hV'V, s, hwV', hs⟩ := J.exists_quotientπ_app_eq V t (g.base w) hw
      rw [← J.quotient.presheaf.germ_res_apply (homOfLE hV'V) (g.base w) hwV', ← hs] at ha ⊢
      have ha' := (LocallyRingedSpace.stalkMap_germ_apply g V' w hwV' s).symm.trans
        ((toQuotient_stalkMap_germ g w V' hwV' s).symm.trans ha)
      obtain ⟨N, hwN, iN, iN', hN⟩ := W.presheaf.germ_eq (U := (Opens.map g.base).obj V')
        (V := (Opens.map g.base).obj V') w hwV' hwV' _ 0
        (ha'.trans (map_zero _).symm)
      rw [map_zero] at hN
      let V'' : Opens X := ⟨g.base '' (N : Set W), hg.isOpenMap _ N.2⟩
      have hV''V' : V'' ≤ V' := by
        rintro _ ⟨n, hn, rfl⟩
        exact leOfHom iN hn
      have hwV'' : g.base w ∈ V'' := ⟨w, hwN, rfl⟩
      have hmem : X.sheaf.presheaf.map (homOfLE hV''V').op s ∈ J.ideal V'' := by
        refine (mem_vanishingIdealSubsheaf_iff (X := X) _).mpr ?_
        intro y hy hu
        rw [germ_sheaf_res X hV''V' y hy s] at hu
        obtain ⟨n, hnN, rfl⟩ : ∃ n ∈ (N : Set W), g.base n = y := hy
        have hu' := hu.map (g.stalkMap n).hom
        change IsUnit (g.stalkMap n (X.presheaf.germ V' (g.base n) _ s)) at hu'
        rw [LocallyRingedSpace.stalkMap_germ_apply g V' n _ s,
          ← W.presheaf.germ_res_apply iN n hnN, hN, map_zero] at hu'
        exact not_isUnit_zero hu'
      rw [← J.quotient.presheaf.germ_res_apply (homOfLE hV''V') (g.base w) hwV'',
        ← J.quotientπ_app_res, (J.quotientπ_app_eq_zero_iff _ _).mpr hmem, map_zero]
    · intro b
      obtain ⟨a, rfl⟩ := hsurj w b
      obtain ⟨V, hw, s, rfl⟩ := X.presheaf.exists_germ_eq a
      exact ⟨_, toQuotient_stalkMap_germ g w V hw s⟩
  exact SheafedSpace.IsOpenImmersion.of_stalk_iso (toQuotient g) hg

end openImmersion

section scheme

/-! ### `(X, 𝒪_X / J_red)` as a Noetherian scheme from reduced Noetherian affine charts -/

variable (X : LocallyRingedSpace.{u})
  (h : ∀ x : X, ∃ (R : CommRingCat.{u}) (_ : IsNoetherianRing R) (_ : _root_.IsReduced R)
    (g : (Spec R).toLocallyRingedSpace ⟶ X), IsOpenEmbedding g.base ∧
      (∀ w, Function.Surjective (g.stalkMap w)) ∧ x ∈ Set.range g.base)

include h in
private lemma isLocalRing_stalk_quotient (x : X) :
    IsLocalRing ((vanishingIdealSubsheaf X).quotient.presheaf.stalk x) := by
  obtain ⟨R, -, hR, g, hg, hs, w, rfl⟩ := h x
  have := isOpenImmersion_toQuotient g hg hs
  set φ := (toQuotient g).hom.stalkMap w
  have : IsIso φ := SheafedSpace.IsOpenImmersion.stalk_iso (toQuotient g) w
  have hφ : Function.Surjective φ := (ConcreteCategory.bijective_of_isIso φ).2
  have : Nontrivial ((vanishingIdealSubsheaf X).quotient.presheaf.stalk (g.base w)) :=
    hφ.nontrivial
  exact IsLocalRing.of_surjective' (inv φ).hom fun y => ⟨φ y, by
    change (φ ≫ inv φ) y = y
    rw [IsIso.hom_inv_id]
    rfl⟩

/-- The locally ringed space `(X, 𝒪_X / J_red)`, when `X` has reduced Noetherian affine charts. -/
private def quotientLRS : LocallyRingedSpace.{u} where
  toSheafedSpace := (vanishingIdealSubsheaf X).quotientSheafedSpace
  isLocalRing := isLocalRing_stalk_quotient X h

/-- A chart `Spec R ⟶ (X, 𝒪_X / J_red)` as a morphism of locally ringed spaces. -/
private def chartLRSHom {R : CommRingCat.{u}} [_root_.IsReduced R]
    (g : (Spec R).toLocallyRingedSpace ⟶ X) (hg : IsOpenEmbedding g.base)
    (hs : ∀ w, Function.Surjective (g.stalkMap w)) :
    Spec.toLocallyRingedSpace.obj (op R) ⟶ quotientLRS X h :=
  haveI := isOpenImmersion_toQuotient g hg hs
  ⟨(toQuotient g).hom, fun w => @isLocalHom_of_isIso _ _ ((toQuotient g).hom.stalkMap w)
    (SheafedSpace.IsOpenImmersion.stalk_iso (toQuotient g) w)⟩

private lemma isOpenImmersion_chartLRSHom {R : CommRingCat.{u}} [_root_.IsReduced R]
    (g : (Spec R).toLocallyRingedSpace ⟶ X) (hg : IsOpenEmbedding g.base)
    (hs : ∀ w, Function.Surjective (g.stalkMap w)) :
    LocallyRingedSpace.IsOpenImmersion (chartLRSHom X h g hg hs) :=
  isOpenImmersion_toQuotient g hg hs

/-- The scheme `(X, 𝒪_X / J_red)`, when `X` has reduced Noetherian affine charts. -/
private def quotientSchemeOfCharts : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme (quotientLRS X h) fun x => by
    obtain ⟨R, -, hR, g, hg, hs, w, rfl⟩ := h x
    exact ⟨R, chartLRSHom X h g hg hs, ⟨w, rfl⟩, isOpenImmersion_chartLRSHom X h g hg hs⟩

private lemma isNoetherian_quotientSchemeOfCharts [CompactSpace X] :
    IsNoetherian (quotientSchemeOfCharts X h) := by
  have h' := h
  choose R hRN hRr g hg hs hx using h'
  let f : ∀ x, Spec (R x) ⟶ quotientSchemeOfCharts X h := fun x =>
    Scheme.Hom.mk (chartLRSHom X h (g x) (hg x) (hs x))
  have hf : ∀ x, IsOpenImmersion (f x) := fun x =>
    isOpenImmersion_chartLRSHom X h (g x) (hg x) (hs x)
  have hl : IsLocallyNoetherian (quotientSchemeOfCharts X h) := by
    refine isLocallyNoetherian_of_affine_cover
      (S := fun x => ⟨(f x).opensRange, isAffineOpen_opensRange _⟩) ?_ ?_
    · rw [eq_top_iff]
      intro y _
      exact Opens.mem_iSup.mpr ⟨y, hx y⟩
    · intro x
      exact isNoetherianRing_of_ringEquiv _
        ((Scheme.ΓSpecIso (R x)).symm ≪≫ IsOpenImmersion.ΓIsoTop (f x)).commRingCatIsoToRingEquiv
  exact { toIsLocallyNoetherian := hl, toCompactSpace := ‹CompactSpace X› }

include h in
/-- If `X` is quasi-compact and has reduced Noetherian affine charts, then `(X, 𝒪_X / J_red)` is
a Noetherian scheme. -/
private lemma exists_isNoetherian_iso_quotientSheafedSpace [CompactSpace X] :
    ∃ (Y : Scheme.{u}) (_ : IsNoetherian Y),
      Nonempty (Y.toSheafedSpace ≅ (vanishingIdealSubsheaf X).quotientSheafedSpace) :=
  ⟨quotientSchemeOfCharts X h, isNoetherian_quotientSchemeOfCharts X h, ⟨Iso.refl _⟩⟩

end scheme

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}}

/-- A section of an ideal subsheaf `J` with `x ∈ Supp (𝒪_X / J)` has a non-unit germ at `x`.
Copied from the private lemma of the same name in `Hartshorne.Scheme.IdealsOfDefinitionCofinal`. -/
private lemma not_isUnit_germ_of_mem_ideal (J : IdealSubsheaf X.toLocallyRingedSpace.sheaf)
    {x : X.toLocallyRingedSpace} (hsupp : x ∈ sheafSupport J.quotientAb)
    {V : Opens X.toLocallyRingedSpace} (hx : x ∈ V)
    {g : X.toLocallyRingedSpace.sheaf.presheaf.obj (op V)}
    (hg : g ∈ J.ideal V) :
    ¬ IsUnit (X.toLocallyRingedSpace.sheaf.presheaf.germ V x hx g) := by
  intro hu
  obtain ⟨W, i, hxW, hW⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ V g x hx hu
  obtain ⟨v, hv⟩ := hW.exists_right_inv
  have hv' : X.toLocallyRingedSpace.sheaf.presheaf.map i.op g *
      (show X.toLocallyRingedSpace.sheaf.presheaf.obj (op W) from v) = 1 := hv
  have key := Ideal.mul_mem_right (show X.toLocallyRingedSpace.sheaf.presheaf.obj (op W) from v)
    _ (J.ideal_le_comap (leOfHom i) hg)
  rw [show (homOfLE (leOfHom i)).op = i.op from rfl, hv'] at key
  exact J.notMem_sheafSupport_of_one_mem hxW key hsupp

/-- An ideal subsheaf `J` of `𝒪_X` with `Supp (𝒪_X / J) = X` is contained in `J_red`. -/
lemma le_vanishingIdealSubsheaf_of_support_eq_univ
    {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf} (hJ : sheafSupport J.quotientAb = Set.univ) :
    J ≤ vanishingIdealSubsheaf X.toLocallyRingedSpace := by
  rw [IdealSubsheaf.le_iff]
  intro V s hs
  exact (mem_vanishingIdealSubsheaf_iff (X := X.toLocallyRingedSpace) s).mpr fun x hx =>
    not_isUnit_germ_of_mem_ideal J (hJ ▸ Set.mem_univ x) hx hs

/-- Every ideal of definition `J` of a Noetherian formal scheme `X` is contained in `J_red`
(part of Hartshorne II, Proposition 9.5(b), p. 197). -/
theorem le_vanishingIdealSubsheaf {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
    (h : IsIdealOfDefinition X J) : J ≤ vanishingIdealSubsheaf X.toLocallyRingedSpace :=
  le_vanishingIdealSubsheaf_of_support_eq_univ h.support_eq_univ

variable {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}

/-- On the scheme `(X, 𝒪_X / J)` of an ideal of definition `J`, the image of a section of `J_red`
has non-unit germs. -/
private lemma not_isUnit_germ_quotientπ (h : IsIdealOfDefinition X J)
    {V : Opens X.toLocallyRingedSpace}
    {g : X.toLocallyRingedSpace.sheaf.presheaf.obj (op V)}
    (hg : g ∈ (vanishingIdealSubsheaf X.toLocallyRingedSpace).ideal V)
    (x : X.toLocallyRingedSpace) (hx : x ∈ V) :
    ¬ IsUnit (h.quotientScheme.presheaf.germ V x hx (J.quotientπ.hom.app (op V) g)) := by
  intro hu
  obtain ⟨W, hWV, hxW, hW⟩ : ∃ (W : Opens X.toLocallyRingedSpace) (hWV : W ≤ V), x ∈ W ∧
      IsUnit (J.quotient.presheaf.map (homOfLE hWV).op (J.quotientπ.hom.app (op V) g)) := by
    obtain ⟨W, i, hxW, hW⟩ :=
      h.quotientScheme.toRingedSpace.isUnit_res_of_isUnit_germ V _ x hx hu
    exact ⟨W, leOfHom i, hxW, hW⟩
  obtain ⟨t, ht⟩ : ∃ t : J.quotient.presheaf.obj (op W),
      J.quotient.presheaf.map (homOfLE hWV).op (J.quotientπ.hom.app (op V) g) * t = 1 :=
    hW.exists_right_inv
  obtain ⟨W', hW'W, t', hxW', ht'⟩ := J.exists_quotientπ_app_eq W t x hxW
  set g' := X.toLocallyRingedSpace.sheaf.presheaf.map (homOfLE hW'W).op
    (X.toLocallyRingedSpace.sheaf.presheaf.map (homOfLE hWV).op g) with hg'
  have hj : g' * t' - 1 ∈ J.ideal W' := by
    rw [← J.quotientπ_app_eq_zero_iff, map_sub, map_mul, map_one, ht', hg',
      J.quotientπ_app_res, J.quotientπ_app_res, sub_eq_zero, ← map_mul, ht, map_one]
  have hj' := not_isUnit_germ_of_mem_ideal J (h.support_eq_univ ▸ Set.mem_univ x) hxW' hj
  have hgt : g' * t' ∈ (vanishingIdealSubsheaf X.toLocallyRingedSpace).ideal W' :=
    Ideal.mul_mem_right _ _ ((vanishingIdealSubsheaf X.toLocallyRingedSpace).ideal_le_comap hW'W
      ((vanishingIdealSubsheaf X.toLocallyRingedSpace).ideal_le_comap hWV hg))
  refine (mem_vanishingIdealSubsheaf_iff _).mp hgt x hxW' ?_
  have : IsLocalRing (X.toLocallyRingedSpace.sheaf.presheaf.stalk x) :=
    inferInstanceAs (IsLocalRing (X.presheaf.stalk x))
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
      (X.toLocallyRingedSpace.sheaf.presheaf.germ W' x hxW' (g' * t')) with
    h | h
  · exact h
  · refine absurd ?_ hj'
    rw [map_sub, map_one, ← neg_sub]
    exact h.neg

/-- **Reducedness characterizes `J_red`** (part of Hartshorne II, Proposition 9.5(b), p. 197).
For an ideal of definition `J` of a Noetherian formal scheme `X`, the scheme `(X, 𝒪_X / J)` is
reduced if and only if `J` is the ideal `J_red` of sections vanishing at every point. -/
theorem isReduced_quotientScheme_iff (h : IsIdealOfDefinition X J) :
    IsReduced h.quotientScheme ↔ J = vanishingIdealSubsheaf X.toLocallyRingedSpace := by
  constructor
  · intro hred
    refine le_antisymm h.le_vanishingIdealSubsheaf ?_
    rw [IdealSubsheaf.le_iff]
    intro V s hs
    rw [← J.quotientπ_app_eq_zero_iff]
    set Y := h.quotientScheme
    let V' : Y.Opens := V
    let f : Γ(Y, V') := J.quotientπ.hom.app (op V) s
    refine (AlgebraicGeometry.basicOpen_eq_bot_iff f).mp ?_
    rw [eq_bot_iff]
    intro y hy
    have hyV : y ∈ V' := Y.basicOpen_le _ hy
    rw [Scheme.mem_basicOpen Y f y hyV] at hy
    exact absurd hy (not_isUnit_germ_quotientπ h hs y hyV)
  · intro hJ
    refine ⟨fun U => ⟨fun t ht => ?_⟩⟩
    obtain ⟨n, hn⟩ := ht
    change J.quotient.presheaf.obj (op U) at t
    replace hn : t ^ n = 0 := hn
    refine TopCat.Presheaf.section_ext J.quotient U t 0 fun x hx => ?_
    obtain ⟨V, hVU, s, hxV, hs⟩ := J.exists_quotientπ_app_eq U t x hx
    rw [map_zero, ← J.quotient.presheaf.germ_res_apply (homOfLE hVU) x hxV, ← hs]
    suffices hs0 : J.quotientπ.hom.app (op V) s = 0 by rw [hs0, map_zero]
    have hpow : s ^ n ∈ J.ideal V := by
      rw [← J.quotientπ_app_eq_zero_iff, map_pow, hs, ← map_pow]
      change J.quotient.presheaf.map (homOfLE hVU).op (t ^ n) = 0
      rw [hn, map_zero]
    rw [hJ] at hpow
    rw [J.quotientπ_app_eq_zero_iff, hJ]
    refine (mem_vanishingIdealSubsheaf_iff (X := X.toLocallyRingedSpace) s).mpr fun y hy hu => ?_
    refine (mem_vanishingIdealSubsheaf_iff (X := X.toLocallyRingedSpace) _).mp hpow y hy ?_
    exact (map_pow (X.presheaf.germ V y hy).hom s n).symm ▸ hu.pow n

/-- **The largest ideal of definition, assuming `J_red` is one** (part of Hartshorne II,
Proposition 9.5(b), p. 197). If `J_red` is an ideal of definition of the Noetherian formal scheme
`X`, then it is the largest ideal of definition, and an ideal of definition `J` has reduced
quotient scheme `(X, 𝒪_X / J)` if and only if `J = J_red`. -/
theorem isGreatest_of_isIdealOfDefinition_vanishingIdealSubsheaf
    (hred : IsIdealOfDefinition X (vanishingIdealSubsheaf X.toLocallyRingedSpace)) :
    IsGreatest {J | IsIdealOfDefinition X J} (vanishingIdealSubsheaf X.toLocallyRingedSpace) ∧
      ∀ (J : IdealSubsheaf X.toLocallyRingedSpace.sheaf) (h : IsIdealOfDefinition X J),
        IsReduced h.quotientScheme ↔ J = vanishingIdealSubsheaf X.toLocallyRingedSpace :=
  ⟨⟨hred, fun _ h => h.le_vanishingIdealSubsheaf⟩, fun _ h => h.isReduced_quotientScheme_iff⟩

end IsIdealOfDefinition

end Hartshorne
