/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.LocallyFiniteSumSheaf
import Hartshorne.Cohomology.ProjectiveLinePartialFractions
import Hartshorne.Scheme.RegularFunctionsSheaf
import Mathlib.Topology.Sheaves.Abelian

/-!
# The principal-parts resolution on `ℙ¹`

Hartshorne, *Algebraic Geometry*, II.1, Exercise 1.21(d,e) (p. 69), adopted for III,
Exercise 2.2 (p. 212).

Let `X = ℙ¹` over an algebraically closed field `k`, `K` its function field and `K_X` the
constant sheaf. There is a short exact sequence of sheaves of abelian groups

`0 → 𝒪_X → K_X → ⨁_{P ∈ X} i_{P,*}(K/𝒪_{X,P}) → 0`,

and the last map is surjective on global sections.

## The objects

* `𝒪_X` is the sheaf of regular functions, regarded as a sheaf of abelian groups.
* `K_X` is the constant sheaf with value `K`: its sections over `U` are the locally constant
  maps `U → K`.
* `𝒪_{X,P}` is the local ring at `P`, viewed inside `K` through its canonical injection.
* The direct sum is `locallyFiniteSumSheaf`: its sections over `U` are the families
  `(a_P)_{P ∈ U}`, `a_P ∈ K/𝒪_{X,P}`, with locally finite support. Since `ℙ¹` is Noetherian it is
  the coproduct of the skyscraper sheaves `i_{P,*}(K/𝒪_{X,P})`
  (`isColimitLocallyFiniteSumCofan`).

## The maps and the proof

The first map sends a regular function on `U` to the constant map with value its class in `K`.
The second sends a locally constant `s : U → K` to the family of classes of `s(P)` modulo
`𝒪_{X,P}`; its support is locally finite because a rational function has only finitely many
poles, the complement of a nonempty open subset of the curve `ℙ¹` being finite.

The first map is injective on every open set: two regular functions on `U` with the same class
in `K` agree on the overlap of their domains, which is `U`. Exactness in the
middle is checked on stalks, from exactness on sections: a nonempty open subset `U` of `ℙ¹` is
irreducible, hence connected, so a section of `K_X` over `U` is a constant `f ∈ K`; if `f` lies in
every `𝒪_{X,P}` with `P ∈ U`, local representatives of `f` glue to a regular function on `U`.
Finally the last map is surjective on every open set, by partial fractions: a finitely supported
family of principal parts is the image of the sum of the corresponding principal parts
(`projectiveLine_exists_principalPart`).

The construction of the first two maps and the exactness at the first two places work for any
variety whose proper closed subsets are finite; only surjectivity uses `ℙ¹`.

## Main results

* `Hartshorne.projectiveLine_principalPartsResolution`
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Hartshorne

universe u

namespace Variety

variable {k : Type u} [Field k] (X : Variety.{u, u} k)

/-- The structure sheaf `𝒪_X`, as a sheaf of abelian groups. -/
def regularAbSheaf : (TopCat.of X.carrier).Sheaf AddCommGrpCat.{u} :=
  (sheafCompose _ (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj X.regularSheaf)

/-- The constant sheaf `K_X` with value the function field. -/
def functionFieldConstantSheaf : (TopCat.of X.carrier).Sheaf AddCommGrpCat.{u} :=
  constantSheaf (TopCat.of X.carrier) (AddCommGrpCat.of X.FunctionField)

/-- The group `K/𝒪_{X,P}` of principal parts at `P`. -/
def principalPartsGroup (P : X.carrier) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (X.FunctionField ⧸ (X.localRingRange P).toSubring.toAddSubgroup)

/-- The sheaf `⨁_{P ∈ X} i_{P,*}(K/𝒪_{X,P})`. -/
def principalPartsSheaf : (TopCat.of X.carrier).Sheaf AddCommGrpCat.{u} :=
  locallyFiniteSumSheaf (X := TopCat.of X.carrier) X.principalPartsGroup

/-- The class in `K` of a regular function on an open set, read off at a point of that set. -/
def regularClass {U : Opens X.carrier} (f : X.regular U) (x : U) : X.FunctionField :=
  Quotient.mk _ ⟨U, ⟨x.1, x.2⟩, f.1, f.2⟩

theorem regularClass_eq {U : Opens X.carrier} (f : X.regular U) (x y : U) :
    X.regularClass f x = X.regularClass f y :=
  rfl

/-- The class of a regular function on `U` lies in the local ring at every point of `U`. -/
theorem regularClass_mem_localRingRange {U : Opens X.carrier} (f : X.regular U) (x : U) :
    X.regularClass f x ∈ X.localRingRange x.1 :=
  ⟨Quotient.mk _ ⟨U, x.2, f.1, f.2⟩, rfl⟩

/-- On sections over `U`, the map `𝒪_X → K_X`. -/
def regularToConstantApp (U : Opens X.carrier) :
    X.regular U →+ LocallyConstant U X.FunctionField where
  toFun f := ⟨X.regularClass f, IsLocallyConstant.of_constant _ (X.regularClass_eq f)⟩
  map_zero' := LocallyConstant.ext fun _ => Quotient.sound fun _ _ _ => rfl
  map_add' _ _ := LocallyConstant.ext fun _ => Quotient.sound fun _ _ _ => rfl

theorem regularToConstantApp_apply {U : Opens X.carrier} (f : X.regular U) (x : U) :
    X.regularToConstantApp U f x = X.regularClass f x :=
  rfl

/-- **The map `𝒪_X → K_X`**: a regular function goes to the constant map with value its class in
the function field. -/
def regularToConstant : X.regularAbSheaf ⟶ X.functionFieldConstantSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (X.regularToConstantApp U.unop)
      naturality := fun _ _ _ => by
        ext f
        apply LocallyConstant.ext
        intro x
        exact Quotient.sound fun _ _ _ => rfl }

/-- The class of a function-field element modulo the local ring at `x`. -/
def principalPart (x : X.carrier) (f : X.FunctionField) : X.principalPartsGroup x :=
  QuotientAddGroup.mk f

theorem principalPart_eq_zero_iff (x : X.carrier) (f : X.FunctionField) :
    X.principalPart x f = 0 ↔ f ∈ X.localRingRange x :=
  QuotientAddGroup.eq_zero_iff f

theorem principalPart_add (x : X.carrier) (f g : X.FunctionField) :
    X.principalPart x (f + g) = X.principalPart x f + X.principalPart x g :=
  rfl

/-- A rational function lies in the local ring at every point of the domain of a
representative. -/
theorem mk_mem_localRingRange (r : RationalRep X) (y : X.carrier) (hy : y ∈ r.U) :
    (Quotient.mk _ r : X.FunctionField) ∈ X.localRingRange y :=
  ⟨Quotient.mk _ ⟨r.U, hy, r.toFun, r.regular⟩, rfl⟩

variable {X}

/-- On a variety whose proper closed subsets are finite, the principal parts of a locally
constant map to the function field have locally finite support. -/
theorem locallyFiniteSupport_principalPart
    (hcof : ∀ Z : Set X.carrier, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    {U : Opens X.carrier} (s : LocallyConstant U X.FunctionField) :
    LocallyFiniteSupport (X := TopCat.of X.carrier) X.principalPartsGroup
      (fun x : U => X.principalPart x.1 (s x)) := by
  intro x
  obtain ⟨r, hr⟩ := Quotient.exists_rep (s x)
  let W : Set U := s ⁻¹' {s x}
  have hW : IsOpen W := s.isLocallyConstant.isOpen_fiber _
  let V : Opens X.carrier := ⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hW⟩
  refine ⟨V, ⟨x, rfl, rfl⟩, ?_⟩
  have hfin : ((r.U : Set X.carrier)ᶜ).Finite := by
    refine hcof _ r.U.isOpen.isClosed_compl ?_
    intro h
    obtain ⟨y, hy⟩ := r.nonempty_U
    have : y ∈ (r.U : Set X.carrier)ᶜ := h ▸ Set.mem_univ y
    exact this hy
  refine (hfin.preimage (f := fun y : U => y.1) Subtype.val_injective.injOn).subset ?_
  rintro y ⟨⟨w, hwW, hwy⟩, hy⟩ hyr
  have hwy' : w = y := Subtype.ext hwy
  subst hwy'
  apply hy
  rw [principalPart_eq_zero_iff]
  have hsw : s w = s x := hwW
  rw [hsw, ← hr]
  exact X.mk_mem_localRingRange r w.1 hyr

/-- **The map `K_X → ⨁_P i_{P,*}(K/𝒪_{X,P})`**: a locally constant map `s : U → K` goes to the
family of principal parts `(s(P) mod 𝒪_{X,P})_{P ∈ U}`. -/
def constantToPrincipalParts
    (hcof : ∀ Z : Set X.carrier, IsClosed Z → Z ≠ Set.univ → Z.Finite) :
    X.functionFieldConstantSheaf ⟶ X.principalPartsSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun s => ⟨fun x : U.unop => X.principalPart x.1 (s x),
            locallyFiniteSupport_principalPart hcof s⟩
          map_zero' := Subtype.ext (funext fun _ => QuotientAddGroup.mk_zero _)
          map_add' := fun _ _ => Subtype.ext (funext fun _ => QuotientAddGroup.mk_add _ _ _) }
      naturality := fun _ _ _ => rfl }

variable (X) in
theorem regularToConstant_comp_constantToPrincipalParts
    (hcof : ∀ Z : Set X.carrier, IsClosed Z → Z ≠ Set.univ → Z.Finite) :
    X.regularToConstant ≫ constantToPrincipalParts hcof = 0 := by
  apply ObjectProperty.hom_ext
  ext U f
  apply Subtype.ext
  funext x
  exact (X.principalPart_eq_zero_iff x.1 _).2
    (X.regularClass_mem_localRingRange (U := U.unop) f x)

variable (X) in
/-- The complex `𝒪_X → K_X → ⨁_P i_{P,*}(K/𝒪_{X,P})`. -/
def principalPartsComplex
    (hcof : ∀ Z : Set X.carrier, IsClosed Z → Z ≠ Set.univ → Z.Finite) :
    ShortComplex ((TopCat.of X.carrier).Sheaf AddCommGrpCat.{u}) :=
  ShortComplex.mk X.regularToConstant (constantToPrincipalParts hcof)
    (X.regularToConstant_comp_constantToPrincipalParts hcof)

/-- **Gluing local representatives.** A rational function lying in the local ring at every
point of an open set `W` is the class of a regular function on `W`. -/
theorem exists_regularClass_eq {W : Opens X.carrier} (f : X.FunctionField)
    (hf : ∀ y : W, f ∈ X.localRingRange y.1) :
    ∃ r : X.regular W, ∀ y : W, X.regularClass r y = f := by
  have hex : ∀ y : W, ∃ g : GermRep X y.1,
      (Quotient.mk _ g.toRationalRep : X.FunctionField) = f := by
    intro y
    obtain ⟨a, ha⟩ := hf y
    obtain ⟨g, rfl⟩ := Quotient.exists_rep a
    exact ⟨g, ha⟩
  choose g hg using hex
  have key : ∀ (y z : W) (hz : z.1 ∈ (g y).U),
      (g y).toFun ⟨z.1, hz⟩ = (g z).toFun ⟨z.1, (g z).mem_U⟩ := by
    intro y z hz
    have hrel : (g y).toRationalRep.Rel (g z).toRationalRep :=
      Quotient.exact ((hg y).trans (hg z).symm)
    exact hrel z.1 hz (g z).mem_U
  let r : W → k := fun z => (g z).toFun ⟨z.1, (g z).mem_U⟩
  have hr : r ∈ X.regular W := by
    apply X.regular_of_locally
    intro y
    refine ⟨(g y).U ⊓ W, inf_le_right, ⟨(g y).mem_U, y.2⟩, ?_⟩
    have heq : (fun z : ((g y).U ⊓ W : Opens X.carrier) => r ⟨z.1, z.2.2⟩) =
        fun z => (g y).toFun ⟨z.1, z.2.1⟩ := by
      funext z
      exact (key y ⟨z.1, z.2.2⟩ z.2.1).symm
    rw [heq]
    exact X.regular_restrict inf_le_left (g y).regular
  refine ⟨⟨r, hr⟩, fun y => ?_⟩
  rw [← hg y]
  exact Quotient.sound fun z hz hz' => (key y ⟨z, hz⟩ hz').symm

/-- **Exactness on sections.** A locally constant map to the function field whose values lie in
the local rings comes from a regular function. -/
theorem exists_regularToConstantApp_eq {W : Opens X.carrier}
    (s : LocallyConstant W X.FunctionField) (hs : ∀ y : W, s y ∈ X.localRingRange y.1) :
    ∃ r : X.regular W, X.regularToConstantApp W r = s := by
  by_cases hW : Nonempty W
  · obtain ⟨y₀⟩ := hW
    have hpre : PreconnectedSpace W :=
      Subtype.preconnectedSpace
        ((PreirreducibleSpace.isPreirreducible_univ (X := X.carrier)).open_subset W.isOpen
          (Set.subset_univ _)).isPreconnected
    have hconst : ∀ y : W, s y = s y₀ := fun y =>
      s.isLocallyConstant.apply_eq_of_preconnectedSpace y y₀
    obtain ⟨r, hr⟩ := exists_regularClass_eq (s y₀) (fun y => hconst y ▸ hs y)
    exact ⟨r, LocallyConstant.ext fun y => (hr y).trans (hconst y).symm⟩
  · exact ⟨0, LocallyConstant.ext fun y => (hW ⟨y⟩).elim⟩

theorem regularToConstantApp_injective (U : Opens X.carrier) :
    Function.Injective (X.regularToConstantApp U) := by
  intro f g h
  apply Subtype.ext
  funext x
  have hx : X.regularClass f x = X.regularClass g x := congrArg (fun s => s x) h
  exact Quotient.exact hx x.1 x.2 x.2

/-- `𝒪_X → K_X` is a monomorphism. -/
theorem mono_regularToConstant : Mono X.regularToConstant := by
  have hU : ∀ U, Mono (X.regularToConstant.hom.app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).2 (X.regularToConstantApp_injective U.unop)
  have : Mono X.regularToConstant.hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- **Exactness at `K_X`**, checked on stalks. -/
theorem principalPartsComplex_exact
    (hcof : ∀ Z : Set X.carrier, IsClosed Z → Z ≠ Set.univ → Z.Finite) :
    (X.principalPartsComplex hcof).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  rw [ShortComplex.ab_exact_iff]
  intro t ht
  obtain ⟨U, hxU, s, rfl⟩ := X.functionFieldConstantSheaf.presheaf.exists_germ_eq t
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (constantToPrincipalParts hcof).hom (X.functionFieldConstantSheaf.presheaf.germ U x hxU s) = 0
    at ht
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ht
  have ht' : X.principalPartsSheaf.presheaf.germ U x hxU
      ((constantToPrincipalParts hcof).hom.app (op U) s) =
      X.principalPartsSheaf.presheaf.germ U x hxU 0 := by
    rw [ht]
    exact (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := X.principalPartsSheaf.presheaf.germ_eq x hxU hxU _ _ ht'
  rw [map_zero] at hW
  let sW : LocallyConstant W X.FunctionField := X.functionFieldConstantSheaf.presheaf.map iU.op s
  have hsW : (constantToPrincipalParts hcof).hom.app (op W) sW = 0 := by
    rw [← hW]
    exact (ConcreteCategory.congr_hom ((constantToPrincipalParts hcof).hom.naturality iU.op) s)
  have hmem : ∀ y : W, sW y ∈ X.localRingRange y.1 := by
    intro y
    have hy := congrFun (congrArg Subtype.val hsW) y
    exact (X.principalPart_eq_zero_iff y.1 _).1 hy
  obtain ⟨r, hr⟩ := exists_regularToConstantApp_eq (W := W) sW hmem
  refine ⟨X.regularAbSheaf.presheaf.germ W x hxW r, ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := X.regularAbSheaf.presheaf)
    (G := X.functionFieldConstantSheaf.presheaf) W x hxW X.regularToConstant.hom r).trans ?_
  change X.functionFieldConstantSheaf.presheaf.germ W x hxW (X.regularToConstantApp W r) = _
  rw [hr]
  exact X.functionFieldConstantSheaf.presheaf.germ_res_apply iU x hxW s

/-- **Surjectivity on sections**, given principal parts: on a Noetherian variety in which every
rational function has, at every point, a principal part regular elsewhere, every finitely
supported family of principal parts over an open set comes from a single rational function. -/
theorem constantToPrincipalParts_app_surjective [NoetherianSpace X.carrier]
    (hcof : ∀ Z : Set X.carrier, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (hpp : ∀ (P : X.carrier) (f : X.FunctionField), ∃ g : X.FunctionField,
      (∀ Q, Q ≠ P → g ∈ X.localRingRange Q) ∧ f - g ∈ X.localRingRange P)
    (U : Opens X.carrier) :
    Function.Surjective ((constantToPrincipalParts hcof).hom.app (op U)) := by
  classical
  intro σ
  let σ' : locallyFiniteSections (X := TopCat.of X.carrier) X.principalPartsGroup U := σ
  let S := locallyFiniteSectionSupport (X := TopCat.of X.carrier) X.principalPartsGroup σ'
  choose f hf using fun y : U => QuotientAddGroup.mk_surjective (σ'.1 y)
  choose g hg using fun y : U => hpp y.1 (f y)
  let F : X.FunctionField := ∑ y ∈ S, g y
  refine ⟨LocallyConstant.const U F, ?_⟩
  apply Subtype.ext
  funext y
  change X.principalPart y.1 F = σ'.1 y
  have hrest : ∀ T : Finset U, y ∉ T → ∑ z ∈ T, g z ∈ X.localRingRange y.1 := by
    intro T hyT
    refine Subalgebra.sum_mem _ fun z hz => (hg z).1 y.1 ?_
    intro h
    apply hyT
    have hzy : z = y := Subtype.ext h.symm
    rwa [← hzy]
  by_cases hy : y ∈ S
  · have hF : F = g y + ∑ z ∈ S.erase y, g z := (Finset.add_sum_erase S g hy).symm
    rw [hF, principalPart_add,
      (X.principalPart_eq_zero_iff y.1 _).2 (hrest _ (Finset.notMem_erase y S)), add_zero,
      ← hf y]
    refine (QuotientAddGroup.eq.2 ?_).symm
    have h : -f y + g y = -(f y - g y) := by abel
    rw [h]
    exact neg_mem (hg y).2
  · have hσ : σ'.1 y = 0 := by
      by_contra h
      exact hy ((mem_locallyFiniteSectionSupport _ σ' y).2 h)
    rw [hσ]
    exact (X.principalPart_eq_zero_iff y.1 _).2 (hrest S hy)

/-- **Epimorphism**, given principal parts on a Noetherian variety. -/
theorem epi_constantToPrincipalParts [NoetherianSpace X.carrier]
    (hcof : ∀ Z : Set X.carrier, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (hpp : ∀ (P : X.carrier) (f : X.FunctionField), ∃ g : X.FunctionField,
      (∀ Q, Q ≠ P → g ∈ X.localRingRange Q) ∧ f - g ∈ X.localRingRange P) :
    Epi (constantToPrincipalParts hcof) := by
  have hU : ∀ U, Epi ((constantToPrincipalParts hcof).hom.app U) := fun U =>
    (AddCommGrpCat.epi_iff_surjective _).2
      (constantToPrincipalParts_app_surjective hcof hpp U.unop)
  have : Epi (constantToPrincipalParts hcof).hom := NatTrans.epi_of_epi_app _
  exact Sheaf.Hom.epi_of_presheaf_epi _ _ _

end Variety

open Variety

/-- **Hartshorne II.1, Exercise 1.21(d,e) (adopted for III, Exercise 2.2).** Let `X = ℙ¹` over an
algebraically closed field `k`, `K` its function field and `K_X` the constant sheaf. Then:

* the sheaf of locally finitely supported families of principal parts is the direct sum
  `⨁_{P ∈ X} i_{P,*}(K/𝒪_{X,P})` of the skyscraper sheaves, with the summand inclusions as
  coprojections;
* `0 → 𝒪_X → K_X → ⨁_{P ∈ X} i_{P,*}(K/𝒪_{X,P}) → 0` is a short exact sequence of sheaves of
  abelian groups;
* the last map is surjective on global sections. -/
theorem projectiveLine_principalPartsResolution (k : Type u) [Field k] [IsAlgClosed k] :
    Nonempty (IsColimit (locallyFiniteSumCofan (X := TopCat.of (projectiveLine k).carrier)
      (projectiveLine k).principalPartsGroup)) ∧
    ((projectiveLine k).principalPartsComplex
      (projectiveLine_finite_of_isClosed (k := k))).ShortExact ∧
    Function.Surjective ((constantToPrincipalParts (X := projectiveLine k)
      (projectiveLine_finite_of_isClosed (k := k))).hom.app (op ⊤)) := by
  have : NoetherianSpace (projectiveLine k).carrier :=
    NoetherianSpace.set (Set.univ : Set (ProjectiveSpace k (Fin 2)))
  have hpp := projectiveLine_exists_principalPart (k := k)
  refine ⟨⟨isColimitLocallyFiniteSumCofan⟩, ?_,
    constantToPrincipalParts_app_surjective _ hpp ⊤⟩
  have hmono := (projectiveLine k).mono_regularToConstant
  have hepi := epi_constantToPrincipalParts (X := projectiveLine k)
    (projectiveLine_finite_of_isClosed (k := k)) hpp
  exact { exact := principalPartsComplex_exact _, mono_f := hmono, epi_g := hepi }

end Hartshorne
