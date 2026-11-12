/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.InverseSystemMittagLefflerExact
import Hartshorne.Scheme.AffineGlobalSectionsExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# First Čech cocycles, inverse limits and lifting of global sections

Let `T` be a topological space and `U = (Uᵢ)` a family of opens of `T`. A *Čech 1-cocycle* of a
presheaf of abelian groups `P` on `U` is a family `cᵢⱼ ∈ P(Uᵢ ∩ Uⱼ)` with
`cᵢⱼ + cⱼₖ = cᵢₖ` on `Uᵢ ∩ Uⱼ ∩ Uₖ`; it is a coboundary when `cᵢⱼ = aᵢ - aⱼ` for sections
`aᵢ ∈ P(Uᵢ)`. `Hartshorne.CechOneVanishes P U` says that every 1-cocycle is a coboundary.

* `Hartshorne.CechOneVanishes.of_iso`: the condition only depends on `P` up to isomorphism.
* `Hartshorne.cechOneVanishes_of_isLimit`: let `P = lim_n Qₙ` be a sequential inverse limit of
  sheaves of abelian groups, computed on sections, and let `U` cover `T`. If every `Qₙ`
  satisfies the condition on `U` and the transition maps `Γ(T, Qₙ₊₁) ⟶ Γ(T, Qₙ)` are surjective,
  then `P` satisfies the condition on `U`. This combines the levelwise exact sequences
  `0 ⟶ Γ(T, Qₙ) ⟶ ∏ᵢ Qₙ(Uᵢ) ⟶ Z¹(U, Qₙ) ⟶ 0` with Hartshorne II, Proposition 9.1(b)
  (`Hartshorne.InverseSystem.inverseLimit_exact_of_isMittagLeffler`).
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace Hartshorne

universe u

section Presheaf

variable {T : TopCat.{u}} (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- Restriction `P(V) ⟶ P(W)` of a presheaf of abelian groups along `W ≤ V`, as an additive map. -/
abbrev presheafRes {V W : Opens T} (h : W ≤ V) : P.obj (op V) →+ P.obj (op W) :=
  (P.map (homOfLE h).op).hom

variable {P} in
lemma presheafRes_res {V W W' : Opens T} (h : W ≤ V) (h' : W' ≤ W) (s : P.obj (op V)) :
    presheafRes P h' (presheafRes P h s) = presheafRes P (h'.trans h) s := by
  change (P.map (homOfLE h).op ≫ P.map (homOfLE h').op) s = _
  rw [← P.map_comp]
  rfl

variable {P} in
lemma presheafRes_self {V : Opens T} (h : V ≤ V) (s : P.obj (op V)) : presheafRes P h s = s := by
  change P.map (𝟙 (op V)) s = s
  rw [P.map_id]
  rfl

variable {P} in
lemma presheafRes_naturality {P' : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P')
    {V W : Opens T} (h : W ≤ V) (s : P.obj (op V)) :
    φ.app (op W) (presheafRes P h s) = presheafRes P' h (φ.app (op V) s) := by
  change (P.map (homOfLE h).op ≫ φ.app (op W)) s = (φ.app (op V) ≫ P'.map (homOfLE h).op) s
  rw [φ.naturality]

lemma inf_inf_le_left' {U₁ U₂ U₃ : Opens T} : U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ ⊓ U₂ := inf_le_left

lemma inf_inf_le_mid {U₁ U₂ U₃ : Opens T} : U₁ ⊓ U₂ ⊓ U₃ ≤ U₂ ⊓ U₃ :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

lemma inf_inf_le_outer {U₁ U₂ U₃ : Opens T} : U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ ⊓ U₃ :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

/-- A family `cᵢⱼ ∈ P(Uᵢ ∩ Uⱼ)` is a **Čech 1-cocycle** on `U` when `cᵢⱼ + cⱼₖ = cᵢₖ` on every
triple intersection `Uᵢ ∩ Uⱼ ∩ Uₖ`. -/
def IsCechOneCocycle {ι : Type*} (U : ι → Opens T) (c : ∀ i j, P.obj (op (U i ⊓ U j))) : Prop :=
  ∀ i j k, presheafRes P inf_inf_le_left' (c i j) + presheafRes P inf_inf_le_mid (c j k) =
    presheafRes P (inf_inf_le_outer (U₂ := U j)) (c i k)

/-- **Vanishing of first Čech cohomology on a family of opens** `U`: every Čech 1-cocycle
`cᵢⱼ ∈ P(Uᵢ ∩ Uⱼ)` is a coboundary, `cᵢⱼ = aᵢ - aⱼ` on `Uᵢ ∩ Uⱼ` for sections `aᵢ ∈ P(Uᵢ)`. -/
def CechOneVanishes {ι : Type*} (U : ι → Opens T) : Prop :=
  ∀ c : ∀ i j, P.obj (op (U i ⊓ U j)), IsCechOneCocycle P U c →
    ∃ a : ∀ i, P.obj (op (U i)), ∀ i j,
      c i j = presheafRes P inf_le_left (a i) - presheafRes P inf_le_right (a j)

variable {P}

/-- Vanishing of first Čech cohomology on `U` transports along an isomorphism of presheaves. -/
theorem CechOneVanishes.of_iso {P' : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}} (e : P ≅ P')
    {ι : Type*} {U : ι → Opens T} (h : CechOneVanishes P U) : CechOneVanishes P' U := by
  intro c hc
  obtain ⟨a, ha⟩ := h (fun i j => e.inv.app _ (c i j)) fun i j k => by
    simp only [← presheafRes_naturality, ← map_add, hc i j k]
  refine ⟨fun i => e.hom.app _ (a i), fun i j => ?_⟩
  have := congrArg (e.hom.app _) (ha i j)
  rw [map_sub, presheafRes_naturality, presheafRes_naturality] at this
  rw [← this]
  change c i j = (e.inv.app _ ≫ e.hom.app _) (c i j)
  rw [Iso.inv_hom_id_app]
  rfl

/-- On the cover `U`, the cocycle condition forces `cᵢᵢ = 0`. -/
lemma IsCechOneCocycle.self_eq_zero {ι : Type*} {U : ι → Opens T}
    {c : ∀ i j, P.obj (op (U i ⊓ U j))} (hc : IsCechOneCocycle P U c) (i : ι) : c i i = 0 := by
  have h := hc i i i
  have h1 : U i ⊓ U i ≤ U i ⊓ U i ⊓ U i := le_inf le_rfl inf_le_left
  have := congrArg (presheafRes P h1) h
  simp only [map_add, presheafRes_res, presheafRes_self] at this
  simpa using this

end Presheaf

section Levelwise

variable {T : TopCat.{u}} {ι : Type} (U : ι → Opens T)

/-- The `0`-cochains `∏ᵢ F(Uᵢ)` of a sheaf of abelian groups on the family `U`, as a functor. -/
@[simps! obj]
def cechZeroFunctor : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj F := AddCommGrpCat.of (∀ i, F.obj.obj (op (U i)))
  map φ := AddCommGrpCat.ofHom
    (AddMonoidHom.pi fun i => (φ.hom.app (op (U i))).hom.comp (Pi.evalAddMonoidHom _ i))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The Čech `1`-cocycles of a sheaf of abelian groups on `U`, as an additive subgroup of the
`1`-cochains. -/
def cechOneCocycles (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
    AddSubgroup (∀ i j, F.obj.obj (op (U i ⊓ U j))) where
  carrier := {c | IsCechOneCocycle F.obj U c}
  add_mem' {c d} hc hd i j k := by
    simp only [Pi.add_apply, map_add]
    rw [← hc i j k, ← hd i j k]
    abel
  zero_mem' i j k := by simp
  neg_mem' {c} hc i j k := by
    simp only [Pi.neg_apply, map_neg]
    rw [← hc i j k]
    abel

/-- The Čech `1`-cocycles on `U`, as a functor. -/
@[simps! obj]
def cechOneFunctor : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj F := AddCommGrpCat.of (cechOneCocycles U F)
  map {F G} φ := AddCommGrpCat.ofHom
    { toFun := fun c => ⟨fun i j => φ.hom.app _ (c.1 i j), fun i j k => by
        rw [← presheafRes_naturality, ← presheafRes_naturality, ← presheafRes_naturality,
          ← map_add, c.2 i j k]⟩
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Global sections of sheaves of abelian groups, as a functor. -/
@[simps! obj]
def sheafGlobalSectionsFunctor : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op ⊤)

/-- Restriction of global sections to the `0`-cochains. -/
def cechZeroOfGlobal : sheafGlobalSectionsFunctor (T := T) ⟶ cechZeroFunctor U where
  app F := AddCommGrpCat.ofHom (AddMonoidHom.pi fun i => presheafRes F.obj le_top)
  naturality {F G} φ := by
    ext s
    funext i
    exact (presheafRes_naturality φ.hom le_top s).symm

/-- The Čech differential from `0`-cochains to `1`-cocycles. -/
def cechZeroDiff : cechZeroFunctor U ⟶ cechOneFunctor U where
  app F := AddCommGrpCat.ofHom
    { toFun := fun a => ⟨fun i j => presheafRes F.obj inf_le_left (a i) -
          presheafRes F.obj inf_le_right (a j), fun i j k => by
        simp only [map_sub, presheafRes_res]
        abel⟩
      map_zero' := Subtype.ext (funext fun i => funext fun j => by simp)
      map_add' := fun a b => Subtype.ext (funext fun i => funext fun j => by
        simp only [AddSubgroup.coe_add, Pi.add_apply, map_add]
        abel) }
  naturality {F G} φ := by
    ext a
    apply Subtype.ext
    funext i j
    show presheafRes G.obj inf_le_left (φ.hom.app _ (a i)) -
        presheafRes G.obj inf_le_right (φ.hom.app _ (a j)) =
      φ.hom.app _ (presheafRes F.obj inf_le_left (a i) - presheafRes F.obj inf_le_right (a j))
    rw [map_sub, presheafRes_naturality, presheafRes_naturality]

variable {U}

lemma cechZeroOfGlobal_injective (hU : iSup U = ⊤) (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
    Function.Injective ((cechZeroOfGlobal U).app F) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Sheaf.eq_of_locally_eq' (F := F) U ⊤ (fun i => homOfLE le_top) hU.ge s 0 fun i => ?_
  rw [map_zero]
  exact congrFun hs i

lemma cechZero_exact (hU : iSup U = ⊤) (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
    Function.Exact ((cechZeroOfGlobal U).app F) ((cechZeroDiff U).app F) := by
  intro a
  constructor
  · intro ha
    have hcompat : TopCat.Presheaf.IsCompatible F.obj U a := fun i j => by
      have := congrArg (fun c => c.1 i j) ha
      exact sub_eq_zero.mp this
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := F) U ⊤ (fun i => homOfLE le_top) hU.ge a hcompat
    exact ⟨s, funext hs⟩
  · rintro ⟨s, rfl⟩
    apply Subtype.ext
    funext i j
    exact sub_eq_zero.mpr ((presheafRes_res (P := F.obj) (s := s) le_top inf_le_left).trans
      (presheafRes_res (P := F.obj) (s := s) le_top inf_le_right).symm)

lemma cechZeroDiff_surjective (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (hF : CechOneVanishes F.obj U) : Function.Surjective ((cechZeroDiff U).app F) := by
  rintro ⟨c, hc⟩
  obtain ⟨a, ha⟩ := hF c hc
  exact ⟨a, Subtype.ext (funext fun i => funext fun j => (ha i j).symm)⟩

end Levelwise

section Limit

variable {T : TopCat.{u}} {ι : Type} {U : ι → Opens T}

private lemma surjective_map_of_succ (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (h : ∀ n, Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op)) :
    ∀ ⦃i j : ℕᵒᵖ⦄ (f : i ⟶ j), Function.Surjective (A.map f) := by
  rintro ⟨m⟩ ⟨n⟩ f
  have hnm : n ≤ m := leOfHom f.unop
  induction m, hnm using Nat.le_induction with
  | base =>
    rw [show f = 𝟙 _ from Subsingleton.elim _ _, A.map_id]
    exact Function.surjective_id
  | succ m hnm ih =>
    rw [show f = (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op from Subsingleton.elim _ _,
      A.map_comp]
    exact (ih (homOfLE hnm).op).comp (h m)

/-- **Čech `H¹` of a sequential inverse limit.** Let `c` be a cone over a sequential inverse system
`Q` of sheaves of abelian groups which is a limit on sections (`hext`, `hex`), let `U` cover `T`,
suppose every `Qₙ` has vanishing first Čech cohomology on `U` and the transition maps
`Γ(T, Qₙ₊₁) ⟶ Γ(T, Qₙ)` are surjective. Then `c.pt` has vanishing first Čech cohomology on `U`.
The levelwise sequences `0 ⟶ Γ(T, Qₙ) ⟶ ∏ᵢ Qₙ(Uᵢ) ⟶ Z¹(U, Qₙ) ⟶ 0` are exact, the first
system is Mittag–Leffler, so the sequence of inverse limits is exact (Hartshorne II,
Proposition 9.1(b)). -/
theorem cechOneVanishes_of_isLimit (Q : ℕᵒᵖ ⥤ Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (c : Cone Q)
    (hext : ∀ (V : Opens T) (x y : c.pt.obj.obj (op V)),
      (∀ n, (c.π.app (op n) : c.pt ⟶ Q.obj (op n)).hom.app (op V) x =
        (c.π.app (op n) : c.pt ⟶ Q.obj (op n)).hom.app (op V) y) → x = y)
    (hex : ∀ (V : Opens T) (y : ∀ n, (Q.obj (op n)).obj.obj (op V)),
      (∀ ⦃m n : ℕ⦄ (f : (op m : ℕᵒᵖ) ⟶ op n), (Q.map f).hom.app (op V) (y m) = y n) →
        ∃ x : c.pt.obj.obj (op V), ∀ n,
          (c.π.app (op n) : c.pt ⟶ Q.obj (op n)).hom.app (op V) x = y n)
    (hU : iSup U = ⊤) (hQ : ∀ n, CechOneVanishes (Q.obj (op n)).obj U)
    (hsurj : ∀ n, Function.Surjective
      ((Q.map (homOfLE (Nat.le_succ n)).op).hom.app (op ⊤))) :
    CechOneVanishes c.pt.obj U := by
  intro z hz
  have hML : InverseSystem.IsMittagLeffler (Q ⋙ sheafGlobalSectionsFunctor) :=
    InverseSystem.isMittagLeffler_of_surjective _
      (surjective_map_of_succ (Q ⋙ sheafGlobalSectionsFunctor) hsurj)
  have hlevel := InverseSystem.inverseLimit_exact_of_isMittagLeffler
    (Functor.whiskerLeft Q (cechZeroOfGlobal U)) (Functor.whiskerLeft Q (cechZeroDiff U))
    (fun j => ⟨cechZeroOfGlobal_injective hU _, cechZero_exact hU _,
      cechZeroDiff_surjective _ (hQ j.unop)⟩) hML
  -- the image of `z` in the cocycles of every `Qₙ`
  let zs : (Q ⋙ cechOneFunctor U ⋙ forget AddCommGrpCat).sections :=
    ⟨fun j => (cechOneFunctor U).map (c.π.app j) ⟨z, hz⟩, fun {j j'} f => by
      change ((cechOneFunctor U).map (c.π.app j) ≫ (cechOneFunctor U).map (Q.map f)) _ = _
      rw [← Functor.map_comp, Cone.w]⟩
  obtain ⟨s, hs⟩ := hlevel.2.2 zs
  have hsec : ∀ i, ∃ x : c.pt.obj.obj (op (U i)), ∀ n,
      (c.π.app (op n)).hom.app (op (U i)) x = s.1 (op n) i := fun i =>
    hex (U i) (fun n => s.1 (op n) i) fun m n f => congrFun (s.2 f) i
  choose a ha using hsec
  refine ⟨a, fun i j => hext _ _ _ fun n => ?_⟩
  have h1 := congrArg (fun t => (t.1 (op n)).1 i j) hs
  change presheafRes _ inf_le_left (s.1 (op n) i) - presheafRes _ inf_le_right (s.1 (op n) j) =
    (c.π.app (op n)).hom.app _ (z i j) at h1
  rw [← h1, map_sub, presheafRes_naturality (P := c.pt.obj) (c.π.app (op n)).hom,
    presheafRes_naturality (P := c.pt.obj) (c.π.app (op n)).hom, ha, ha]

end Limit

section Modules

variable {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}

/-- The morphism of underlying presheaves of abelian groups of a morphism of sheaves of
modules. -/
abbrev sheafOfModulesAbMap {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    M.val.presheaf ⟶ N.val.presheaf :=
  (PresheafOfModules.toPresheaf R.obj).map f.val

/-- On every open, the sections of a short exact sequence of sheaves of modules form a left exact
sequence. -/
lemma sheafOfModules_sections_exact {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    (V : Opens T) : Function.Injective ((sheafOfModulesAbMap S.f).app (op V)) ∧
      Function.Exact ((sheafOfModulesAbMap S.f).app (op V))
        ((sheafOfModulesAbMap S.g).app (op V)) := by
  have : Mono S.f := hS.mono_f
  have : (SheafOfModules.evaluation R (op V)).Additive := { map_add := rfl }
  have h := hS.exact.map_of_mono_of_preservesKernel (SheafOfModules.evaluation R (op V))
    inferInstance inferInstance
  refine ⟨(ModuleCat.mono_iff_injective _).mp
    ((SheafOfModules.evaluation R (op V)).map_mono S.f), fun x => ⟨fun hx => ?_, ?_⟩⟩
  · exact (ShortComplex.moduleCat_exact_iff _).mp h x hx
  · rintro ⟨y, rfl⟩
    exact congrArg (fun φ => (SheafOfModules.evaluation R (op V)).map φ y) S.zero

lemma sheafOfModules_limit_ext {K : Type} [SmallCategory K] {F : K ⥤ SheafOfModules.{u} R}
    {c : Cone F} (hc : IsLimit c) (V : Opens T) {x y : c.pt.val.presheaf.obj (op V)}
    (h : ∀ j, (sheafOfModulesAbMap (c.π.app j)).app (op V) x =
      (sheafOfModulesAbMap (c.π.app j)).app (op V) y) : x = y := by
  have hc' := isLimitOfPreserves (SheafOfModules.evaluation R (op V) ⋙ forget _) hc
  exact (Types.isLimitEquivSections hc').injective (Subtype.ext (funext h))

lemma sheafOfModules_limit_exists {K : Type} [SmallCategory K] {F : K ⥤ SheafOfModules.{u} R}
    {c : Cone F} (hc : IsLimit c) (V : Opens T) (y : ∀ j, (F.obj j).val.presheaf.obj (op V))
    (hy : ∀ ⦃j j' : K⦄ (f : j ⟶ j'), (sheafOfModulesAbMap (F.map f)).app (op V) (y j) = y j') :
    ∃ x : c.pt.val.presheaf.obj (op V), ∀ j, (sheafOfModulesAbMap (c.π.app j)).app (op V) x = y j := by
  have hc' := isLimitOfPreserves (SheafOfModules.evaluation R (op V) ⋙ forget _) hc
  refine ⟨(Types.isLimitEquivSections hc').symm ⟨y, fun {j j'} f => hy f⟩, fun j => ?_⟩
  exact Types.isLimitEquivSections_symm_apply hc' _ j

/-- **Lifting global sections along a Čech-acyclic kernel.** Let `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` be a short
exact sequence of sheaves of modules, `U` a cover of `T` and `s` a global section of `F''` which
lifts to `F` on every `Uᵢ`. If every Čech 1-cocycle of `F'` on `U` is a coboundary, then `s`
lifts to a global section of `F`: the differences of the local lifts form a cocycle of `F'`, and
correcting the local lifts by a trivialization makes them glue. -/
theorem sheafOfModules_exists_lift_of_cechOneVanishes {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact) {ι : Type} {U : ι → Opens T} (hU : iSup U = ⊤)
    (hA : CechOneVanishes S.X₁.val.presheaf U) (s : S.X₃.val.presheaf.obj (op ⊤))
    (hs : ∀ i, ∃ t : S.X₂.val.presheaf.obj (op (U i)),
      (sheafOfModulesAbMap S.g).app _ t = presheafRes S.X₃.val.presheaf le_top s) :
    ∃ t, (sheafOfModulesAbMap S.g).app (op ⊤) t = s := by
  choose t ht using hs
  have hex := sheafOfModules_sections_exact hS
  have hgf : ∀ (V : Opens T) (x : S.X₁.val.presheaf.obj (op V)),
      (sheafOfModulesAbMap S.g).app _ ((sheafOfModulesAbMap S.f).app _ x) = 0 :=
    fun V x => ((hex V).2 _).mpr ⟨x, rfl⟩
  have hd : ∀ i j, ∃ c, (sheafOfModulesAbMap S.f).app (op (U i ⊓ U j)) c =
      presheafRes S.X₂.val.presheaf inf_le_left (t i) -
        presheafRes S.X₂.val.presheaf inf_le_right (t j) := by
    intro i j
    refine ((hex _).2 _).mp ?_
    rw [map_sub, presheafRes_naturality, presheafRes_naturality, ht, ht,
      presheafRes_res, presheafRes_res, sub_self]
  choose c hc using hd
  have hcoc : IsCechOneCocycle S.X₁.val.presheaf U c := by
    intro i j k
    refine (hex _).1 ?_
    rw [map_add, presheafRes_naturality, presheafRes_naturality, presheafRes_naturality, hc, hc,
      hc]
    simp only [map_sub, presheafRes_res]
    abel
  obtain ⟨a, ha⟩ := hA c hcoc
  let t' : ∀ i, S.X₂.val.presheaf.obj (op (U i)) :=
    fun i => t i - (sheafOfModulesAbMap S.f).app _ (a i)
  have hcompat : TopCat.Presheaf.IsCompatible ((SheafOfModules.toSheaf R).obj S.X₂).obj U t' := by
    intro i j
    show presheafRes S.X₂.val.presheaf inf_le_left (t' i) =
      presheafRes S.X₂.val.presheaf inf_le_right (t' j)
    rw [← sub_eq_zero]
    simp only [t', map_sub, ← presheafRes_naturality]
    have := congrArg ((sheafOfModulesAbMap S.f).app (op (U i ⊓ U j))) (ha i j)
    rw [hc, map_sub] at this
    convert sub_eq_zero.mpr this using 1
    abel
  obtain ⟨t0, ht0, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := (SheafOfModules.toSheaf R).obj S.X₂)
    U ⊤ (fun i => homOfLE le_top) hU.ge t' hcompat
  refine ⟨t0, TopCat.Sheaf.eq_of_locally_eq' (F := (SheafOfModules.toSheaf R).obj S.X₃) U ⊤
    (fun i => homOfLE le_top) hU.ge _ _ fun i => ?_⟩
  show presheafRes S.X₃.val.presheaf le_top ((sheafOfModulesAbMap S.g).app _ t0) =
    presheafRes _ le_top s
  have := ht0 i
  change presheafRes S.X₂.val.presheaf le_top t0 = t' i at this
  refine (presheafRes_naturality (sheafOfModulesAbMap S.g) le_top t0).symm.trans ?_
  rw [this, map_sub, hgf, sub_zero, ht]

end Modules

section OpenPushforward

variable {T : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u})

/-- The functor `V ↦ V ⊓ W` on the opens of `T`. -/
@[simps]
def opensInfFunctor (W : Opens T) : Opens T ⥤ Opens T where
  obj V := V ⊓ W
  map f := homOfLE (inf_le_inf_right W (leOfHom f))

instance (W : Opens T) : (opensInfFunctor W).IsContinuous (Opens.grothendieckTopology T)
    (Opens.grothendieckTopology T) :=
  haveI := W.isOpenEmbedding.functor_isContinuous
  Functor.isContinuous_comp' (F₁ := Opens.map W.inclusion') (F₂ := W.isOpenEmbedding.functor)
    (NatIso.ofComponents (fun V => eqToIso (by
      rw [Functor.comp_obj, Opens.functor_obj_map_obj W.isOpenEmbedding.isOpenMap,
        Opens.isOpenEmbedding_obj_top, inf_comm]
      rfl)) (fun _ => rfl)) (Opens.grothendieckTopology T)
    (Opens.grothendieckTopology ((Opens.toTopCat T).obj W)) (Opens.grothendieckTopology T)

/-- The restriction maps `R(V) ⟶ R(V ⊓ W)`, as a morphism from `R` to its pushforward along
`V ↦ V ⊓ W`. -/
def opensInfRingHom (W : Opens T) :
    R ⟶ ((opensInfFunctor W).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology T) (Opens.grothendieckTopology T)).obj R :=
  Sheaf.homEquiv.symm
    { app := fun V => R.obj.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op
      naturality := fun V V' f => by
        induction V with | op V => ?_
        induction V' with | op V' => ?_
        exact (R.obj.map_comp f (homOfLE (inf_le_left : V' ⊓ W ≤ V')).op).symm.trans
          (R.obj.map_comp (homOfLE (inf_le_left : V ⊓ W ≤ V)).op
            ((opensInfFunctor W).map f.unop).op) }

/-- The sheaf of modules `V ↦ G(V ⊓ W)` attached to a sheaf of modules `G` and an open `W`, the
direct image of the restriction of `G` to `W`. -/
abbrev opensInfModule (W : Opens T) (G : SheafOfModules.{u} R) : SheafOfModules.{u} R :=
  (SheafOfModules.pushforward (opensInfRingHom R W)).obj G

/-- The restriction maps `G(V) ⟶ G(V ⊓ W)`, a morphism of sheaves of modules. -/
def toOpensInfModule (W : Opens T) (G : SheafOfModules.{u} R) : G ⟶ opensInfModule R W G where
  val :=
    { app := fun V => G.val.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op
      naturality := fun {V V'} f => by
        induction V with | op V => ?_
        induction V' with | op V' => ?_
        ext x
        exact (G.val.map_comp_apply f (homOfLE (inf_le_left : V' ⊓ W ≤ V')).op x).symm.trans
          (G.val.map_comp_apply (homOfLE (inf_le_left : V ⊓ W ≤ V)).op
            ((opensInfFunctor W).map f.unop).op x) }

variable {R}

lemma opensInfModule_res (W : Opens T) (G : SheafOfModules.{u} R) {V V' : Opens T} (h : V' ≤ V)
    (x : G.val.presheaf.obj (op (V ⊓ W))) :
    presheafRes (opensInfModule R W G).val.presheaf h x =
      presheafRes G.val.presheaf (inf_le_inf_right W h) x :=
  rfl

lemma toOpensInfModule_app (W : Opens T) (G : SheafOfModules.{u} R) (V : Opens T)
    (x : G.val.presheaf.obj (op V)) :
    (sheafOfModulesAbMap (toOpensInfModule R W G)).app (op V) x =
      presheafRes G.val.presheaf (inf_le_left : V ⊓ W ≤ V) x :=
  rfl

end OpenPushforward

section CechFromLift

variable {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}

/-- **Čech `H¹` from lifting of global sections.** Let `G` be a sheaf of modules such that for every
monomorphism `G ⟶ P` the global sections of `P` surject onto those of the cokernel `P / G`. Then
on every cover `U` of `T` every Čech 1-cocycle of `G` is a coboundary.

Proof: take `P = ∏ₖ (V ↦ G(V ∩ Uₖ))` with the diagonal restriction `G ⟶ P`. A cocycle `c` gives
local sections `(cₖᵢ)ₖ` of `P` over `Uᵢ` whose classes in `P / G` glue, as on `Uᵢ ∩ Uⱼ` they differ
by the image of `-cᵢⱼ`. A global lift `p = (pₖ)` of the glued section differs over `Uᵢ` from
`(cₖᵢ)ₖ` by the image of some `gᵢ ∈ G(Uᵢ)`; comparing components gives `gᵢ = pᵢ` and
`cₖᵢ = pₖ - pᵢ`. -/
theorem cechOneVanishes_of_surjective_cokernel (G : SheafOfModules.{u} R) {ι : Type}
    (U : ι → Opens T) (hU : iSup U = ⊤)
    (hlift : ∀ (P : SheafOfModules.{u} R) (f : G ⟶ P), Mono f →
      Function.Surjective ((sheafOfModulesAbMap (cokernel.π f)).app (op ⊤))) :
    CechOneVanishes G.val.presheaf U := by
  intro c hc
  let Pk : ι → SheafOfModules.{u} R := fun k => opensInfModule R (U k) G
  let f : G ⟶ ∏ᶜ Pk := Pi.lift fun k => toOpensInfModule R (U k) G
  have hcomp : ∀ k (V : Opens T) (x : G.val.presheaf.obj (op V)),
      (sheafOfModulesAbMap (Pi.π Pk k)).app (op V) ((sheafOfModulesAbMap f).app (op V) x) =
        presheafRes G.val.presheaf (inf_le_left : V ⊓ U k ≤ V) x := by
    intro k V x
    change (sheafOfModulesAbMap (f ≫ Pi.π Pk k)).app (op V) x = _
    rw [Pi.lift_π]
    rfl
  have hlim := limit.isLimit (Discrete.functor Pk)
  have hext : ∀ (V : Opens T) (x y : (∏ᶜ Pk).val.presheaf.obj (op V)),
      (∀ k, (sheafOfModulesAbMap (Pi.π Pk k)).app (op V) x =
        (sheafOfModulesAbMap (Pi.π Pk k)).app (op V) y) → x = y :=
    fun V x y h => sheafOfModules_limit_ext hlim V fun ⟨k⟩ => h k
  have hexi : ∀ (V : Opens T) (y : ∀ k, (Pk k).val.presheaf.obj (op V)),
      ∃ x : (∏ᶜ Pk).val.presheaf.obj (op V),
        ∀ k, (sheafOfModulesAbMap (Pi.π Pk k)).app (op V) x = y k := by
    intro V y
    obtain ⟨x, hx⟩ := sheafOfModules_limit_exists hlim V (fun j => y j.as) (by
      rintro ⟨j⟩ ⟨j'⟩ g
      obtain rfl : j = j' := Discrete.eq_of_hom g
      rw [show g = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
      rfl)
    exact ⟨x, fun k => hx ⟨k⟩⟩
  -- `f` is a monomorphism
  have hinj : ∀ V : Opens T, Function.Injective ((sheafOfModulesAbMap f).app (op V)) := by
    intro V
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine TopCat.Sheaf.eq_of_locally_eq' (F := (SheafOfModules.toSheaf R).obj G)
      (fun k => V ⊓ U k) V (fun k => homOfLE inf_le_left) ?_ x 0 fun k => ?_
    · rw [← inf_iSup_eq, hU, inf_top_eq]
    · show presheafRes G.val.presheaf inf_le_left x = presheafRes G.val.presheaf inf_le_left 0
      rw [map_zero, ← hcomp, hx, map_zero]
      rfl
  have hmono : Mono f := ⟨fun {Z} a b hab => by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    ext z
    exact hinj V.unop (congrArg (fun φ => (sheafOfModulesAbMap φ).app V z) hab)⟩
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
  have hex := sheafOfModules_sections_exact hS
  have hgf : ∀ (V : Opens T) (x : G.val.presheaf.obj (op V)),
      (sheafOfModulesAbMap (cokernel.π f)).app _ ((sheafOfModulesAbMap f).app _ x) = 0 :=
    fun V x => ((hex V).2 _).mpr ⟨x, rfl⟩
  have hc0 := hc.self_eq_zero
  -- the local sections `(cₖᵢ)ₖ` of `P` over `Uᵢ`
  have hx : ∀ i, ∃ x : (∏ᶜ Pk).val.presheaf.obj (op (U i)), ∀ k,
      (sheafOfModulesAbMap (Pi.π Pk k)).app (op (U i)) x =
        presheafRes G.val.presheaf (le_inf inf_le_right inf_le_left : U i ⊓ U k ≤ U k ⊓ U i)
          (c k i) := fun i => hexi (U i) _
  choose x hxk using hx
  -- on `Uᵢ ∩ Uⱼ` the local sections differ by the image of `-cᵢⱼ`
  have hdiff : ∀ i j, presheafRes (∏ᶜ Pk).val.presheaf (inf_le_left : U i ⊓ U j ≤ U i) (x i) -
      presheafRes (∏ᶜ Pk).val.presheaf (inf_le_right : U i ⊓ U j ≤ U j) (x j) =
        (sheafOfModulesAbMap f).app _ (-c i j) := by
    intro i j
    refine hext _ _ _ fun k => ?_
    rw [map_sub, presheafRes_naturality, presheafRes_naturality, hxk, hxk, hcomp,
      opensInfModule_res, opensInfModule_res, presheafRes_res, presheafRes_res, map_neg]
    have h := congrArg (presheafRes G.val.presheaf
      (show U i ⊓ U j ⊓ U k ≤ U k ⊓ U i ⊓ U j from
        le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
          (inf_le_left.trans inf_le_right))) (hc k i j)
    simp only [map_add, presheafRes_res] at h
    rw [← h]
    abel
  let σ : ∀ i, (cokernel f).val.presheaf.obj (op (U i)) :=
    fun i => (sheafOfModulesAbMap (cokernel.π f)).app _ (x i)
  have hcompat : TopCat.Presheaf.IsCompatible ((SheafOfModules.toSheaf R).obj (cokernel f)).obj
      U σ := by
    intro i j
    show presheafRes (cokernel f).val.presheaf inf_le_left (σ i) =
      presheafRes (cokernel f).val.presheaf inf_le_right (σ j)
    rw [← sub_eq_zero]
    simp only [σ, ← presheafRes_naturality, ← map_sub, hdiff, hgf]
  obtain ⟨σ0, hσ0, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (F := (SheafOfModules.toSheaf R).obj (cokernel f)) U ⊤ (fun i => homOfLE le_top) hU.ge σ
    hcompat
  obtain ⟨p, hp⟩ := hlift _ f hmono σ0
  -- over `Uᵢ`, `p - (cₖᵢ)ₖ` comes from `gᵢ ∈ G(Uᵢ)`
  have hg : ∀ i, ∃ g : G.val.presheaf.obj (op (U i)), (sheafOfModulesAbMap f).app _ g =
      presheafRes (∏ᶜ Pk).val.presheaf le_top p - x i := by
    intro i
    refine ((hex _).2 _).mp ?_
    rw [map_sub, presheafRes_naturality, hp]
    exact sub_eq_zero.mpr (hσ0 i)
  choose g hgi using hg
  let a : ∀ k, G.val.presheaf.obj (op (U k)) := fun k =>
    presheafRes G.val.presheaf (le_inf le_top le_rfl : U k ≤ ⊤ ⊓ U k)
      ((sheafOfModulesAbMap (Pi.π Pk k)).app (op ⊤) p)
  -- components of `hgi`
  have hcompk : ∀ i k, presheafRes G.val.presheaf (inf_le_left : U i ⊓ U k ≤ U i) (g i) =
      presheafRes G.val.presheaf (inf_le_right : U i ⊓ U k ≤ U k) (a k) -
        presheafRes G.val.presheaf (le_inf inf_le_right inf_le_left : U i ⊓ U k ≤ U k ⊓ U i)
          (c k i) := by
    intro i k
    have := congrArg ((sheafOfModulesAbMap (Pi.π Pk k)).app (op (U i))) (hgi i)
    rw [hcomp, map_sub, presheafRes_naturality, hxk] at this
    rw [this]
    congr 1
    exact (presheafRes_res (P := G.val.presheaf) _ _ _).symm
  have hga : ∀ i, g i = a i := by
    intro i
    have h := congrArg (presheafRes G.val.presheaf (le_inf le_rfl le_rfl : U i ≤ U i ⊓ U i))
      (hcompk i i)
    simp only [map_sub, presheafRes_res, presheafRes_self, hc0, map_zero, sub_zero] at h
    exact h
  refine ⟨a, fun i j => ?_⟩
  have h := congrArg (presheafRes G.val.presheaf (le_inf inf_le_right inf_le_left :
    U i ⊓ U j ≤ U j ⊓ U i)) (hcompk j i)
  simp only [map_sub, presheafRes_res, presheafRes_self, hga] at h
  rw [h]
  abel

end CechFromLift

end Hartshorne
