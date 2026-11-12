/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModule
import Hartshorne.Scheme.PowersOfIdealOfDefinition

/-!
# Reconstruction of a coherent formal module from its infinitesimal reductions

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.6(a) (pp. 197–198): the constructions.

Let `(T, R)` be a ringed space, `J` an ideal subsheaf of `R` and `M` an `R`-module.

* `Hartshorne.IdealSubsheaf.smul J M`: the submodule sheaf `J M ⊆ M`, the sections lying, near
  every point, in `J(V) M(V)`; this is the image of `J ⊗ M ⟶ M`.
  `IdealSubsheaf.smulModules J M` is `J M` as an `R`-module and `IdealSubsheaf.smulι J M` its
  inclusion into `M`; `IdealSubsheaf.smul_mono` says `J ⊆ J'` gives `J M ⊆ J' M`.
* `Hartshorne.IdealSubsheaf.powQuotient J M n`: the `R`-module `M / J ^ (n + 1) M`, the cokernel
  of `J ^ (n + 1) M ⟶ M`, with the projection `IdealSubsheaf.powQuotientπ J M n`, the
  transition maps `IdealSubsheaf.powQuotientMap J M n : M / J ^ (n + 2) M ⟶ M / J ^ (n + 1) M`,
  the inverse system `IdealSubsheaf.powQuotientDiagram J M` and the canonical map
  `IdealSubsheaf.toLimitPowQuotient J M : M ⟶ lim_n M / J ^ (n + 1) M`.

For an ideal of definition `J` of a Noetherian formal scheme `X` (`h : IsIdealOfDefinition X J`)
and an `𝒪_X`-module `F`:

* `Hartshorne.IsIdealOfDefinition.quotientRingCatSheafHom h`: the projection `𝒪_X ⟶ 𝒪_X / J`
  onto the structure sheaf of the scheme `(X, 𝒪_X / J)` (`IsIdealOfDefinition.quotientScheme`),
  along which modules on that scheme are pushed forward to `𝒪_X`-modules
  (`IsIdealOfDefinition.quotientPushforward h`) and `𝒪_X`-modules are pulled back
  (`IsIdealOfDefinition.quotientPullback h`).
* `Hartshorne.IsIdealOfDefinition.reduction h F n`: Hartshorne's `F_n = F / J ^ (n + 1) F` as a
  module on the scheme `(X, 𝒪_X / J ^ (n + 1))`, the pullback of the `𝒪_X`-module
  `F / J ^ (n + 1) F` along `𝒪_X ⟶ 𝒪_X / J ^ (n + 1)` (the scheme exists by Proposition 9.5(c),
  `IsIdealOfDefinition.pow_succ`). As `F / J ^ (n + 1) F` is killed by `J ^ (n + 1)`, its
  pushforward back to `X` is `F / J ^ (n + 1) F` again (the identification is not formalized
  here).
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

/-- A family of submodules of a sheaf of modules on a topological space which is stable under
restriction and local defines a sheaf. (Copied from `Hartshorne.Scheme.IdealOfDefinition`, where it
is private.) -/
private theorem isSheaf_submodule_of_local'' {T : TopCat.{u}}
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

namespace IdealSubsheaf

variable {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T} (J : IdealSubsheaf R)
  (M : SheafOfModules.{u} (ringCatSheafOf R))

/-- The submodule `J(V) M(V)` of the sections of `M` over `V`. -/
def sectionsSmul (V : Opens T) :
    Submodule ((ringCatSheafOf R).obj.obj (op V)) (M.val.obj (op V)) :=
  (show Ideal ((ringCatSheafOf R).obj.obj (op V)) from J.ideal V) • ⊤

/-- Restriction of sections of `M` along `W ≤ V`, as a semilinear map. -/
private abbrev res {V W : Opens T} (h : W ≤ V) :
    M.val.obj (op V) →ₛₗ[((ringCatSheafOf R).obj.map (homOfLE h).op).hom] M.val.obj (op W) :=
  M.val.restrictₛₗ (homOfLE h).op

private lemma res_res {V W W' : Opens T} (h : W ≤ V) (h' : W' ≤ W) (s : M.val.obj (op V)) :
    res M h' (res M h s) = res M (h'.trans h) s :=
  (M.val.map_comp_apply (homOfLE h).op (homOfLE h').op s).symm

private lemma res_refl {V : Opens T} (s : M.val.obj (op V)) : res M (le_refl V) s = s := by
  change M.val.map (𝟙 (op V)) s = s
  rw [M.val.map_id]
  rfl

/-- Restriction maps `J(V) M(V)` into `J(W) M(W)`. -/
lemma map_mem_sectionsSmul {V W : Opens T} (h : W ≤ V) {s : M.val.obj (op V)}
    (hs : s ∈ J.sectionsSmul M V) : M.val.restrictₛₗ (homOfLE h).op s ∈ J.sectionsSmul M W := by
  refine Submodule.smul_induction_on hs (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem_smul (J.ideal_le_comap h hr) trivial
  · rw [map_add]
    exact add_mem hx hy

/-- **The submodule sheaf `J M`** of an `R`-module `M`, for an ideal subsheaf `J` of `R`: the
sections lying, near every point, in `J(V) M(V)`. It is the image of `J ⊗ M ⟶ M`. -/
def smul : M.val.Submodule where
  obj V :=
    { carrier := {s | ∀ x ∈ V.unop, ∃ (W : Opens T) (h : W ≤ V.unop), x ∈ W ∧
        res M h s ∈ J.sectionsSmul M W}
      zero_mem' := fun x hx => ⟨V.unop, le_rfl, hx, by rw [map_zero]; exact zero_mem _⟩
      add_mem' := by
        intro s t hs ht x hx
        obtain ⟨W₁, h₁, hx₁, hs₁⟩ := hs x hx
        obtain ⟨W₂, h₂, hx₂, ht₂⟩ := ht x hx
        refine ⟨W₁ ⊓ W₂, inf_le_left.trans h₁, ⟨hx₁, hx₂⟩, ?_⟩
        rw [map_add]
        refine add_mem ?_ ?_
        · rw [← res_res M h₁ inf_le_left]
          exact J.map_mem_sectionsSmul M _ hs₁
        · rw [show inf_le_left.trans h₁ = (inf_le_right : W₁ ⊓ W₂ ≤ W₂).trans h₂ from rfl,
            ← res_res M h₂ inf_le_right]
          exact J.map_mem_sectionsSmul M _ ht₂
      smul_mem' := by
        intro r s hs x hx
        obtain ⟨W, h, hxW, hsW⟩ := hs x hx
        refine ⟨W, h, hxW, ?_⟩
        rw [LinearMap.map_smulₛₗ]
        exact Submodule.smul_mem _ _ hsW }
  map {V V'} f := by
    intro s hs x hx
    obtain ⟨W, h, hxW, hsW⟩ := hs x (leOfHom f.unop hx)
    refine ⟨V'.unop ⊓ W, inf_le_left, ⟨hx, hxW⟩, ?_⟩
    have key : res M (inf_le_left : V'.unop ⊓ W ≤ V'.unop) (M.val.restrictₛₗ f s) =
        res M (inf_le_right : V'.unop ⊓ W ≤ W) (res M h s) :=
      ((M.val.map_comp_apply f (homOfLE (inf_le_left : V'.unop ⊓ W ≤ V'.unop)).op s).symm.trans
        (M.val.map_comp_apply (homOfLE h).op (homOfLE (inf_le_right : V'.unop ⊓ W ≤ W)).op s) :)
    change res M (inf_le_left : V'.unop ⊓ W ≤ V'.unop) (M.val.restrictₛₗ f s) ∈ _
    rw [key]
    exact J.map_mem_sectionsSmul M _ hsW

lemma mem_smul_iff (V : Opens T) (s : M.val.obj (op V)) :
    s ∈ (J.smul M).obj (op V) ↔ ∀ x ∈ V, ∃ (W : Opens T) (h : W ≤ V), x ∈ W ∧
      M.val.restrictₛₗ (homOfLE h).op s ∈ J.sectionsSmul M W :=
  Iff.rfl

/-- `J(V) M(V) ⊆ (J M)(V)`. -/
lemma sectionsSmul_le_smul (V : Opens T) : J.sectionsSmul M V ≤ (J.smul M).obj (op V) := by
  intro s hs x hx
  refine ⟨V, le_rfl, hx, ?_⟩
  rw [res_refl]
  exact hs

/-- The sections of `J M` are local. -/
lemma smul_isLocal (U : Opens T) (s : M.val.obj (op U))
    (hs : ∀ x ∈ U, ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧
      M.val.map (homOfLE hVU).op s ∈ (J.smul M).obj (op V)) :
    s ∈ (J.smul M).obj (op U) := by
  intro x hx
  obtain ⟨V, hVU, hxV, hsV⟩ := hs x hx
  obtain ⟨W, hWV, hxW, hsW⟩ := hsV x hxV
  refine ⟨W, hWV.trans hVU, hxW, ?_⟩
  rw [← res_res M hVU hWV]
  exact hsW

/-- If `J ⊆ J'` then `J M ⊆ J' M`. -/
lemma smul_mono {J J' : IdealSubsheaf R} (hJ : J ≤ J') : J.smul M ≤ J'.smul M := by
  intro V s hs x hx
  obtain ⟨W, h, hxW, hsW⟩ := hs x hx
  refine ⟨W, h, hxW, Submodule.smul_mono_left ?_ hsW⟩
  exact (le_iff.mp hJ) W

/-- The submodule sheaf `J M`, as an `R`-module. -/
def smulModules : SheafOfModules.{u} (ringCatSheafOf R) :=
  ⟨(J.smul M).toPresheafOfModules, isSheaf_submodule_of_local'' (J.smul M) (J.smul_isLocal M)⟩

/-- The inclusion `J M ⟶ M`. -/
def smulι : J.smulModules M ⟶ M :=
  ⟨(J.smul M).ι⟩

/-- For `J M ⊆ J' M`, the inclusion `J M ⟶ J' M`. -/
def smulInclusion {J J' : IdealSubsheaf R} (hJ : J.smul M ≤ J'.smul M) :
    J.smulModules M ⟶ J'.smulModules M :=
  ⟨PresheafOfModules.Submodule.homOfLE hJ⟩

@[reassoc (attr := simp)]
lemma smulInclusion_smulι {J J' : IdealSubsheaf R} (hJ : J.smul M ≤ J'.smul M) :
    smulInclusion M hJ ≫ J'.smulι M = J.smulι M :=
  SheafOfModules.Hom.ext (PresheafOfModules.Submodule.homOfLE_ι _)

/-- **The quotient `M / J ^ (n + 1) M`**: the cokernel of the inclusion `J ^ (n + 1) M ⟶ M`. -/
def powQuotient (n : ℕ) : SheafOfModules.{u} (ringCatSheafOf R) :=
  cokernel ((J ^ (n + 1)).smulι M)

/-- The projection `M ⟶ M / J ^ (n + 1) M`. -/
def powQuotientπ (n : ℕ) : M ⟶ J.powQuotient M n :=
  cokernel.π _

/-- The transition map `M / J ^ (n + 2) M ⟶ M / J ^ (n + 1) M`, induced by the identity of `M`
since `J ^ (n + 2) M ⊆ J ^ (n + 1) M`. -/
def powQuotientMap (n : ℕ) : J.powQuotient M (n + 1) ⟶ J.powQuotient M n :=
  cokernel.desc _ (J.powQuotientπ M n)
    ((smulInclusion_smulι_assoc M (smul_mono M (J.pow_le_pow_right (Nat.le_succ (n + 1)))) _).symm.trans
      ((congrArg (smulInclusion M _ ≫ ·) (cokernel.condition _)).trans comp_zero))

@[reassoc (attr := simp)]
lemma powQuotientπ_powQuotientMap (n : ℕ) :
    J.powQuotientπ M (n + 1) ≫ J.powQuotientMap M n = J.powQuotientπ M n :=
  cokernel.π_desc _ _ _

/-- **The inverse system** `n ↦ M / J ^ (n + 1) M` of `R`-modules. -/
def powQuotientDiagram : ℕᵒᵖ ⥤ SheafOfModules.{u} (ringCatSheafOf R) :=
  Functor.ofOpSequence (J.powQuotientMap M)

/-- The cone over the inverse system `n ↦ M / J ^ (n + 1) M` with vertex `M`, given by the
projections. -/
def powQuotientCone : Cone (J.powQuotientDiagram M) where
  pt := M
  π := NatTrans.ofOpSequence (fun n => J.powQuotientπ M n) (fun n => by
    rw [show (J.powQuotientDiagram M).map (homOfLE (n.le_add_right 1)).op = J.powQuotientMap M n
      from Functor.ofOpSequence_map_homOfLE_succ _ n]
    exact (Category.id_comp _).trans (J.powQuotientπ_powQuotientMap M n).symm)

/-- **The canonical map** `M ⟶ lim_n M / J ^ (n + 1) M`. -/
def toLimitPowQuotient : M ⟶ limit (J.powQuotientDiagram M) :=
  limit.lift _ (J.powQuotientCone M)

@[reassoc (attr := simp)]
lemma toLimitPowQuotient_π (n : ℕ) :
    J.toLimitPowQuotient M ≫ limit.π (J.powQuotientDiagram M) (op n) = J.powQuotientπ M n :=
  limit.lift_π _ _

/-! ### Cofinal systems of ideals have the same completion -/

section Cofinal

variable {J' J'' : IdealSubsheaf R}

/-- For `J ^ (k + 1) M ⊆ J' ^ (n + 1) M`, the map `M / J ^ (k + 1) M ⟶ M / J' ^ (n + 1) M` induced
by the identity of `M`. -/
def powQuotientDesc {k n : ℕ} (hkn : (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M) :
    J.powQuotient M k ⟶ J'.powQuotient M n :=
  cokernel.desc _ (J'.powQuotientπ M n)
    ((smulInclusion_smulι_assoc M hkn _).symm.trans
      ((congrArg (smulInclusion M hkn ≫ ·) (cokernel.condition _)).trans comp_zero))

@[reassoc (attr := simp)]
lemma powQuotientπ_powQuotientDesc {k n : ℕ}
    (hkn : (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M) :
    J.powQuotientπ M k ≫ J.powQuotientDesc M hkn = J'.powQuotientπ M n :=
  cokernel.π_desc _ _ _

instance (n : ℕ) : Epi (J.powQuotientπ M n) :=
  inferInstanceAs (Epi (cokernel.π _))

lemma powQuotientDesc_self (n : ℕ) : J.powQuotientDesc M (le_refl ((J ^ (n + 1)).smul M)) = 𝟙 _ :=
  (cancel_epi (J.powQuotientπ M n)).mp (by simp)

@[reassoc]
lemma powQuotientDesc_comp {k m n : ℕ} (hkm : (J ^ (k + 1)).smul M ≤ (J' ^ (m + 1)).smul M)
    (hmn : (J' ^ (m + 1)).smul M ≤ (J'' ^ (n + 1)).smul M) :
    J.powQuotientDesc M hkm ≫ J'.powQuotientDesc M hmn = J.powQuotientDesc M (hkm.trans hmn) :=
  (cancel_epi (J.powQuotientπ M k)).mp (by simp)

lemma powQuotientDiagram_map_eq {k k' : ℕ} (h : k ≤ k') :
    (J.powQuotientDiagram M).map (homOfLE h).op =
      J.powQuotientDesc M (smul_mono M (J.pow_le_pow_right (Nat.succ_le_succ h))) :=
  (cancel_epi (J.powQuotientπ M k')).mp
    (((J.powQuotientCone M).w (homOfLE h).op).trans (J.powQuotientπ_powQuotientDesc M _).symm)

/-- The composite `lim_k M / J ^ (k + 1) M ⟶ M / J ^ (k + 1) M ⟶ M / J' ^ (n + 1) M` does not
depend on `k`. -/
lemma limit_π_powQuotientDesc {k k' n : ℕ} (hkn : (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M)
    (hk'n : (J ^ (k' + 1)).smul M ≤ (J' ^ (n + 1)).smul M) :
    limit.π (J.powQuotientDiagram M) (op k) ≫ J.powQuotientDesc M hkn =
      limit.π (J.powQuotientDiagram M) (op k') ≫ J.powQuotientDesc M hk'n := by
  have key : ∀ {a b : ℕ} (hab : a ≤ b) (ha : (J ^ (a + 1)).smul M ≤ (J' ^ (n + 1)).smul M)
      (hb : (J ^ (b + 1)).smul M ≤ (J' ^ (n + 1)).smul M),
      limit.π (J.powQuotientDiagram M) (op a) ≫ J.powQuotientDesc M ha =
        limit.π (J.powQuotientDiagram M) (op b) ≫ J.powQuotientDesc M hb := by
    intro a b hab ha hb
    exact (congrArg (· ≫ J.powQuotientDesc M ha)
      (limit.w (J.powQuotientDiagram M) (homOfLE hab).op).symm).trans
      ((Category.assoc _ _ _).trans (congrArg (limit.π (J.powQuotientDiagram M) (op b) ≫ ·)
        ((congrArg (· ≫ J.powQuotientDesc M ha) (J.powQuotientDiagram_map_eq M hab)).trans
          (J.powQuotientDesc_comp M _ ha))))
  exact (key (le_max_left k k') hkn
    ((smul_mono M (J.pow_le_pow_right (Nat.succ_le_succ (le_max_left k k')))).trans hkn)).trans
    (key (le_max_right k k') hk'n
      ((smul_mono M (J.pow_le_pow_right (Nat.succ_le_succ (le_max_left k k')))).trans hkn)).symm

variable {J M}

/-- If every `J' ^ (n + 1) M` contains some `J ^ (k + 1) M`, the components
`lim_k M / J ^ (k + 1) M ⟶ M / J' ^ (n + 1) M` of the induced map of limits. -/
def limitPowQuotientMapApp (hJJ' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M)
    (n : ℕ) : limit (J.powQuotientDiagram M) ⟶ J'.powQuotient M n :=
  limit.π (J.powQuotientDiagram M) (op (hJJ' n).choose) ≫ J.powQuotientDesc M (hJJ' n).choose_spec

lemma limitPowQuotientMapApp_eq (hJJ' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M)
    {k n : ℕ} (hkn : (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M) :
    limitPowQuotientMapApp hJJ' n =
      limit.π (J.powQuotientDiagram M) (op k) ≫ J.powQuotientDesc M hkn :=
  J.limit_π_powQuotientDesc M _ _

lemma powQuotientMap_eq_powQuotientDesc (n : ℕ) :
    J.powQuotientMap M n =
      J.powQuotientDesc M (smul_mono M (J.pow_le_pow_right (Nat.le_succ (n + 1)))) :=
  (cancel_epi (J.powQuotientπ M (n + 1))).mp (by simp)

lemma limitPowQuotientMapApp_comp
    (hJJ' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M) (n : ℕ) :
    limitPowQuotientMapApp hJJ' (n + 1) ≫ J'.powQuotientMap M n =
      limitPowQuotientMapApp hJJ' n :=
  (congrArg (limitPowQuotientMapApp hJJ' (n + 1) ≫ ·)
    (powQuotientMap_eq_powQuotientDesc (J := J') (M := M) n)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (limit.π (J.powQuotientDiagram M) (op (hJJ' (n + 1)).choose) ≫ ·)
        (J.powQuotientDesc_comp M _ _)).trans (limitPowQuotientMapApp_eq hJJ' _).symm))

/-- If every `J' ^ (n + 1) M` contains some `J ^ (k + 1) M`, the induced map
`lim_k M / J ^ (k + 1) M ⟶ lim_n M / J' ^ (n + 1) M`. -/
def limitPowQuotientMap (hJJ' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M) :
    limit (J.powQuotientDiagram M) ⟶ limit (J'.powQuotientDiagram M) :=
  limit.lift (J'.powQuotientDiagram M)
    { pt := limit (J.powQuotientDiagram M)
      π := NatTrans.ofOpSequence (G := J'.powQuotientDiagram M) (limitPowQuotientMapApp hJJ')
        (fun n => (Category.id_comp _).trans ((limitPowQuotientMapApp_comp hJJ' n).symm.trans
          (congrArg (limitPowQuotientMapApp hJJ' (n + 1) ≫ ·)
            (Functor.ofOpSequence_map_homOfLE_succ _ n).symm))) }

@[reassoc (attr := simp)]
lemma limitPowQuotientMap_π (hJJ' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M)
    {k n : ℕ} (hkn : (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M) :
    limitPowQuotientMap hJJ' ≫ limit.π (J'.powQuotientDiagram M) (op n) =
      limit.π (J.powQuotientDiagram M) (op k) ≫ J.powQuotientDesc M hkn :=
  (limit.lift_π _ _).trans (limitPowQuotientMapApp_eq hJJ' hkn)

lemma toLimitPowQuotient_limitPowQuotientMap
    (hJJ' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M) :
    J.toLimitPowQuotient M ≫ limitPowQuotientMap hJJ' = J'.toLimitPowQuotient M := by
  refine limit.hom_ext fun ⟨n⟩ => ?_
  obtain ⟨k, hk⟩ := hJJ' n
  simp only [Category.assoc, limitPowQuotientMap_π hJJ' hk, toLimitPowQuotient_π]
  exact (J.toLimitPowQuotient_π_assoc M k _).trans (J.powQuotientπ_powQuotientDesc M hk)

lemma limitPowQuotientMap_comp
    (hJJ' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M)
    (hJ'J'' : ∀ n, ∃ k, (J' ^ (k + 1)).smul M ≤ (J'' ^ (n + 1)).smul M)
    (hJJ'' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J'' ^ (n + 1)).smul M) :
    limitPowQuotientMap hJJ' ≫ limitPowQuotientMap hJ'J'' = limitPowQuotientMap hJJ'' := by
  refine limit.hom_ext fun ⟨n⟩ => ?_
  obtain ⟨m, hm⟩ := hJ'J'' n
  obtain ⟨k, hk⟩ := hJJ' m
  simp only [Category.assoc, limitPowQuotientMap_π hJ'J'' hm,
    limitPowQuotientMap_π hJJ'' (hk.trans hm)]
  exact (limitPowQuotientMap_π_assoc hJJ' hk _).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (J.powQuotientDesc_comp M hk hm)))

lemma limitPowQuotientMap_self (hJJ : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J ^ (n + 1)).smul M) :
    limitPowQuotientMap hJJ = 𝟙 _ := by
  refine limit.hom_ext fun ⟨n⟩ => ?_
  simp only [limitPowQuotientMap_π hJJ (le_refl ((J ^ (n + 1)).smul M)), powQuotientDesc_self,
    Category.id_comp]
  exact Category.comp_id _

/-- **Cofinal systems of ideals have the same completion.** If the systems `J ^ (n + 1) M` and
`J' ^ (n + 1) M` are mutually cofinal, then `lim_n M / J ^ (n + 1) M ≅ lim_n M / J' ^ (n + 1) M`,
compatibly with the canonical maps from `M`. -/
def limitPowQuotientIsoOfCofinal
    (hJJ' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M)
    (hJ'J : ∀ n, ∃ k, (J' ^ (k + 1)).smul M ≤ (J ^ (n + 1)).smul M) :
    limit (J.powQuotientDiagram M) ≅ limit (J'.powQuotientDiagram M) where
  hom := limitPowQuotientMap hJJ'
  inv := limitPowQuotientMap hJ'J
  hom_inv_id :=
    (limitPowQuotientMap_comp hJJ' hJ'J (fun n => ⟨n, le_rfl⟩)).trans (limitPowQuotientMap_self _)
  inv_hom_id :=
    (limitPowQuotientMap_comp hJ'J hJJ' (fun n => ⟨n, le_rfl⟩)).trans (limitPowQuotientMap_self _)

/-- If the systems `J ^ (n + 1) M` and `J' ^ (n + 1) M` are mutually cofinal, then
`M ⟶ lim_n M / J ^ (n + 1) M` is an isomorphism iff `M ⟶ lim_n M / J' ^ (n + 1) M` is. -/
theorem isIso_toLimitPowQuotient_iff_of_cofinal
    (hJJ' : ∀ n, ∃ k, (J ^ (k + 1)).smul M ≤ (J' ^ (n + 1)).smul M)
    (hJ'J : ∀ n, ∃ k, (J' ^ (k + 1)).smul M ≤ (J ^ (n + 1)).smul M) :
    IsIso (J.toLimitPowQuotient M) ↔ IsIso (J'.toLimitPowQuotient M) := by
  have e : J.toLimitPowQuotient M ≫ (limitPowQuotientIsoOfCofinal hJJ' hJ'J).hom =
      J'.toLimitPowQuotient M :=
    toLimitPowQuotient_limitPowQuotientMap hJJ'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : IsIso (J.toLimitPowQuotient M ≫ (limitPowQuotientIsoOfCofinal hJJ' hJ'J).hom) :=
      inferInstance
    convert this using 1
    exact e.symm
  · have : IsIso (J.toLimitPowQuotient M ≫ (limitPowQuotientIsoOfCofinal hJJ' hJ'J).hom) := by
      convert h using 1
    exact IsIso.of_isIso_comp_right _ (limitPowQuotientIsoOfCofinal hJJ' hJ'J).hom

end Cofinal

end IdealSubsheaf

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J)

/-- The identity of the underlying space of `X`, from `(X, 𝒪_X / J)` to `X`, induces a continuous
functor on opens. (Instance synthesis does not always find this, since the two underlying spaces
agree only up to unfolding `quotientScheme`; it is then supplied by hand.) -/
instance isContinuous_opensMap_quotientScheme :
    (Opens.map (X := h.quotientScheme.toTopCat) (Y := X.toLocallyRingedSpace.toTopCat)
      (𝟙 _)).IsContinuous (Opens.grothendieckTopology X.toLocallyRingedSpace.carrier)
      (Opens.grothendieckTopology h.quotientScheme.carrier) :=
  inferInstanceAs ((Opens.map (𝟙 X.toLocallyRingedSpace.toTopCat)).IsContinuous
    (Opens.grothendieckTopology X.toLocallyRingedSpace.toTopCat)
    (Opens.grothendieckTopology X.toLocallyRingedSpace.toTopCat))

/-- The projection `𝒪_X ⟶ 𝒪_X / J` of an ideal of definition, onto the structure sheaf of the
scheme `(X, 𝒪_X / J)`, as a morphism of sheaves of rings in `RingCat`. -/
def quotientRingCatSheafHom :
    structureRingCatSheaf X.toLocallyRingedSpace ⟶
      ((Opens.map (X := h.quotientScheme.toTopCat) (Y := X.toLocallyRingedSpace.toTopCat)
        (𝟙 _)).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X.toLocallyRingedSpace.carrier)
        (Opens.grothendieckTopology h.quotientScheme.carrier)).obj h.quotientScheme.ringCatSheaf
    where
  hom := Functor.whiskerRight J.quotientπ.hom (forget₂ CommRingCat RingCat.{u})

/-- The pushforward of modules on the scheme `(X, 𝒪_X / J)` to `𝒪_X`-modules, along
`𝒪_X ⟶ 𝒪_X / J`. -/
def quotientPushforward :
    h.quotientScheme.Modules ⥤ SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace) :=
  letI := h.isContinuous_opensMap_quotientScheme
  SheafOfModules.pushforward.{u} h.quotientRingCatSheafHom

/-- The pushforward along `𝒪_X ⟶ 𝒪_X / J` of presheaves of modules has a left adjoint. -/
lemma isRightAdjoint_presheafPushforward_quotientRingCatSheafHom :
    (PresheafOfModules.pushforward.{u} h.quotientRingCatSheafHom.hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

/-- The pushforward along `𝒪_X ⟶ 𝒪_X / J` of sheaves of modules has a left adjoint. -/
lemma isRightAdjoint_quotientPushforward : h.quotientPushforward.IsRightAdjoint := by
  let := h.isContinuous_opensMap_quotientScheme
  have := h.isRightAdjoint_presheafPushforward_quotientRingCatSheafHom
  exact inferInstanceAs (SheafOfModules.pushforward.{u} h.quotientRingCatSheafHom).IsRightAdjoint

/-- The pullback of `𝒪_X`-modules to modules on the scheme `(X, 𝒪_X / J)`, along
`𝒪_X ⟶ 𝒪_X / J`; it is left adjoint to `quotientPushforward`. -/
def quotientPullback :
    SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace) ⥤ h.quotientScheme.Modules :=
  letI := h.isContinuous_opensMap_quotientScheme
  haveI : (SheafOfModules.pushforward.{u} h.quotientRingCatSheafHom).IsRightAdjoint :=
    h.isRightAdjoint_quotientPushforward
  SheafOfModules.pullback.{u} h.quotientRingCatSheafHom

/-- The adjunction between `quotientPullback` and `quotientPushforward`. -/
def quotientAdjunction : h.quotientPullback ⊣ h.quotientPushforward :=
  letI := h.isContinuous_opensMap_quotientScheme
  haveI : (SheafOfModules.pushforward.{u} h.quotientRingCatSheafHom).IsRightAdjoint :=
    h.isRightAdjoint_quotientPushforward
  SheafOfModules.pullbackPushforwardAdjunction.{u} h.quotientRingCatSheafHom

variable (F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace))

/-- **The reduction `F_n = F / J ^ (n + 1) F`** (Hartshorne II.9, Proposition 9.6(a)), as a module
on the scheme `(X, 𝒪_X / J ^ (n + 1))` of the ideal of definition `J ^ (n + 1)`
(Proposition 9.5(c)): the pullback of the `𝒪_X`-module `F / J ^ (n + 1) F` along
`𝒪_X ⟶ 𝒪_X / J ^ (n + 1)`. -/
def reduction (n : ℕ) : (h.pow_succ n).quotientScheme.Modules :=
  (h.pow_succ n).quotientPullback.obj (J.powQuotient F n)

/-- The map `F / J ^ (n + 1) F ⟶ F_n` of `𝒪_X`-modules, with `F_n` pushed forward to `X`: the
unit of the adjunction. -/
def toReduction (n : ℕ) :
    J.powQuotient F n ⟶ (h.pow_succ n).quotientPushforward.obj (h.reduction F n) :=
  (h.pow_succ n).quotientAdjunction.unit.app (J.powQuotient F n)

end IsIdealOfDefinition

end Hartshorne
