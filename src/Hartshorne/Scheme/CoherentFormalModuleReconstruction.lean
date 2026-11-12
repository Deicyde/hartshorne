/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModule
import Hartshorne.Scheme.PowersOfIdealOfDefinition
import Hartshorne.Scheme.AffineFormalModuleExact

/-!
# Reconstruction of a coherent formal module from its infinitesimal reductions

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.6(a) (pp. 197–198): the constructions.

Let `(T, R)` be a ringed space, `J` an ideal subsheaf of `R` and `M` an `R`-module.

* `Hartshorne.IdealSubsheaf.smulSubmodule J M`: the submodule sheaf `J M ⊆ M`, the sections
  lying, near every point, in `J(V) M(V)`; this is the image of `J ⊗ M ⟶ M`.
  `IdealSubsheaf.smulModules J M` is `J M` as an `R`-module and `IdealSubsheaf.smulι J M` its
  inclusion into `M`; `IdealSubsheaf.smulSubmodule_mono` says `J ⊆ J'` gives `J M ⊆ J' M`.
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
  pushforward back to `X` is `F / J ^ (n + 1) F` again: the unit
  `IsIdealOfDefinition.toReduction h F n` is an isomorphism
  (`IsIdealOfDefinition.isIso_toReduction`).

Modules killed by an ideal subsheaf (`IdealSubsheaf.Annihilates J M`: `J(V) M(V) = 0` for all `V`):

* `Hartshorne.IdealSubsheaf.annihilates_cokernel_smulι`: `J` kills `M / J M`.
* `Hartshorne.IdealSubsheaf.Annihilates.quotientModule`: a module killed by `J` is a module over
  `R / J`, with the same underlying sheaf (`Annihilates.quotientπ_smul`).
* `Hartshorne.IsIdealOfDefinition.isIso_quotientAdjunction_unit_app`: for an `𝒪_X`-module `Q`
  killed by an ideal of definition `J`, the unit `Q ⟶ i_* i^* Q` along `𝒪_X ⟶ 𝒪_X / J` is an
  isomorphism. The pushforward along `𝒪_X ⟶ 𝒪_X / J` is fully faithful, since that map is locally
  surjective, and `Q` is the pushforward of `IsIdealOfDefinition.quotientModule h hQ`.

The chart computation. Let `X` be a locally Noetherian scheme, `I` a quasi-coherent ideal subsheaf,
`X̂` the formal completion along `I`, `J = ker (𝒪_{X̂} ⟶ 𝒪_Y)`
(`QuasicoherentIdealSubsheaf.formalCompletionIdealSubsheaf I`) and `F` a quasi-coherent
`𝒪_X`-module, with completion `F̂ = lim_n (F / I ^ (n + 1) F)|_Y`:

* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionPowShortComplex_exact`: the kernel of
  `F̂ ⟶ (F / I ^ (n + 1) F)|_Y` is `J ^ (n + 1) F̂`; the projection is an epimorphism
  (`epi_moduleCompletionπ'`). Over an affine open `U` of `X` this is
  `mem_sectionsSmul_of_moduleCompletionπ_eq_zero`: a compatible sequence of sections of `F` over
  `U` whose `n`-th term lies in `I(U) ^ (n + 1) Γ(U, F)` is rewritten, using finitely many
  generators `fᵢ` of `I(U) ^ (n + 1)`, as `∑ fᵢ yᵢ` with `yᵢ` sections of `F̂`.
* `Hartshorne.QuasicoherentIdealSubsheaf.powQuotientModuleCompletionIso`:
  `F̂ / J ^ (n + 1) F̂ ≅ (F / I ^ (n + 1) F)|_Y`, compatibly with the transition maps
  (`powQuotientMap_powQuotientModuleCompletionIso_hom`).
* `Hartshorne.QuasicoherentIdealSubsheaf.isIso_toLimitPowQuotient_moduleCompletion`: `F̂` is
  complete for `J`, that is `F̂ ⟶ lim_n F̂ / J ^ (n + 1) F̂` is an isomorphism.
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

/-- If `J ⊆ J'` then `J ^ k ⊆ J' ^ k`. -/
lemma pow_le_pow_left {J J' : IdealSubsheaf R} (h : J ≤ J') (k : ℕ) : J ^ k ≤ J' ^ k := by
  refine le_iff.mpr fun V s hs x hx => ?_
  obtain ⟨W, hWV, hxW, hsW⟩ := hs x hx
  exact ⟨W, hWV, hxW, Ideal.pow_right_mono (le_iff.mp h W) k hsW⟩

/-- `J ^ (a m) ⊆ (J ^ a) ^ m`. -/
lemma pow_mul_le_pow_pow (a m : ℕ) : J ^ (a * m) ≤ (J ^ a) ^ m := by
  refine le_iff.mpr fun V s hs x hx => ?_
  obtain ⟨W, hWV, hxW, hsW⟩ := hs x hx
  refine ⟨W, hWV, hxW, ?_⟩
  have hsW' : R.presheaf.map (homOfLE hWV).op s ∈ (J.ideal W ^ a) ^ m := by
    rw [← pow_mul]
    exact hsW
  exact Ideal.pow_right_mono (J.ideal_pow_le_ideal_pow a W) m hsW'

/-- If `J₂ ^ a ⊆ J₁` with `a > 0`, then every `J₁ ^ (n + 1)` contains some `J₂ ^ (k + 1)`. -/
lemma exists_pow_succ_le_pow_succ {J₁ J₂ : IdealSubsheaf R} {a : ℕ} (ha : 0 < a)
    (h : J₂ ^ a ≤ J₁) (n : ℕ) : ∃ k, J₂ ^ (k + 1) ≤ J₁ ^ (n + 1) := by
  refine ⟨a * (n + 1) - 1, ?_⟩
  rw [Nat.sub_add_cancel (Nat.mul_pos ha n.succ_pos)]
  exact (J₂.pow_mul_le_pow_pow a (n + 1)).trans (pow_le_pow_left h (n + 1))

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
def smulSubmodule : M.val.Submodule where
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

lemma mem_smulSubmodule_iff (V : Opens T) (s : M.val.obj (op V)) :
    s ∈ (J.smulSubmodule M).obj (op V) ↔ ∀ x ∈ V, ∃ (W : Opens T) (h : W ≤ V), x ∈ W ∧
      M.val.restrictₛₗ (homOfLE h).op s ∈ J.sectionsSmul M W :=
  Iff.rfl

/-- `J(V) M(V) ⊆ (J M)(V)`. -/
lemma sectionsSmul_le_smulSubmodule (V : Opens T) :
    J.sectionsSmul M V ≤ (J.smulSubmodule M).obj (op V) := by
  intro s hs x hx
  refine ⟨V, le_rfl, hx, ?_⟩
  rw [res_refl]
  exact hs

/-- The sections of `J M` are local. -/
lemma smulSubmodule_isLocal (U : Opens T) (s : M.val.obj (op U))
    (hs : ∀ x ∈ U, ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧
      M.val.map (homOfLE hVU).op s ∈ (J.smulSubmodule M).obj (op V)) :
    s ∈ (J.smulSubmodule M).obj (op U) := by
  intro x hx
  obtain ⟨V, hVU, hxV, hsV⟩ := hs x hx
  obtain ⟨W, hWV, hxW, hsW⟩ := hsV x hxV
  refine ⟨W, hWV.trans hVU, hxW, ?_⟩
  rw [← res_res M hVU hWV]
  exact hsW

/-- If `J ⊆ J'` then `J M ⊆ J' M`. -/
lemma smulSubmodule_mono {J J' : IdealSubsheaf R} (hJ : J ≤ J') :
    J.smulSubmodule M ≤ J'.smulSubmodule M := by
  intro V s hs x hx
  obtain ⟨W, h, hxW, hsW⟩ := hs x hx
  refine ⟨W, h, hxW, Submodule.smul_mono_left ?_ hsW⟩
  exact (le_iff.mp hJ) W

/-- The submodule sheaf `J M`, as an `R`-module. -/
def smulModules : SheafOfModules.{u} (ringCatSheafOf R) :=
  ⟨(J.smulSubmodule M).toPresheafOfModules,
    isSheaf_submodule_of_local'' (J.smulSubmodule M) (J.smulSubmodule_isLocal M)⟩

/-- The inclusion `J M ⟶ M`. -/
def smulι : J.smulModules M ⟶ M :=
  ⟨(J.smulSubmodule M).ι⟩

/-- For `J M ⊆ J' M`, the inclusion `J M ⟶ J' M`. -/
def smulInclusion {J J' : IdealSubsheaf R} (hJ : J.smulSubmodule M ≤ J'.smulSubmodule M) :
    J.smulModules M ⟶ J'.smulModules M :=
  ⟨PresheafOfModules.Submodule.homOfLE hJ⟩

@[reassoc (attr := simp)]
lemma smulInclusion_smulι {J J' : IdealSubsheaf R} (hJ : J.smulSubmodule M ≤ J'.smulSubmodule M) :
    smulInclusion M hJ ≫ J'.smulι M = J.smulι M :=
  SheafOfModules.Hom.ext (PresheafOfModules.Submodule.homOfLE_ι _)

/-- The submodule sheaf `J ^ (k + 1) M`. -/
abbrev powSubmodule (k : ℕ) : M.val.Submodule :=
  (J ^ (k + 1)).smulSubmodule M

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
    ((smulInclusion_smulι_assoc M
      (smulSubmodule_mono M (J.pow_le_pow_right (Nat.le_succ (n + 1)))) _).symm.trans
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
def powQuotientDesc {k n : ℕ} (hkn : J.powSubmodule M k ≤ J'.powSubmodule M n) :
    J.powQuotient M k ⟶ J'.powQuotient M n :=
  cokernel.desc _ (J'.powQuotientπ M n)
    ((smulInclusion_smulι_assoc M hkn _).symm.trans
      ((congrArg (smulInclusion M hkn ≫ ·) (cokernel.condition _)).trans comp_zero))

@[reassoc (attr := simp)]
lemma powQuotientπ_powQuotientDesc {k n : ℕ}
    (hkn : J.powSubmodule M k ≤ J'.powSubmodule M n) :
    J.powQuotientπ M k ≫ J.powQuotientDesc M hkn = J'.powQuotientπ M n :=
  cokernel.π_desc _ _ _

instance (n : ℕ) : Epi (J.powQuotientπ M n) :=
  inferInstanceAs (Epi (cokernel.π _))

lemma powQuotientDesc_self (n : ℕ) : J.powQuotientDesc M (le_refl (J.powSubmodule M n)) = 𝟙 _ :=
  (cancel_epi (J.powQuotientπ M n)).mp (by simp)

@[reassoc]
lemma powQuotientDesc_comp {k m n : ℕ} (hkm : J.powSubmodule M k ≤ J'.powSubmodule M m)
    (hmn : J'.powSubmodule M m ≤ J''.powSubmodule M n) :
    J.powQuotientDesc M hkm ≫ J'.powQuotientDesc M hmn = J.powQuotientDesc M (hkm.trans hmn) :=
  (cancel_epi (J.powQuotientπ M k)).mp (by simp)

lemma powQuotientDiagram_map_eq {k k' : ℕ} (h : k ≤ k') :
    (J.powQuotientDiagram M).map (homOfLE h).op =
      J.powQuotientDesc M (smulSubmodule_mono M (J.pow_le_pow_right (Nat.succ_le_succ h))) :=
  (cancel_epi (J.powQuotientπ M k')).mp
    (((J.powQuotientCone M).w (homOfLE h).op).trans (J.powQuotientπ_powQuotientDesc M _).symm)

/-- The composite `lim_k M / J ^ (k + 1) M ⟶ M / J ^ (k + 1) M ⟶ M / J' ^ (n + 1) M` does not
depend on `k`. -/
lemma limit_π_powQuotientDesc {k k' n : ℕ} (hkn : J.powSubmodule M k ≤ J'.powSubmodule M n)
    (hk'n : J.powSubmodule M k' ≤ J'.powSubmodule M n) :
    limit.π (J.powQuotientDiagram M) (op k) ≫ J.powQuotientDesc M hkn =
      limit.π (J.powQuotientDiagram M) (op k') ≫ J.powQuotientDesc M hk'n := by
  have key : ∀ {a b : ℕ} (hab : a ≤ b) (ha : J.powSubmodule M a ≤ J'.powSubmodule M n)
      (hb : J.powSubmodule M b ≤ J'.powSubmodule M n),
      limit.π (J.powQuotientDiagram M) (op a) ≫ J.powQuotientDesc M ha =
        limit.π (J.powQuotientDiagram M) (op b) ≫ J.powQuotientDesc M hb := by
    intro a b hab ha hb
    exact (congrArg (· ≫ J.powQuotientDesc M ha)
      (limit.w (J.powQuotientDiagram M) (homOfLE hab).op).symm).trans
      ((Category.assoc _ _ _).trans (congrArg (limit.π (J.powQuotientDiagram M) (op b) ≫ ·)
        ((congrArg (· ≫ J.powQuotientDesc M ha) (J.powQuotientDiagram_map_eq M hab)).trans
          (J.powQuotientDesc_comp M _ ha))))
  have hmax : J.powSubmodule M (max k k') ≤ J'.powSubmodule M n :=
    (smulSubmodule_mono M (J.pow_le_pow_right (Nat.succ_le_succ (le_max_left k k')))).trans hkn
  exact (key (le_max_left k k') hkn hmax).trans (key (le_max_right k k') hk'n hmax).symm

variable {J M}

/-- If every `J' ^ (n + 1) M` contains some `J ^ (k + 1) M`, the components
`lim_k M / J ^ (k + 1) M ⟶ M / J' ^ (n + 1) M` of the induced map of limits. -/
def limitPowQuotientMapApp (hJJ' : ∀ n, ∃ k, J.powSubmodule M k ≤ J'.powSubmodule M n)
    (n : ℕ) : limit (J.powQuotientDiagram M) ⟶ J'.powQuotient M n :=
  limit.π (J.powQuotientDiagram M) (op (hJJ' n).choose) ≫ J.powQuotientDesc M (hJJ' n).choose_spec

lemma limitPowQuotientMapApp_eq (hJJ' : ∀ n, ∃ k, J.powSubmodule M k ≤ J'.powSubmodule M n)
    {k n : ℕ} (hkn : J.powSubmodule M k ≤ J'.powSubmodule M n) :
    limitPowQuotientMapApp hJJ' n =
      limit.π (J.powQuotientDiagram M) (op k) ≫ J.powQuotientDesc M hkn :=
  J.limit_π_powQuotientDesc M _ _

lemma powQuotientMap_eq_powQuotientDesc (n : ℕ) :
    J.powQuotientMap M n =
      J.powQuotientDesc M (smulSubmodule_mono M (J.pow_le_pow_right (Nat.le_succ (n + 1)))) :=
  (cancel_epi (J.powQuotientπ M (n + 1))).mp (by simp)

lemma limitPowQuotientMapApp_comp
    (hJJ' : ∀ n, ∃ k, J.powSubmodule M k ≤ J'.powSubmodule M n) (n : ℕ) :
    limitPowQuotientMapApp hJJ' (n + 1) ≫ J'.powQuotientMap M n =
      limitPowQuotientMapApp hJJ' n :=
  (congrArg (limitPowQuotientMapApp hJJ' (n + 1) ≫ ·)
    (powQuotientMap_eq_powQuotientDesc (J := J') (M := M) n)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (limit.π (J.powQuotientDiagram M) (op (hJJ' (n + 1)).choose) ≫ ·)
        (J.powQuotientDesc_comp M _ _)).trans (limitPowQuotientMapApp_eq hJJ' _).symm))

/-- If every `J' ^ (n + 1) M` contains some `J ^ (k + 1) M`, the induced map
`lim_k M / J ^ (k + 1) M ⟶ lim_n M / J' ^ (n + 1) M`. -/
def limitPowQuotientMap (hJJ' : ∀ n, ∃ k, J.powSubmodule M k ≤ J'.powSubmodule M n) :
    limit (J.powQuotientDiagram M) ⟶ limit (J'.powQuotientDiagram M) :=
  limit.lift (J'.powQuotientDiagram M)
    { pt := limit (J.powQuotientDiagram M)
      π := NatTrans.ofOpSequence (G := J'.powQuotientDiagram M) (limitPowQuotientMapApp hJJ')
        (fun n => (Category.id_comp _).trans ((limitPowQuotientMapApp_comp hJJ' n).symm.trans
          (congrArg (limitPowQuotientMapApp hJJ' (n + 1) ≫ ·)
            (Functor.ofOpSequence_map_homOfLE_succ _ n).symm))) }

@[reassoc (attr := simp)]
lemma limitPowQuotientMap_π (hJJ' : ∀ n, ∃ k, J.powSubmodule M k ≤ J'.powSubmodule M n)
    {k n : ℕ} (hkn : J.powSubmodule M k ≤ J'.powSubmodule M n) :
    limitPowQuotientMap hJJ' ≫ limit.π (J'.powQuotientDiagram M) (op n) =
      limit.π (J.powQuotientDiagram M) (op k) ≫ J.powQuotientDesc M hkn :=
  (limit.lift_π _ _).trans (limitPowQuotientMapApp_eq hJJ' hkn)

lemma toLimitPowQuotient_limitPowQuotientMap
    (hJJ' : ∀ n, ∃ k, J.powSubmodule M k ≤ J'.powSubmodule M n) :
    J.toLimitPowQuotient M ≫ limitPowQuotientMap hJJ' = J'.toLimitPowQuotient M := by
  refine limit.hom_ext fun ⟨n⟩ => ?_
  obtain ⟨k, hk⟩ := hJJ' n
  simp only [Category.assoc, limitPowQuotientMap_π hJJ' hk, toLimitPowQuotient_π]
  exact (J.toLimitPowQuotient_π_assoc M k _).trans (J.powQuotientπ_powQuotientDesc M hk)

lemma limitPowQuotientMap_comp
    (hJJ' : ∀ n, ∃ k, J.powSubmodule M k ≤ J'.powSubmodule M n)
    (hJ'J'' : ∀ n, ∃ k, J'.powSubmodule M k ≤ J''.powSubmodule M n)
    (hJJ'' : ∀ n, ∃ k, J.powSubmodule M k ≤ J''.powSubmodule M n) :
    limitPowQuotientMap hJJ' ≫ limitPowQuotientMap hJ'J'' = limitPowQuotientMap hJJ'' := by
  refine limit.hom_ext fun ⟨n⟩ => ?_
  obtain ⟨m, hm⟩ := hJ'J'' n
  obtain ⟨k, hk⟩ := hJJ' m
  simp only [Category.assoc, limitPowQuotientMap_π hJ'J'' hm,
    limitPowQuotientMap_π hJJ'' (hk.trans hm)]
  exact (limitPowQuotientMap_π_assoc hJJ' hk _).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (J.powQuotientDesc_comp M hk hm)))

lemma limitPowQuotientMap_self (hJJ : ∀ n, ∃ k, J.powSubmodule M k ≤ J.powSubmodule M n) :
    limitPowQuotientMap hJJ = 𝟙 _ := by
  refine limit.hom_ext fun ⟨n⟩ => ?_
  simp only [limitPowQuotientMap_π hJJ (le_refl (J.powSubmodule M n)), powQuotientDesc_self,
    Category.id_comp]
  exact Category.comp_id _

/-- **Cofinal systems of ideals have the same completion.** If the systems `J ^ (n + 1) M` and
`J' ^ (n + 1) M` are mutually cofinal, then `lim_n M / J ^ (n + 1) M ≅ lim_n M / J' ^ (n + 1) M`,
compatibly with the canonical maps from `M`. -/
def limitPowQuotientIsoOfCofinal
    (hJJ' : ∀ n, ∃ k, J.powSubmodule M k ≤ J'.powSubmodule M n)
    (hJ'J : ∀ n, ∃ k, J'.powSubmodule M k ≤ J.powSubmodule M n) :
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
    (hJJ' : ∀ n, ∃ k, J.powSubmodule M k ≤ J'.powSubmodule M n)
    (hJ'J : ∀ n, ∃ k, J'.powSubmodule M k ≤ J.powSubmodule M n) :
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

/-- **`J` kills `M`**: `J(V) M(V) = 0` for every open `V`. -/
def Annihilates : Prop := ∀ V : Opens T, J.sectionsSmul M V = ⊥

/-! ### Modules killed by an ideal subsheaf

A module `M` killed by `J` is a module over `R / J`: the sections `M(V)` are modules over
`R(V) ⧸ J(V)`, and the sheafification of this presheaf of modules has underlying sheaf `M`. The
quotient `M / J M` is killed by `J`. -/

section Annihilates

variable {J M}

/-- If `J` kills `M`, every section of `J` kills every section of `M`. -/
lemma Annihilates.smul_eq_zero (hM : J.Annihilates M) {V : Opens T} {r : R.presheaf.obj (op V)}
    (hr : r ∈ J.ideal V) (m : M.val.obj (op V)) :
    (show (ringCatSheafOf R).obj.obj (op V) from r) • m = 0 := by
  have : (show (ringCatSheafOf R).obj.obj (op V) from r) • m ∈ J.sectionsSmul M V :=
    Submodule.smul_mem_smul hr trivial
  rw [hM V] at this
  exact this

variable (J) in
private lemma quotientπ_hom_eq :
    J.quotientπ.hom = J.quotientPresheafπ ≫ toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap) := by
  rw [toSheafify_naturality]
  rfl

variable (J) in
private lemma quotientπ_app_apply (U : Opens T) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op U) s = (toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap)).app (op U)
        (Ideal.Quotient.mk (J.ideal U) s) := by
  rw [quotientπ_hom_eq]
  rfl

variable (J) in
/-- The projection `R ⟶ R / J` is locally surjective. -/
lemma isLocallySurjective_quotientπ :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) J.quotientπ.hom := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun U t x hx => ?_
  obtain ⟨V, hVU, ⟨q, hq⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff
    (toSheafify (Opens.grothendieckTopology T)
      (idealQuotientPresheaf R J.ideal J.ideal_le_comap))).mp
    (inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) _)) U t x hx
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨V, hVU, ⟨s, by rw [quotientπ_app_apply]; exact hq⟩, hxV⟩

variable (J) in
/-- The presheaf of rings `V ↦ R(V) ⧸ J(V)` in `RingCat`. -/
abbrev quotientPresheafRingCat : (Opens T)ᵒᵖ ⥤ RingCat.{u} :=
  idealQuotientPresheaf R J.ideal J.ideal_le_comap ⋙ forget₂ CommRingCat RingCat.{u}

variable (J) in
/-- The sheafification map from the presheaf `V ↦ R(V) ⧸ J(V)` to `R / J`, in `RingCat`. -/
def quotientPresheafToSheaf : J.quotientPresheafRingCat ⟶ (ringCatSheafOf J.quotient).obj :=
  Functor.whiskerRight (toSheafify (Opens.grothendieckTopology T)
    (idealQuotientPresheaf R J.ideal J.ideal_le_comap)) (forget₂ CommRingCat RingCat.{u})

variable (J) in
instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) J.quotientPresheafToSheaf :=
  ⟨fun {_} s => (Presheaf.isLocallySurjective_toSheafify' (J := Opens.grothendieckTopology T)
    (idealQuotientPresheaf R J.ideal J.ideal_le_comap)).imageSieve_mem s⟩

variable (J) in
instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology T) J.quotientPresheafToSheaf :=
  ⟨fun {_} s t h => (Presheaf.isLocallyInjective_toSheafify' (J := Opens.grothendieckTopology T)
    (idealQuotientPresheaf R J.ideal J.ideal_le_comap)).equalizerSieve_mem s t h⟩

/-- For `M` killed by `J`, the module structure of `M(V)` over `R(V) ⧸ J(V)`. -/
@[instance_reducible]
def Annihilates.sectionsModule (hM : J.Annihilates M) (V : (Opens T)ᵒᵖ) :
    Module (J.quotientPresheafRingCat.obj V) (M.val.presheaf.obj V) :=
  @Module.IsTorsionBySet.module ((ringCatSheafOf R).obj.obj V) (M.val.obj V) _ _ _
    (J.ideal V.unop) _ (fun m r => hM.smul_eq_zero r.2 m)

/-- The class of `r` acts on `M(V)` as `r` does. -/
lemma Annihilates.mk_smul (hM : J.Annihilates M) (V : (Opens T)ᵒᵖ) (r : R.presheaf.obj V)
    (m : M.val.obj V) :
    letI := hM.sectionsModule V
    (show J.quotientPresheafRingCat.obj V from Ideal.Quotient.mk (J.ideal V.unop) r) •
      (show M.val.presheaf.obj V from m) =
      (show (ringCatSheafOf R).obj.obj V from r) • m :=
  rfl

/-- For `M` killed by `J`, `M` as a presheaf of modules over `V ↦ R(V) ⧸ J(V)`. -/
def Annihilates.presheafModule (hM : J.Annihilates M) :
    PresheafOfModules.{u} J.quotientPresheafRingCat :=
  letI := hM.sectionsModule
  PresheafOfModules.ofPresheaf M.val.presheaf (by
    intro V W f r m
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact M.val.map_smul f r m)

variable (M) in
/-- The sheaf of abelian groups underlying `M`. -/
abbrev toAbSheaf : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} :=
  ⟨M.val.presheaf, M.isSheaf⟩

/-- The identity of the underlying sheaf of `M` is a sheafification map. -/
lemma Annihilates.isLocallyInjective_id (hM : J.Annihilates M) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology T)
      (show hM.presheafModule.presheaf ⟶ (toAbSheaf M).obj from 𝟙 _) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ => Function.injective_id

/-- The identity of the underlying sheaf of `M` is a sheafification map. -/
lemma Annihilates.isLocallySurjective_id (hM : J.Annihilates M) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology T)
      (show hM.presheafModule.presheaf ⟶ (toAbSheaf M).obj from 𝟙 _) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ => Function.surjective_id

/-- **A module killed by `J` is a module over `R / J`**: the sheafification of `M`, viewed as a
presheaf of modules over `V ↦ R(V) ⧸ J(V)`, whose underlying sheaf is `M` itself. -/
def Annihilates.quotientModule (hM : J.Annihilates M) :
    SheafOfModules.{u} (ringCatSheafOf J.quotient) :=
  @PresheafOfModules.sheafify _ _ _ _ _ J.quotientPresheafToSheaf _ _ hM.presheafModule
    (toAbSheaf M) (show hM.presheafModule.presheaf ⟶ (toAbSheaf M).obj from 𝟙 _)
    hM.isLocallyInjective_id hM.isLocallySurjective_id

/-- On `hM.quotientModule`, the image of `r ∈ R(V)` in `(R / J)(V)` acts as `r` acts on `M`. -/
lemma Annihilates.quotientπ_smul (hM : J.Annihilates M) (V : Opens T) (r : R.presheaf.obj (op V))
    (m : M.val.obj (op V)) :
    (show (ringCatSheafOf J.quotient).obj.obj (op V) from J.quotientπ.hom.app (op V) r) •
      (show hM.quotientModule.val.obj (op V) from m) =
      (show M.val.obj (op V) from (show (ringCatSheafOf R).obj.obj (op V) from r) • m) := by
  have := hM.isLocallyInjective_id
  have := hM.isLocallySurjective_id
  have := PresheafOfModules.Sheafify.map_smul_eq J.quotientPresheafToSheaf
    (M₀ := hM.presheafModule) (A := toAbSheaf M)
    (show hM.presheafModule.presheaf ⟶ (toAbSheaf M).obj from 𝟙 _)
    (J.quotientπ.hom.app (op V) r) m (𝟙 _) (Ideal.Quotient.mk (J.ideal V) r)
    (by rw [CategoryTheory.Functor.map_id]; exact (J.quotientπ_app_apply V r).symm) m
    (by rw [CategoryTheory.Functor.map_id]; rfl)
  rw [CategoryTheory.Functor.map_id] at this
  exact this

section LocalLift

variable {A B : SheafOfModules.{u} (ringCatSheafOf R)}

private lemma toSheaf_preservesColimit {K : Type} [SmallCategory K]
    (D : K ⥤ SheafOfModules.{u} (ringCatSheafOf R)) :
    PreservesColimit D (SheafOfModules.toSheaf (ringCatSheafOf R)) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)
  let D₀ : K ⥤ PresheafOfModules.{u} (ringCatSheafOf R).obj := D ⋙ SheafOfModules.forget _
  let D' : K ⥤ SheafOfModules.{u} (ringCatSheafOf R) :=
    D₀ ⋙ PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)
  let e : D ≅ D' := Functor.isoWhiskerLeft D (asIso adj.counit).symm
  have hc₀ := colimit.isColimit D₀
  have : PreservesColimitsOfSize.{0, 0}
      (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)) :=
    adj.leftAdjoint_preservesColimits
  have h2 : PreservesColimit D₀
      (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj) ⋙
        SheafOfModules.toSheaf (ringCatSheafOf R)) :=
    preservesColimit_of_natIso D₀
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 (ringCatSheafOf R).obj)).symm
  have : PreservesColimit D' (SheafOfModules.toSheaf (ringCatSheafOf R)) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)) hc₀)
      (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj) ⋙
        SheafOfModules.toSheaf (ringCatSheafOf R)) hc₀)
  exact preservesColimit_of_iso_diagram _ e.symm

/-- An epimorphism of `R`-modules is locally surjective on sections. -/
private lemma exists_local_lift (g : A ⟶ B) [Epi g] {U : Opens T} (t : B.val.obj (op U)) {x : T}
    (hx : x ∈ U) : ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧
      ∃ s : A.val.obj (op V), g.val.app (op V) s = B.val.map (homOfLE hVU).op t := by
  have h := toSheaf_preservesColimit (span g g)
  have : Epi ((SheafOfModules.toSheaf (ringCatSheafOf R)).map g) :=
    @preserves_epi_of_preservesColimit _ _ _ _ (SheafOfModules.toSheaf (ringCatSheafOf R)) _ _ g h
      ‹Epi g›
  have h := (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((SheafOfModules.toSheaf (ringCatSheafOf R)).map g)).mpr this
  obtain ⟨V, hVU, ⟨s, hs⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp h U t x hx
  exact ⟨V, hVU, hxV, s, hs⟩

/-- A section of an `R`-module which vanishes near every point vanishes. -/
private lemma eq_zero_of_locally {U : Opens T} (s : A.val.obj (op U))
    (hs : ∀ x ∈ U, ∃ (V : Opens T) (hVU : V ≤ U), x ∈ V ∧ A.val.map (homOfLE hVU).op s = 0) :
    s = 0 := by
  choose V hVU hxV hV using hs
  let A' : TopCat.Sheaf AddCommGrpCat.{u} T := ⟨A.val.presheaf, A.isSheaf⟩
  refine A'.eq_of_locally_eq' (U := fun x : U => V x.1 x.2) U
    (fun x => homOfLE (hVU x.1 x.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) s 0 fun x => ?_
  exact (hV x.1 x.2).trans (map_zero _).symm

end LocalLift

variable (J M) in
/-- **`J` kills `M / J M`**: near every point a section of `M / J M` is the class of a section of
`M`, and `J` maps those into `J M`. -/
theorem annihilates_cokernel_smulι : J.Annihilates (cokernel (J.smulι M)) := by
  intro V
  refine eq_bot_iff.mpr (Submodule.smul_le.mpr fun r hr q _ => ?_)
  rw [Submodule.mem_bot]
  refine eq_zero_of_locally _ fun x hx => ?_
  obtain ⟨W, hWV, hxW, f, hf⟩ := exists_local_lift (cokernel.π (J.smulι M)) q hx
  refine ⟨W, hWV, hxW, ?_⟩
  have hrW : R.presheaf.map (homOfLE hWV).op r ∈ J.ideal W := J.ideal_le_comap hWV hr
  have hmem : (show (ringCatSheafOf R).obj.obj (op W) from R.presheaf.map (homOfLE hWV).op r) • f ∈
      (J.smulSubmodule M).obj (op W) :=
    J.sectionsSmul_le_smulSubmodule M W (Submodule.smul_mem_smul hrW trivial)
  have h0 : (cokernel.π (J.smulι M)).val.app (op W)
      ((J.smulι M).val.app (op W) ⟨_, hmem⟩) = 0 := by
    have := congrArg (fun k => k.val.app (op W) ⟨_, hmem⟩) (cokernel.condition (J.smulι M))
    exact this
  rw [(cokernel (J.smulι M)).val.map_smul, ← hf]
  exact (((cokernel.π (J.smulι M)).val.app (op W)).hom.map_smul _ f).symm.trans h0

end Annihilates

end IdealSubsheaf

/-! ### The completion of a module is complete for `J`

Let `I` be a quasi-coherent ideal subsheaf of `𝒪_X`, `X` locally Noetherian, and `J` the ideal
subsheaf `ker (𝒪_{X̂} ⟶ 𝒪_Y)` of the structure sheaf of the formal completion `X̂` along `I`.
For a quasi-coherent `𝒪_X`-module `F`, the kernel of `F̂ ⟶ (F / I ^ (n + 1) F)|_Y` is
`J ^ (n + 1) F̂`, so `F̂ / J ^ (n + 1) F̂ ≅ (F / I ^ (n + 1) F)|_Y`, and `F̂` is the limit of the
`F̂ / J ^ (n + 1) F̂`. -/

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

/-- The ideal subsheaf `J = ker (𝒪_{X̂} ⟶ 𝒪_Y)` of the structure sheaf of the formal completion. -/
def formalCompletionIdealSubsheaf : IdealSubsheaf I.formalCompletionSheaf :=
  IdealSubsheaf.ofIdeals _ I.formalCompletionIdeal (fun h => I.formalCompletionIdeal_le_comap h)
    (fun s hs => I.mem_formalCompletionIdeal_of_locally s hs)

lemma formalCompletionIdealSubsheaf_pow_ideal (k : ℕ) (V : Opens (I.infinitesimalNeighborhood 1)) :
    (I.formalCompletionIdealSubsheaf ^ k).ideal V = I.formalCompletionIdealPow k V :=
  rfl


variable (G : X.Modules)

/-- The completion `F̂`, as a module over `𝒪_{X̂}` in the form used for ideal subsheaves. -/
abbrev moduleCompletion' : SheafOfModules.{u} (ringCatSheafOf I.formalCompletionSheaf) :=
  I.moduleCompletion G

/-- `(F / I ^ (n + 1) F)|_Y`, as a module over `𝒪_{X̂}` in the form used for ideal subsheaves. -/
abbrev moduleCompletionObj' (n : ℕ) : SheafOfModules.{u} (ringCatSheafOf I.formalCompletionSheaf) :=
  I.moduleCompletionObj G n

/-- The projection `F̂ ⟶ (F / I ^ (n + 1) F)|_Y`. -/
abbrev moduleCompletionπ' (n : ℕ) : I.moduleCompletion' G ⟶ I.moduleCompletionObj' G n :=
  I.moduleCompletionπ G n

/-- `J ^ (n + 1)` maps `F̂` to zero in `(F / I ^ (n + 1) F)|_Y`. -/
lemma smulι_moduleCompletionπ [IsLocallyNoetherian X] (n : ℕ) :
    (I.formalCompletionIdealSubsheaf ^ (n + 1)).smulι (I.moduleCompletion' G) ≫
      I.moduleCompletionπ' G n = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  ext ⟨s, hs⟩
  change (I.moduleCompletionπ' G n).val.app V s = 0
  -- the image of `a • y`, `a ∈ J ^ (n + 1)`, vanishes
  have key : ∀ (W : Opens (I.infinitesimalNeighborhood 1))
      (t : (I.moduleCompletion' G).val.obj (op W)),
      t ∈ (I.formalCompletionIdealSubsheaf ^ (n + 1)).sectionsSmul (I.moduleCompletion' G) W →
        (I.moduleCompletionπ' G n).val.app (op W) t = 0 := by
    intro W t ht
    refine Submodule.smul_induction_on ht (fun a ha y _ => ?_) (fun y z hy hz => ?_)
    · rw [map_smul]
      have h0 : (I.formalCompletionπ n).hom.app (op W) a = 0 :=
        (I.mem_formalCompletionIdealPow_iff n W a).mp ha
      have h1 : (I.formalCompletionRingCatSheafπ n).hom.app (op W) a = 0 := h0
      change (show (I.infinitesimalNeighborhood (n + 1)).ringCatSheaf.obj.obj
          (op ((I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj W)) from
          (I.formalCompletionRingCatSheafπ n).hom.app (op W) a) •
        (show (I.moduleCompletionNeighborhood G n).val.obj
          (op ((I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj W)) from
          (I.moduleCompletionπ' G n).val.app (op W) y) = 0
      rw [show (show (I.infinitesimalNeighborhood (n + 1)).ringCatSheaf.obj.obj
          (op ((I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj W)) from
          (I.formalCompletionRingCatSheafπ n).hom.app (op W) a) = 0 from h1, zero_smul]
    · rw [map_add, hy, hz, add_zero]
  refine IdealSubsheaf.eq_zero_of_locally _ fun x hx => ?_
  obtain ⟨W, hWV, hxW, hsW⟩ := hs x hx
  refine ⟨W, hWV, hxW, ?_⟩
  exact (PresheafOfModules.naturality_apply (I.moduleCompletionπ' G n).val (homOfLE hWV).op
    s).symm.trans (key W _ hsW)


/-- An element of `span {f i} • N` is a combination `∑ f i • c i` with `c i ∈ N`. -/
private lemma exists_sum_of_mem_span_smul {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {r : ℕ} (f : Fin r → A) (N : Submodule A M) {m : M}
    (hm : m ∈ Submodule.span A (Set.range f) • N) :
    ∃ c : Fin r → M, (∀ i, c i ∈ N) ∧ m = ∑ i, f i • c i := by
  refine Submodule.smul_induction_on hm (fun a ha y hy => ?_) (fun y z hy hz => ?_)
  · obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp ha
    refine ⟨fun i => b i • y, fun i => N.smul_mem _ hy, ?_⟩
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, smul_eq_mul, mul_comm]
  · obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    exact ⟨c + d, fun i => N.add_mem (hc i) (hd i), by
      simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]⟩

/-- The canonical map `𝒪_X ⟶ i_* 𝒪_{X̂_Y}` of sheaves of commutative rings. -/
private def toFormalCompletionSheaf :
    X.sheaf ⟶ ((Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafPushforwardContinuous
      CommRingCat.{u} _ _).obj I.formalCompletionSheaf where
  hom :=
    { app U := I.formalCompletionSectionsMap U.unop
      naturality _ _ f := (I.formalCompletionSectionsMap_naturality (leOfHom f.unop)).symm }

/-- The canonical map `𝒪_X ⟶ i_* 𝒪_{X̂_Y}` of sheaves of rings in `RingCat`. -/
private def toFormalCompletionRingCatSheaf :
    X.ringCatSheaf ⟶ ((Opens.map (I.infinitesimalNeighborhoodι 1).base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj I.formalCompletionRingCatSheaf where
  hom := Functor.whiskerRight I.toFormalCompletionSheaf.hom (forget₂ CommRingCat RingCat.{u})

private lemma toFormalCompletionRingCatSheaf_compat (n : ℕ) (V : X.Opensᵒᵖ)
    (r : X.ringCatSheaf.obj.obj V) :
    (I.infinitesimalNeighborhood (n + 1)).ringCatSheaf.obj.map
        ((I.functorToPreimageInfinitesimalNeighborhoodι n).app V.unop).op
        ((I.infinitesimalNeighborhoodι (n + 1)).toRingCatSheafHom.hom.app V r) =
      (I.formalCompletionRingCatSheafπ n).hom.app
        (op ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj V.unop))
        (I.toFormalCompletionRingCatSheaf.hom.app V r) :=
  (congrArg (fun g => g.hom r) (I.formalCompletionSectionsMap_π V.unop n)).symm

/-- `𝒪_X(U) ⟶ 𝒪_{X̂}(U ∩ |Y|)` carries `I(U)` into `J(U ∩ |Y|)`, for `U` affine. -/
private lemma toFormalCompletionRingCatSheaf_mem (U : X.affineOpens) {a : Γ(X, (U : X.Opens))}
    (ha : a ∈ I.ideal U) :
    I.toFormalCompletionRingCatSheaf.hom.app (op (U : X.Opens)) a ∈
      I.formalCompletionIdeal ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj U) := by
  have hk : RingHom.ker ((I.infinitesimalNeighborhoodι (0 + 1)).app U).hom = I.ideal U ^ (0 + 1) :=
    (Scheme.IdealSheafData.ker_subschemeι_app _ U).trans (I.ideal_pow (0 + 1) U)
  have hker : (I.infinitesimalNeighborhoodι (0 + 1)).app U a = 0 := by
    have : a ∈ RingHom.ker ((I.infinitesimalNeighborhoodι (0 + 1)).app U).hom := by
      rw [hk, _root_.pow_one]
      exact ha
    exact this
  have h := I.toFormalCompletionRingCatSheaf_compat 0 (op (U : X.Opens)) a
  have h0 : (I.infinitesimalNeighborhood (0 + 1)).ringCatSheaf.obj.map
      ((I.functorToPreimageInfinitesimalNeighborhoodι 0).app U).op
      ((I.infinitesimalNeighborhoodι (0 + 1)).toRingCatSheafHom.hom.app (op U) a) = 0 := by
    change (I.infinitesimalNeighborhood (0 + 1)).ringCatSheaf.obj.map _
      ((I.infinitesimalNeighborhoodι (0 + 1)).app U a) = 0
    rw [hker]
    exact map_zero _
  exact (I.mem_formalCompletionIdeal_iff _ _).mpr (h.symm.trans h0)


open Scheme.Modules in
/-- **The kernel of `F̂ ⟶ (F / I ^ (n + 1) F)|_Y` is `J ^ (n + 1) F̂`, over an affine open.** For
`X` locally Noetherian, `F` quasi-coherent and `U` affine, a section of `F̂` over `U ∩ |Y|` with
vanishing image in `(F / I ^ (n + 1) F)|_Y` lies in `J(U ∩ |Y|) ^ (n + 1) F̂(U ∩ |Y|)`. -/
theorem mem_sectionsSmul_of_moduleCompletionπ_eq_zero [IsLocallyNoetherian X] [G.IsQuasicoherent]
    (n : ℕ) (U : X.affineOpens)
    (x : ((SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf).obj
      (I.moduleCompletion G)).val.obj (op (U : X.Opens)))
    (hx : ((SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf).map
      (I.moduleCompletionπ G n)).val.app (op (U : X.Opens)) x = 0) :
    (show (I.moduleCompletion' G).val.obj
      (op ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj U)) from x) ∈
      (I.formalCompletionIdealSubsheaf ^ (n + 1)).sectionsSmul (I.moduleCompletion' G)
        ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj U) := by
  have hχ := I.toFormalCompletionRingCatSheaf_compat
  -- lifts of the components of `x`
  choose s hs using fun k => I.moduleCompletionSectionsMap_surjective G k U
    (((SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf).map
      (I.moduleCompletionπ G k)).val.app (op (U : X.Opens)) x)
  have hs' : ∀ k, (I.moduleCompletionLevelMap I.toFormalCompletionRingCatSheaf hχ G k).val.app
      (op (U : X.Opens)) (s k) =
      ((SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf).map
        (I.moduleCompletionπ G k)).val.app (op (U : X.Opens)) x := fun k =>
    (I.moduleCompletionLevelMap_val_app I.toFormalCompletionRingCatSheaf hχ G k U (s k)).trans
      (hs k)
  have hker : ∀ (k : ℕ) (t : Γ(G, (U : X.Opens))),
      (I.moduleCompletionLevelMap I.toFormalCompletionRingCatSheaf hχ G k).val.app
        (op (U : X.Opens)) t = 0 ↔
      t ∈ I.ideal U ^ (k + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(G, (U : X.Opens))) :=
    fun k t => I.moduleCompletionSectionsMap_eq_zero_iff G k U t
  have hxs := fun k => I.moduleCompletionMap_val_app_moduleCompletionπ
    I.toFormalCompletionRingCatSheaf G k U x
  -- the lifts form a Cauchy sequence
  have hS : ∀ k, s (k + 1) - s k ∈
      I.ideal U ^ (k + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(G, (U : X.Opens))) := by
    intro k
    have a1 := (I.moduleCompletionMap_val_app_moduleCompletionLevelMap
      I.toFormalCompletionRingCatSheaf hχ G k U (s (k + 1))).symm.trans
      ((congrArg (fun y => ((SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf).map
        (I.moduleCompletionMap G k)).val.app (op (U : X.Opens)) y) (hs' (k + 1))).trans (hxs k))
    exact (hker k _).1 ((map_sub _ _ _).trans (sub_eq_zero.2 (a1.trans (hs' k).symm)))
  -- `s n ∈ I(U) ^ (n + 1) Γ(U, G)`
  have hsn : s n ∈ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(G, (U : X.Opens))) :=
    (hker n _).1 ((hs' n).trans hx)
  have htel : ∀ k m, s (k + m) - s k ∈
      I.ideal U ^ (k + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(G, (U : X.Opens))) := by
    intro k m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show s (k + (m + 1)) - s k = (s (k + m + 1) - s (k + m)) + (s (k + m) - s k) by
        rw [← add_assoc]; abel]
      exact add_mem (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (hS (k + m))) ih
  -- generators of `I(U) ^ (n + 1)`
  have : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (I.ideal U ^ (n + 1)))
  have hd : ∀ j, ∃ d : Fin r → Γ(G, (U : X.Opens)),
      (∀ i, d i ∈ I.ideal U ^ j • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(G, (U : X.Opens)))) ∧
        s (n + j + 1) - s (n + j) = ∑ i, f i • d i := by
    intro j
    refine exists_sum_of_mem_span_smul f _ ?_
    rw [hf, ← Submodule.mul_smul, ← pow_add, show n + 1 + j = n + j + 1 by omega]
    exact hS (n + j)
  choose d hd hd' using hd
  obtain ⟨c₀, -, hc₀⟩ := exists_sum_of_mem_span_smul f
    (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(G, (U : X.Opens))) (by rw [hf]; exact hsn)
  let c : ℕ → Fin r → Γ(G, (U : X.Opens)) := fun j => c₀ + ∑ k ∈ Finset.range j, d k
  have hc : ∀ j, s (n + j) = ∑ i, f i • c j i := by
    intro j
    induction j with
    | zero => simpa [c] using hc₀
    | succ j ih =>
      rw [show n + (j + 1) = n + j + 1 by omega, ← sub_add_cancel (s (n + j + 1)) (s (n + j)),
        hd' j, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [c, Finset.sum_range_succ, Pi.add_apply, Finset.sum_apply, smul_add]
      abel
  have hcC : ∀ i j, c (j + 1 + 1) i - c (j + 1) i ∈
      I.ideal U ^ (j + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(G, (U : X.Opens))) := by
    intro i j
    simp only [c, Finset.sum_range_succ (n := j + 1), Pi.add_apply, Finset.sum_apply]
    convert hd (j + 1) i using 1
    abel
  choose y hy using fun i => I.exists_moduleCompletion_sections I.toFormalCompletionRingCatSheaf
    hχ G U (fun j => c (j + 1) i) (hcC i)
  have : (PresheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf.hom).IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top _)
  have : (SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf).IsRightAdjoint :=
    (SheafOfModules.PullbackConstruction.adjunction.{u} _).isRightAdjoint
  have hlim := isLimitOfPreserves (SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf)
    (limit.isLimit (I.moduleCompletionDiagram G))
  -- `x = ∑ f i • y i`
  have hxy : x = ∑ i, (show X.ringCatSheaf.obj.obj (op (U : X.Opens)) from f i) • y i := by
    refine sections_isLimit_mapCone_ext hlim (op (U : X.Opens)) _ _ fun k => ?_
    change _ = ((SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf).map
      (I.moduleCompletionπ G k)).val.app (op (U : X.Opens)) (∑ i, _ • y i)
    have e1 : ∀ i, ((SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf).map
        (I.moduleCompletionπ G k)).val.app (op (U : X.Opens))
          ((show X.ringCatSheaf.obj.obj (op (U : X.Opens)) from f i) • y i) =
        (show X.ringCatSheaf.obj.obj (op (U : X.Opens)) from f i) •
          (I.moduleCompletionLevelMap I.toFormalCompletionRingCatSheaf hχ G k).val.app
            (op (U : X.Opens)) (c (k + 1) i) := fun i =>
      ((((SheafOfModules.pushforward.{u} I.toFormalCompletionRingCatSheaf).map
        (I.moduleCompletionπ G k)).val.app (op (U : X.Opens))).hom.map_smul _ (y i)).trans
        (congrArg _ (hy i k))
    have e2 : (I.moduleCompletionLevelMap I.toFormalCompletionRingCatSheaf hχ G k).val.app
        (op (U : X.Opens)) (∑ i, f i • c (k + 1) i) =
        ∑ i, (show X.ringCatSheaf.obj.obj (op (U : X.Opens)) from f i) •
          (I.moduleCompletionLevelMap I.toFormalCompletionRingCatSheaf hχ G k).val.app
            (op (U : X.Opens)) (c (k + 1) i) :=
      (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ =>
        ((I.moduleCompletionLevelMap I.toFormalCompletionRingCatSheaf hχ G k).val.app
          (op (U : X.Opens))).hom.map_smul _ _)
    have e3 : (I.moduleCompletionLevelMap I.toFormalCompletionRingCatSheaf hχ G k).val.app
        (op (U : X.Opens)) (s k) =
        (I.moduleCompletionLevelMap I.toFormalCompletionRingCatSheaf hχ G k).val.app
          (op (U : X.Opens)) (s (n + (k + 1))) := by
      have hm := htel k (n + 1)
      rw [show k + (n + 1) = n + (k + 1) by omega] at hm
      exact (sub_eq_zero.1 ((map_sub _ _ _).symm.trans ((hker k _).2 hm))).symm
    exact ((hs' k).symm.trans (e3.trans ((congrArg _ (hc (k + 1))).trans
      (e2.trans (Finset.sum_congr rfl fun i _ => (e1 i).symm))))).trans (map_sum _ _ _).symm
  -- the coefficients lie in `J ^ (n + 1)`
  have hmem : ∀ i, (I.toFormalCompletionSheaf.hom.app (op (U : X.Opens))) (f i) ∈
      (I.formalCompletionIdealSubsheaf ^ (n + 1)).ideal
        ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj U) := by
    intro i
    have hfi : f i ∈ I.ideal U ^ (n + 1) := hf ▸ Submodule.subset_span ⟨i, rfl⟩
    have h1 : Ideal.map (I.toFormalCompletionSheaf.hom.app (op (U : X.Opens))).hom (I.ideal U) ≤
        I.formalCompletionIdealSubsheaf.ideal
          ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj U) :=
      Ideal.map_le_iff_le_comap.mpr fun a ha => I.toFormalCompletionRingCatSheaf_mem U ha
    refine IdealSubsheaf.ideal_pow_le_ideal_pow _ _ _ (Ideal.pow_right_mono h1 (n + 1) ?_)
    exact (Ideal.map_pow (I.toFormalCompletionSheaf.hom.app (op (U : X.Opens))).hom
      (I := I.ideal U) (n + 1)).le (Ideal.mem_map_of_mem _ hfi)
  subst hxy
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hmem i) Submodule.mem_top


/-- The opens `U ∩ |Y|`, `U` affine, form a basis of `|Y|`. -/
private lemma isBasis_affineOpens_preimage :
    Opens.IsBasis ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj ''
      {U : X.Opens | IsAffineOpen U}) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {V x} hx => ?_
  obtain ⟨U, hxU, hUV⟩ := I.exists_affineOpens_preimage_le hx
  exact ⟨_, ⟨U, U.2, rfl⟩, hxU, hUV⟩

/-- The short complex `J ^ (n + 1) F̂ ⟶ F̂ ⟶ (F / I ^ (n + 1) F)|_Y`. -/
abbrev moduleCompletionPowShortComplex [IsLocallyNoetherian X] (n : ℕ) :
    ShortComplex (SheafOfModules.{u} (ringCatSheafOf I.formalCompletionSheaf)) :=
  ShortComplex.mk _ _ (I.smulι_moduleCompletionπ G n)

/-- **`J ^ (n + 1) F̂ ⟶ F̂ ⟶ (F / I ^ (n + 1) F)|_Y` is exact** for `X` locally Noetherian and `F`
quasi-coherent. -/
theorem moduleCompletionPowShortComplex_exact [IsLocallyNoetherian X] [G.IsQuasicoherent]
    (n : ℕ) : (I.moduleCompletionPowShortComplex G n).Exact := by
  refine sheafOfModules_exact_of_isBasis_sections _ I.isBasis_affineOpens_preimage ?_
  rintro _ ⟨U, hU, rfl⟩ x hx
  exact ⟨⟨x, (I.formalCompletionIdealSubsheaf ^ (n + 1)).sectionsSmul_le_smulSubmodule _ _
    (I.mem_sectionsSmul_of_moduleCompletionπ_eq_zero G n ⟨U, hU⟩ x hx)⟩, rfl⟩

/-- **`F̂ ⟶ (F / I ^ (n + 1) F)|_Y` is an epimorphism** for `F` quasi-coherent. -/
instance epi_moduleCompletionπ' [IsLocallyNoetherian X] [G.IsQuasicoherent] (n : ℕ) :
    Epi (I.moduleCompletionπ' G n) := by
  have hχ := I.toFormalCompletionRingCatSheaf_compat
  have h : (ShortComplex.mk (I.moduleCompletionπ' G n) (0 : _ ⟶ I.moduleCompletionObj' G n)
      comp_zero).Exact := by
    refine sheafOfModules_exact_of_isBasis_sections _ I.isBasis_affineOpens_preimage ?_
    rintro _ ⟨U, hU, rfl⟩ x -
    obtain ⟨t, ht⟩ := I.moduleCompletionSectionsMap_surjective G n ⟨U, hU⟩ x
    obtain ⟨z, hz⟩ := I.exists_moduleCompletion_sections I.toFormalCompletionRingCatSheaf hχ G
      ⟨U, hU⟩ (fun _ => t) (fun k => by simp)
    exact ⟨z, (hz n).trans ((I.moduleCompletionLevelMap_val_app _ hχ G n U t).trans ht)⟩
  exact (ShortComplex.exact_iff_epi _ rfl).mp h

/-- **`F̂ / J ^ (n + 1) F̂ ≅ (F / I ^ (n + 1) F)|_Y`**, for `X` locally Noetherian and `F`
quasi-coherent, induced by the projection `F̂ ⟶ (F / I ^ (n + 1) F)|_Y`. -/
def powQuotientModuleCompletionIso [IsLocallyNoetherian X] [G.IsQuasicoherent] (n : ℕ) :
    I.formalCompletionIdealSubsheaf.powQuotient (I.moduleCompletion' G) n ≅
      I.moduleCompletionObj' G n :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (I.moduleCompletionPowShortComplex_exact G n).gIsCokernel

@[reassoc (attr := simp)]
lemma powQuotientπ_powQuotientModuleCompletionIso_hom [IsLocallyNoetherian X] [G.IsQuasicoherent]
    (n : ℕ) :
    I.formalCompletionIdealSubsheaf.powQuotientπ (I.moduleCompletion' G) n ≫
      (I.powQuotientModuleCompletionIso G n).hom = I.moduleCompletionπ' G n :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one


/-- The inverse system of the completion, in the form used for ideal subsheaves. -/
abbrev moduleCompletionDiagram' :
    ℕᵒᵖ ⥤ SheafOfModules.{u} (ringCatSheafOf I.formalCompletionSheaf) :=
  I.moduleCompletionDiagram G

/-- `F̂` is the limit of its inverse system, in the form used for ideal subsheaves. -/
def isLimitModuleCompletionCone' :
    IsLimit (show Cone (I.moduleCompletionDiagram' G) from
      limit.cone (I.moduleCompletionDiagram G)) :=
  limit.isLimit (I.moduleCompletionDiagram G)

@[reassoc]
lemma powQuotientMap_powQuotientModuleCompletionIso_hom [IsLocallyNoetherian X] [G.IsQuasicoherent]
    (n : ℕ) :
    I.formalCompletionIdealSubsheaf.powQuotientMap (I.moduleCompletion' G) n ≫
      (I.powQuotientModuleCompletionIso G n).hom =
      (I.powQuotientModuleCompletionIso G (n + 1)).hom ≫
        (show I.moduleCompletionObj' G (n + 1) ⟶ I.moduleCompletionObj' G n from
          I.moduleCompletionMap G n) := by
  refine (cancel_epi
    (I.formalCompletionIdealSubsheaf.powQuotientπ (I.moduleCompletion' G) (n + 1))).mp ?_
  rw [IdealSubsheaf.powQuotientπ_powQuotientMap_assoc,
    powQuotientπ_powQuotientModuleCompletionIso_hom,
    powQuotientπ_powQuotientModuleCompletionIso_hom_assoc]
  exact (I.moduleCompletionπ_comp_moduleCompletionMap G n).symm


/-- The isomorphisms `F̂ / J ^ (n + 1) F̂ ≅ (F / I ^ (n + 1) F)|_Y` as a map of inverse systems. -/
def powQuotientDiagramToModuleCompletionDiagram [IsLocallyNoetherian X] [G.IsQuasicoherent] :
    I.formalCompletionIdealSubsheaf.powQuotientDiagram (I.moduleCompletion' G) ⟶
      I.moduleCompletionDiagram' G :=
  NatTrans.ofOpSequence (fun n => (I.powQuotientModuleCompletionIso G n).hom) (fun n => by
    rw [show (I.formalCompletionIdealSubsheaf.powQuotientDiagram (I.moduleCompletion' G)).map
        (homOfLE (n.le_add_right 1)).op =
        I.formalCompletionIdealSubsheaf.powQuotientMap (I.moduleCompletion' G) n from
      Functor.ofOpSequence_map_homOfLE_succ _ n,
      show (I.moduleCompletionDiagram' G).map (homOfLE (n.le_add_right 1)).op =
        I.moduleCompletionMap G n from Functor.ofOpSequence_map_homOfLE_succ _ n]
    exact I.powQuotientMap_powQuotientModuleCompletionIso_hom G n)

instance [IsLocallyNoetherian X] [G.IsQuasicoherent] :
    IsIso (I.powQuotientDiagramToModuleCompletionDiagram G) :=
  have : ∀ n : ℕᵒᵖ, IsIso ((I.powQuotientDiagramToModuleCompletionDiagram G).app n) :=
    fun ⟨n⟩ => inferInstanceAs (IsIso (I.powQuotientModuleCompletionIso G n).hom)
  NatIso.isIso_of_isIso_app _

/-- **`F̂` is complete for `J`**: `F̂ ⟶ lim_n F̂ / J ^ (n + 1) F̂` is an isomorphism, for `X`
locally Noetherian and `F` quasi-coherent. -/
theorem isIso_toLimitPowQuotient_moduleCompletion [IsLocallyNoetherian X] [G.IsQuasicoherent] :
    IsIso (I.formalCompletionIdealSubsheaf.toLimitPowQuotient (I.moduleCompletion' G)) := by
  let E := asIso (I.powQuotientDiagramToModuleCompletionDiagram G)
  have h1 : IsLimit ((Cone.postcompose E.hom).obj
      (I.formalCompletionIdealSubsheaf.powQuotientCone (I.moduleCompletion' G))) :=
    (I.isLimitModuleCompletionCone' G).ofIsoLimit (Cone.ext (Iso.refl _) fun ⟨n⟩ => by
      change I.moduleCompletionπ G n = 𝟙 _ ≫
        I.formalCompletionIdealSubsheaf.powQuotientπ (I.moduleCompletion' G) n ≫
          (I.powQuotientModuleCompletionIso G n).hom
      rw [Category.id_comp, powQuotientπ_powQuotientModuleCompletionIso_hom])
  have hc := (IsLimit.postcomposeHomEquiv E _) h1
  have : I.formalCompletionIdealSubsheaf.toLimitPowQuotient (I.moduleCompletion' G) =
      (hc.conePointUniqueUpToIso (limit.isLimit _)).hom := rfl
  rw [this]
  exact (hc.conePointUniqueUpToIso (limit.isLimit _)).isIso_hom

end QuasicoherentIdealSubsheaf

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J)

/-- **The completion does not depend on the ideal of definition.** For two ideals of definition
`J₁`, `J₂` of a Noetherian formal scheme `X` and an `𝒪_X`-module `F`, the canonical map
`F ⟶ lim_n F / J₁ ^ (n + 1) F` is an isomorphism iff `F ⟶ lim_n F / J₂ ^ (n + 1) F` is: by
Proposition 9.5(a) the two systems of powers are cofinal. -/
theorem isIso_toLimitPowQuotient_iff {J₁ J₂ : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
    (h₁ : IsIdealOfDefinition X J₁) (h₂ : IsIdealOfDefinition X J₂)
    (F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)) :
    IsIso (J₁.toLimitPowQuotient F) ↔ IsIso (J₂.toLimitPowQuotient F) := by
  obtain ⟨a, b, ha, hb, hab, hba⟩ := exists_pow_le_and_pow_le h₁ h₂
  refine IdealSubsheaf.isIso_toLimitPowQuotient_iff_of_cofinal (fun n => ?_) (fun n => ?_)
  · obtain ⟨k, hk⟩ := IdealSubsheaf.exists_pow_succ_le_pow_succ hb hba n
    exact ⟨k, IdealSubsheaf.smulSubmodule_mono F hk⟩
  · obtain ⟨k, hk⟩ := IdealSubsheaf.exists_pow_succ_le_pow_succ ha hab n
    exact ⟨k, IdealSubsheaf.smulSubmodule_mono F hk⟩

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

/-- The projection `𝒪_X ⟶ 𝒪_X / J` is locally surjective. -/
lemma isLocallySurjective_quotientRingCatSheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.toLocallyRingedSpace.carrier)
      h.quotientRingCatSheafHom.hom :=
  ⟨fun {_} s => J.isLocallySurjective_quotientπ.imageSieve_mem s⟩

/-- The pushforward along `𝒪_X ⟶ 𝒪_X / J` is faithful: it does not change the sections. -/
instance : h.quotientPushforward.Faithful where
  map_injective {M N} f g hfg := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    ext x
    exact congrArg (fun k => k.val.app V x) hfg

/-- The pushforward along `𝒪_X ⟶ 𝒪_X / J` is full: since `𝒪_X ⟶ 𝒪_X / J` is locally
surjective, an `𝒪_X`-linear map of `𝒪_X / J`-modules is `𝒪_X / J`-linear. -/
instance : h.quotientPushforward.Full where
  map_surjective {M N} f := by
    have := h.isLocallySurjective_quotientRingCatSheafHom
    exact ⟨⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective h.quotientRingCatSheafHom.hom
      (M₁ := (PresheafOfModules.pushforward₀ _ _).obj M.val)
      (M₂ := (PresheafOfModules.pushforward₀ _ _).obj N.val)
      (h.quotientPushforward.obj N).isSheaf).symm f.val⟩, rfl⟩

section Annihilates

variable {Q : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)}

/-- An `𝒪_X`-module `Q` killed by `J`, as a module on the scheme `(X, 𝒪_X / J)`. -/
def quotientModule (hQ : J.Annihilates Q) : h.quotientScheme.Modules :=
  hQ.quotientModule

/-- Pushing `quotientModule h hQ` forward to `X` gives back `Q`. -/
def quotientPushforwardQuotientModuleIso (hQ : J.Annihilates Q) :
    h.quotientPushforward.obj (h.quotientModule hQ) ≅ Q where
  hom := ⟨PresheafOfModules.homMk (𝟙 Q.val.presheaf) (fun V r m => hQ.quotientπ_smul V.unop r m)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 Q.val.presheaf)
    (fun V r m => (hQ.quotientπ_smul V.unop r m).symm)⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **Modules killed by `J` come from `(X, 𝒪_X / J)`**: for an `𝒪_X`-module `Q` killed by `J`, the
unit `Q ⟶ i_* i^* Q` of the adjunction along `𝒪_X ⟶ 𝒪_X / J` is an isomorphism. -/
theorem isIso_quotientAdjunction_unit_app (hQ : J.Annihilates Q) :
    IsIso (h.quotientAdjunction.unit.app Q) :=
  h.quotientAdjunction.isIso_unit_app_of_iso (h.quotientPushforwardQuotientModuleIso hQ).symm

end Annihilates

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

/-- **`F_n` pushed forward to `X` is `F / J ^ (n + 1) F`**: the map `toReduction h F n` is an
isomorphism, since `F / J ^ (n + 1) F` is killed by `J ^ (n + 1)`. -/
theorem isIso_toReduction (n : ℕ) : IsIso (h.toReduction F n) :=
  (h.pow_succ n).isIso_quotientAdjunction_unit_app
    (IdealSubsheaf.annihilates_cokernel_smulι (J ^ (n + 1)) F)

end IsIdealOfDefinition

end Hartshorne
