/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ArtinReesProZeroKernel
import Hartshorne.Cohomology.Semicontinuity.CoherentFiberDimension
import Hartshorne.Scheme.CartierDivisorSheaf

/-!
# The Artin–Rees kernel sheaves are pro-zero

Hartshorne, *Algebraic Geometry*, III.11, final Artin–Rees step in the proof of Theorem 11.1
(p. 279), sheaf form.

Let `X` be a Noetherian scheme, `E` a coherent `𝒪_X`-module, `R ⊆ E` a coherent submodule sheaf
and `I` a quasi-coherent ideal sheaf, given by its ideals `I(V) ⊆ Γ(X, V)` on affine opens. For a
submodule sheaf `N ⊆ E` the submodule sheaf `I ^ k N` (`powSmul`) consists of the sections lying,
near every point, in `I(V) ^ k N(V)` on an affine open `V`. The kernel sheaves are the cokernels

`K n = (R ∩ I ^ (n + 1) E) / I ^ (n + 1) R`

in the abelian category of `𝒪_X`-modules, with transition maps induced by inclusion
(`kernelSystem`).

* `exists_numerator_le_denominator`: for every `n` there is `n' ≥ n` with
  `R ∩ I ^ (n' + 1) E ⊆ I ^ (n + 1) R`;
* `kernelSystem_isProZero`: hence the transition map `K n' ⟶ K n` is zero;
* `isZero_limit_kernelSystem`: and the inverse limit of the kernel sheaves is zero.

The proof chooses, on each affine open `U`, an Artin–Rees index that works after every
localization of the module-level data `(Γ(X, U), I(U), Γ(E, U), R(U))`
(`ArtinReesKernel.exists_transition_localized_eq_zero`), takes the maximum over a finite affine
cover, and checks the inclusion on stalks, which are localizations of the sections over an affine
neighbourhood.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

namespace ArtinReesKernelSheaf

universe u

/-- A semilinear map sends `J ^ k • P` into `J' ^ k • P'` when it sends `J` into `J'` and `P`
into `P'`. -/
theorem pow_smul_map_mem {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module B N] (φ : A →+* B) (g : M →ₛₗ[φ] N) {J : Ideal A}
    {J' : Ideal B} (hJ : J.map φ ≤ J') {P : Submodule A M} {P' : Submodule B N}
    (hP : ∀ m ∈ P, g m ∈ P') (k : ℕ) {m : M} (hm : m ∈ J ^ k • P) : g m ∈ J' ^ k • P' := by
  refine Submodule.smul_induction_on hm (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [g.map_smulₛₗ]
    refine Submodule.smul_mem_smul ?_ (hP n hn)
    have : φ r ∈ (J ^ k).map φ := Ideal.mem_map_of_mem φ hr
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hJ k this
  · rw [map_add]
    exact add_mem hx hy

variable {X : Scheme.{u}} {E : X.Modules}

/-- The sections over `U` of a family of submodules, as a `Γ(X, U)`-submodule of `Γ(E, U)`. -/
abbrev sub (P : E.val.Submodule) (U : X.Opens) : Submodule Γ(X, U) Γ(E, U) := P.obj (op U)

/-- Restriction of sections of `E` along `V ≤ U`, as a semilinear map. -/
def res (E : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    Γ(E, U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(E, V) where
  toFun := E.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := Scheme.Modules.map_smul E (homOfLE h)

lemma res_apply (E : X.Modules) {U V : X.Opens} (h : V ≤ U) (s : Γ(E, U)) :
    res E h s = E.presheaf.map (homOfLE h).op s :=
  rfl

lemma res_res (E : X.Modules) {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(E, U)) :
    res E hWV (res E hVU s) = res E (hWV.trans hVU) s := by
  simp only [res_apply]
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

lemma res_mem (P : E.val.Submodule) {U V : X.Opens} (h : V ≤ U) {s : Γ(E, U)}
    (hs : s ∈ sub P U) : res E h s ∈ sub P V :=
  P.map _ hs

lemma exists_affine_le {U : X.Opens} {x : X} (hx : x ∈ U) :
    ∃ V : X.affineOpens, (V : X.Opens) ≤ U ∧ x ∈ (V : X.Opens) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨⟨V, hV⟩, hVU, hxV⟩

/-! ### Submodules of `E` defined by a local condition -/

/-- A family of submodules of the sections of `E` is *local* if a section that lies in the family
near every point lies in the family. -/
def IsLocal (N : E.val.Submodule) : Prop :=
  ∀ (U : X.Opens) (s : Γ(E, U)),
    (∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ res E hVU s ∈ sub N V) → s ∈ sub N U

/-- A local family of submodules of `E` is an `𝒪_X`-module. -/
def toModules (N : E.val.Submodule) (hN : IsLocal N) : X.Modules :=
  ⟨N.toPresheafOfModules, Scheme.isSheaf_submodule_of_local N hN⟩

/-- The inclusion between two local families of submodules, as a morphism of `𝒪_X`-modules. -/
def inclusion {N₁ N₂ : E.val.Submodule} (h₁ : IsLocal N₁) (h₂ : IsLocal N₂) (h : N₁ ≤ N₂) :
    toModules N₁ h₁ ⟶ toModules N₂ h₂ :=
  ⟨PresheafOfModules.Submodule.homOfLE h⟩

lemma inclusion_comp {N₁ N₂ N₃ : E.val.Submodule} (h₁ : IsLocal N₁) (h₂ : IsLocal N₂)
    (h₃ : IsLocal N₃) (h : N₁ ≤ N₂) (h' : N₂ ≤ N₃) :
    inclusion h₁ h₂ h ≫ inclusion h₂ h₃ h' = inclusion h₁ h₃ (h.trans h') :=
  rfl

lemma inclusion_refl {N : E.val.Submodule} (h : IsLocal N) :
    inclusion h h (le_refl N) = 𝟙 _ :=
  rfl

lemma isLocal_inf {N₁ N₂ : E.val.Submodule} (h₁ : IsLocal N₁) (h₂ : IsLocal N₂) :
    IsLocal (N₁ ⊓ N₂) := fun U s hs =>
  ⟨h₁ U s fun x hx => (hs x hx).imp fun _ ⟨hVU, hxV, h⟩ => ⟨hVU, hxV, h.1⟩,
    h₂ U s fun x hx => (hs x hx).imp fun _ ⟨hVU, hxV, h⟩ => ⟨hVU, hxV, h.2⟩⟩

/-- A family of submodules of `E` whose associated presheaf is a sheaf is local. -/
theorem isLocal_of_isSheaf (N : E.val.Submodule)
    (hN : Presheaf.IsSheaf (Opens.grothendieckTopology X) N.toPresheafOfModules.presheaf) :
    IsLocal N := by
  intro U s hs
  choose V hVU hxV hV using hs
  let ι := {x : X // x ∈ U}
  let W : ι → X.Opens := fun x => V x.1 x.2
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨N.toPresheafOfModules.presheaf, hN⟩
  let M' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨E.val.presheaf, E.isSheaf⟩
  have hcover : U ≤ iSup W := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩
  let sf : ∀ i : ι, ToType (F.1.obj (op (W i))) := fun i => ⟨_, hV i.1 i.2⟩
  have hsf : TopCat.Presheaf.IsCompatible F.1 W sf := by
    intro i j
    apply Subtype.ext
    change res E _ (res E _ s) = res E _ (res E _ s)
    rw [res_res, res_res]
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' W U (fun i => CategoryTheory.homOfLE (hVU _ _))
    hcover sf hsf
  have hts : (show ↥(N.obj (op U)) from t).1 = s := by
    apply M'.eq_of_locally_eq' W U (fun i => CategoryTheory.homOfLE (hVU _ _)) hcover
    intro i
    have := congrArg Subtype.val (ht i)
    exact this
  change s ∈ N.obj (op U)
  rw [← hts]
  exact (show ↥(N.obj (op U)) from t).2

/-- A family of submodules of the sections of `E` over affine opens, stable under restriction
between affine opens. -/
structure AffineFamily (E : X.Modules) where
  /-- the submodule over an affine open -/
  obj (V : X.affineOpens) : Submodule Γ(X, V) Γ(E, V)
  res_mem {V W : X.affineOpens} (h : (W : X.Opens) ≤ V) {s : Γ(E, V)} :
    s ∈ obj V → res E h s ∈ obj W

namespace AffineFamily

variable (P : AffineFamily E)

/-- The sections lying in `P` near every point, on affine opens. -/
def LocallyIn {U : X.Opens} (s : Γ(E, U)) : Prop :=
  ∀ x ∈ U, ∃ (V : X.affineOpens) (hVU : (V : X.Opens) ≤ U), x ∈ (V : X.Opens) ∧
    res E hVU s ∈ P.obj V

lemma locallyIn_res {U U' : X.Opens} (h : U' ≤ U) {s : Γ(E, U)} (hs : P.LocallyIn s) :
    P.LocallyIn (res E h s) := by
  intro x hx
  obtain ⟨V, hVU, hxV, hV⟩ := hs x (h hx)
  obtain ⟨W, hW, hxW⟩ := exists_affine_le (U := (V : X.Opens) ⊓ U') ⟨hxV, hx⟩
  refine ⟨W, hW.trans inf_le_right, hxW, ?_⟩
  rw [res_res]
  have := P.res_mem (hW.trans inf_le_left) hV
  rwa [res_res] at this

lemma locallyIn_zero (U : X.Opens) : P.LocallyIn (0 : Γ(E, U)) := fun x hx => by
  obtain ⟨V, hVU, hxV⟩ := exists_affine_le hx
  exact ⟨V, hVU, hxV, by rw [map_zero]; exact zero_mem _⟩

lemma locallyIn_add {U : X.Opens} {s t : Γ(E, U)} (hs : P.LocallyIn s) (ht : P.LocallyIn t) :
    P.LocallyIn (s + t) := fun x hx => by
  obtain ⟨V₁, hV₁, hxV₁, h₁⟩ := hs x hx
  obtain ⟨V₂, hV₂, hxV₂, h₂⟩ := ht x hx
  obtain ⟨W, hW, hxW⟩ := exists_affine_le (U := (V₁ : X.Opens) ⊓ V₂) ⟨hxV₁, hxV₂⟩
  refine ⟨W, hW.trans (inf_le_left.trans hV₁), hxW, ?_⟩
  rw [map_add]
  refine add_mem ?_ ?_
  · have := P.res_mem (hW.trans inf_le_left) h₁
    rwa [res_res] at this
  · have := P.res_mem (hW.trans inf_le_right) h₂
    rwa [res_res] at this

lemma locallyIn_smul {U : X.Opens} (r : Γ(X, U)) {s : Γ(E, U)} (hs : P.LocallyIn s) :
    P.LocallyIn (r • s) := fun x hx => by
  obtain ⟨V, hVU, hxV, hV⟩ := hs x hx
  refine ⟨V, hVU, hxV, ?_⟩
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ hV

/-- The submodule of sections of `E` lying in `P` near every point: the sheaf generated by
`P`. -/
def closure : E.val.Submodule where
  obj U :=
    { carrier := {s | P.LocallyIn (U := U.unop) s}
      zero_mem' := P.locallyIn_zero U.unop
      add_mem' := fun hs ht => P.locallyIn_add hs ht
      smul_mem' := fun r _ hs => P.locallyIn_smul (U := U.unop) r hs }
  map f _ hs := P.locallyIn_res (leOfHom f.unop) hs

lemma mem_closure_iff {U : X.Opens} (s : Γ(E, U)) : s ∈ sub P.closure U ↔ P.LocallyIn s :=
  Iff.rfl

lemma isLocal_closure : IsLocal P.closure := by
  intro U s hs x hx
  obtain ⟨V, hVU, hxV, hV⟩ := hs x hx
  obtain ⟨W, hWV, hxW, hW⟩ := hV x hxV
  exact ⟨W, hWV.trans hVU, hxW, by rwa [res_res] at hW⟩

lemma closure_mono {P Q : AffineFamily E} (h : ∀ V, P.obj V ≤ Q.obj V) :
    P.closure ≤ Q.closure := fun _ _ hs x hx =>
  (hs x hx).imp fun V ⟨hVU, hxV, hV⟩ => ⟨hVU, hxV, h V hV⟩

lemma closure_le {N : E.val.Submodule} (hN : IsLocal N) (h : ∀ V, P.obj V ≤ sub N V) :
    P.closure ≤ N := fun U s hs =>
  hN U.unop s fun x hx => by
    obtain ⟨V, hVU, hxV, hV⟩ := hs x hx
    exact ⟨(V : X.Opens), hVU, hxV, h V hV⟩

end AffineFamily

/-! ### Products with powers of an ideal sheaf -/

/-- `V ↦ I(V) ^ k • N(V)` on affine opens. -/
def powSmulFamily (I : X.IdealSheafData) (k : ℕ) (N : E.val.Submodule) : AffineFamily E where
  obj V := I.ideal V ^ k • sub N V
  res_mem {V W} h _ hs :=
    pow_smul_map_mem _ (res E h) (J := I.ideal V) (J' := I.ideal W) (I.map_ideal h).le
      (fun _ hm => res_mem N h hm) k hs

/-- The submodule `I ^ k · N` of `E`: sections lying, near every point, in `I(V) ^ k • N(V)` on
an affine open `V`. -/
def powSmul (I : X.IdealSheafData) (k : ℕ) (N : E.val.Submodule) : E.val.Submodule :=
  (powSmulFamily I k N).closure

lemma isLocal_powSmul (I : X.IdealSheafData) (k : ℕ) (N : E.val.Submodule) :
    IsLocal (powSmul I k N) :=
  AffineFamily.isLocal_closure _

lemma powSmul_antitone (I : X.IdealSheafData) (N : E.val.Submodule) {k l : ℕ} (h : k ≤ l) :
    powSmul I l N ≤ powSmul I k N :=
  AffineFamily.closure_mono fun _ => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

/-- The numerator `R ∩ I ^ (n + 1) E` of the `n`-th Artin–Rees kernel sheaf. -/
def numerator (I : X.IdealSheafData) (R : E.val.Submodule) (n : ℕ) : E.val.Submodule :=
  R ⊓ powSmul I (n + 1) ⊤

/-- The denominator `I ^ (n + 1) R` of the `n`-th Artin–Rees kernel sheaf. -/
def denominator (I : X.IdealSheafData) (R : E.val.Submodule) (n : ℕ) : E.val.Submodule :=
  powSmul I (n + 1) R

variable (I : X.IdealSheafData) {R : E.val.Submodule} (hR : IsLocal R)

include hR in
lemma isLocal_numerator (n : ℕ) : IsLocal (numerator I R n) :=
  isLocal_inf hR (isLocal_powSmul I _ _)

lemma isLocal_denominator (n : ℕ) : IsLocal (denominator I R n) :=
  isLocal_powSmul I _ _

include hR in
lemma denominator_le_numerator (n : ℕ) : denominator I R n ≤ numerator I R n :=
  le_inf ((powSmulFamily I (n + 1) R).closure_le hR fun _ => Submodule.smul_le_right)
    (AffineFamily.closure_mono fun _ => Submodule.smul_mono le_rfl le_top)

lemma numerator_antitone {n m : ℕ} (h : n ≤ m) : numerator I R m ≤ numerator I R n :=
  inf_le_inf_left R (powSmul_antitone I ⊤ (Nat.succ_le_succ h))

lemma denominator_antitone {n m : ℕ} (h : n ≤ m) : denominator I R m ≤ denominator I R n :=
  powSmul_antitone I R (Nat.succ_le_succ h)

/-- The inclusion `I ^ (n + 1) R ⟶ R ∩ I ^ (n + 1) E` of `𝒪_X`-modules. -/
def denominatorToNumerator (n : ℕ) :
    toModules (denominator I R n) (isLocal_denominator I n) ⟶
      toModules (numerator I R n) (isLocal_numerator I hR n) :=
  inclusion _ _ (denominator_le_numerator I hR n)

lemma inclusion_eq_denominatorToNumerator (n : ℕ) :
    inclusion (isLocal_denominator I n) (isLocal_numerator I hR n)
      (denominator_le_numerator I hR n) = denominatorToNumerator I hR n :=
  rfl

/-- The `n`-th Artin–Rees kernel sheaf `(R ∩ I ^ (n + 1) E) / I ^ (n + 1) R`. -/
abbrev kernelSheaf (n : ℕ) : X.Modules :=
  cokernel (denominatorToNumerator I hR n)

/-- The transition map `K m ⟶ K n` for `n ≤ m`, induced by inclusion. -/
def transition {n m : ℕ} (h : n ≤ m) : kernelSheaf I hR m ⟶ kernelSheaf I hR n :=
  cokernel.desc _ (inclusion (isLocal_numerator I hR m) (isLocal_numerator I hR n)
      (numerator_antitone I h) ≫ cokernel.π (denominatorToNumerator I hR n)) (by
    rw [denominatorToNumerator, ← Category.assoc, inclusion_comp,
      ← inclusion_comp _ (isLocal_denominator I n) _ (denominator_antitone I h)
        (denominator_le_numerator I hR n), Category.assoc, inclusion_eq_denominatorToNumerator I hR n,
      cokernel.condition, Limits.comp_zero])

@[reassoc (attr := simp)]
lemma π_transition {n m : ℕ} (h : n ≤ m) :
    cokernel.π _ ≫ transition I hR h =
      inclusion (isLocal_numerator I hR m) (isLocal_numerator I hR n) (numerator_antitone I h) ≫
        cokernel.π (denominatorToNumerator I hR n) :=
  cokernel.π_desc _ _ _

/-- The Artin–Rees kernel sheaves as an inverse system of `𝒪_X`-modules. -/
def kernelSystem : ℕᵒᵖ ⥤ X.Modules where
  obj n := kernelSheaf I hR n.unop
  map f := transition I hR (leOfHom f.unop)
  map_id n := by
    apply coequalizer.hom_ext
    rw [π_transition, inclusion_refl, Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply coequalizer.hom_ext
    rw [π_transition, π_transition_assoc, π_transition, ← Category.assoc, inclusion_comp]

/-- If `R ∩ I ^ (m + 1) E ⊆ I ^ (n + 1) R`, the transition map `K m ⟶ K n` is zero. -/
lemma transition_eq_zero {n m : ℕ} (h : n ≤ m) (hle : numerator I R m ≤ denominator I R n) :
    transition I hR h = 0 := by
  apply coequalizer.hom_ext
  rw [π_transition, Limits.comp_zero, ← inclusion_comp _ (isLocal_denominator I n) _ hle
    (denominator_le_numerator I hR n), Category.assoc, inclusion_eq_denominatorToNumerator I hR n,
    cokernel.condition, Limits.comp_zero]

/-! ### Stalks on an affine chart -/

section Stalks

open FiberDimAux

attribute [local instance] FiberDimAux.stalkModuleSections FiberDimAux.isScalarTower_stalk

/-- Multiplying a germ by (the germ of) a section on a neighbourhood of the point. -/
lemma germ_smul_germ (F : X.Modules) {U U₀ : X.Opens} {x : X} (hxU : x ∈ U) (hx₀ : x ∈ U₀)
    (c : Γ(X, U)) (m : Γ(F, U₀)) :
    X.presheaf.germ U x hxU c • F.presheaf.germ U₀ x hx₀ m =
      F.presheaf.germ (U ⊓ U₀) x (show x ∈ U ⊓ U₀ from ⟨hxU, hx₀⟩)
        (X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : U ⊓ U₀ ≤ U)).op c •
          F.presheaf.map (CategoryTheory.homOfLE (inf_le_right : U ⊓ U₀ ≤ U₀)).op m) := by
  rw [schemeModules_germ_smul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

/-- On an affine chart `U ∋ x`, the ideal `I(V)` of any affine open `V ∋ x` generates in the
local ring at `x` the same ideal as `I(U)`. -/
lemma map_germ_ideal_eq (I : X.IdealSheafData) (U V : X.affineOpens) {x : X}
    (hxU : x ∈ (U : X.Opens)) (hxV : x ∈ (V : X.Opens)) :
    (I.ideal V).map (X.presheaf.germ (V : X.Opens) x hxV).hom =
      (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hxU).hom := by
  obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hxU
  let D : X.affineOpens := X.affineBasicOpen g
  have hDV : D ≤ V := hgV
  have hDU : D ≤ U := X.basicOpen_le g
  have hxD : x ∈ (D : X.Opens) := hxg
  have h₁ : (I.ideal V).map (X.presheaf.germ (V : X.Opens) x hxV).hom =
      (I.ideal D).map (X.presheaf.germ (D : X.Opens) x hxD).hom := by
    rw [← I.map_ideal hDV, Ideal.map_map, ← CommRingCat.hom_comp]
    erw [X.presheaf.germ_res]
  have h₂ : (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hxU).hom =
      (I.ideal D).map (X.presheaf.germ (D : X.Opens) x hxD).hom := by
    rw [← I.map_ideal hDU, Ideal.map_map, ← CommRingCat.hom_comp]
    erw [X.presheaf.germ_res]
  rw [h₁, h₂]

lemma mem_basicOpen_of_mem_primeCompl (U : X.affineOpens) {x : X} (hxU : x ∈ (U : X.Opens))
    {c : Γ(X, (U : X.Opens))} (hc : c ∈ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) :
    x ∈ X.basicOpen c := by
  let _ : Algebra Γ(X, (U : X.Opens)) (X.presheaf.stalk x) :=
    (X.presheaf.germ (U : X.Opens) x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  exact (X.mem_basicOpen' c ⟨x, hxU⟩).mpr
    ((IsLocalization.AtPrime.isUnit_to_map_iff
      (X.presheaf.stalk x) _ c).mpr hc)

/-- **Germs of a quasi-coherent submodule sheaf.** Let `R ⊆ E` be a submodule sheaf whose
restriction to the affine open `U` is quasi-coherent, and let `x ∈ U`. The germ at `x` of a
section of `R` over any neighbourhood of `x` is a fraction `r / c` with `r ∈ R(U)` and
`c ∈ Γ(X, U)` not vanishing at `x`. -/
lemma exists_germ_eq_smul (R : E.val.Submodule)
    (hRs : Presheaf.IsSheaf (Opens.grothendieckTopology X) R.toPresheafOfModules.presheaf)
    (U : X.affineOpens)
    (hiso : IsIso (specRestriction (⟨R.toPresheafOfModules, hRs⟩ : X.Modules) U).fromTildeΓ)
    {x : X} (hxU : x ∈ (U : X.Opens)) {U₀ : X.Opens} (hx₀ : x ∈ U₀) {s : Γ(E, U₀)}
    (hs : s ∈ sub R U₀) :
    ∃ r ∈ sub R U, ∃ c : Γ(X, (U : X.Opens)), x ∈ X.basicOpen c ∧
      E.presheaf.germ U x hxU r = X.presheaf.germ U x hxU c • E.presheaf.germ U₀ x hx₀ s := by
  let R' : X.Modules := ⟨R.toPresheafOfModules, hRs⟩
  have hloc := isLocalizedModule_germₗ R' U.2 hiso ⟨x, hxU⟩
  have := U.2.isLocalization_stalk ⟨x, hxU⟩
  let s' : Γ(R', U₀) := (⟨s, hs⟩ : ↥(R.obj (op U₀)))
  obtain ⟨⟨r, c⟩, hc⟩ := IsLocalizedModule.surj (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (germₗ R' ⟨x, hxU⟩) (R'.presheaf.germ U₀ x hx₀ s')
  change X.presheaf.germ U x hxU c • R'.presheaf.germ U₀ x hx₀ s' = R'.presheaf.germ U x hxU r
    at hc
  rw [germ_smul_germ] at hc
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x _ hxU _ r hc
  have hW' := congrArg (fun z : ↥(R.obj (op W)) => z.1) hW
  change E.presheaf.map iU.op
    (X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : (U : X.Opens) ⊓ U₀ ≤ U)).op c •
      E.presheaf.map (CategoryTheory.homOfLE (inf_le_right : (U : X.Opens) ⊓ U₀ ≤ U₀)).op s) =
    E.presheaf.map iV.op (r.1 : Γ(E, (U : X.Opens))) at hW'
  refine ⟨r.1, r.2, c, mem_basicOpen_of_mem_primeCompl U hxU c.2, ?_⟩
  rw [germ_smul_germ, ← TopCat.Presheaf.germ_res_apply E.presheaf iU x hxW, hW']
  exact (TopCat.Presheaf.germ_res_apply E.presheaf iV x hxW (r.1 : Γ(E, (U : X.Opens)))).symm

/-- The germ map `Γ(E, V) → E_x`, semilinear over the germ map of rings. -/
def germₛₗ (F : X.Modules) (V : X.Opens) (x : X) (hx : x ∈ V) :
    Γ(F, V) →ₛₗ[(X.presheaf.germ V x hx).hom] F.presheaf.stalk x where
  toFun := F.presheaf.germ V x hx
  map_add' := map_add _
  map_smul' := schemeModules_germ_smul F V x hx

lemma isUnit_res_of_le_basicOpen {U W : X.Opens} (c : Γ(X, U)) (hWU : W ≤ U)
    (hW : W ≤ X.basicOpen c) : IsUnit (X.presheaf.map (CategoryTheory.homOfLE hWU).op c) := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro y hy
  obtain ⟨hyU, hu⟩ := (X.mem_basicOpen'' c y).mp (hW hy)
  rw [TopCat.Presheaf.germ_res_apply]
  exact hu

/-- **The local step.** Let `U` be an affine chart on which `E` and `R` are quasi-coherent and
on which the Artin–Rees index `m` works for `n` after every localization. If `s ∈ R(U₀)` lies in
`I(V) ^ (m + 1) E(V)` on an affine neighbourhood `V ⊆ U₀` of a point `x ∈ U`, then `s` lies in
`I(W) ^ (n + 1) R(W)` on some affine neighbourhood `W ⊆ U₀` of `x`. -/
lemma local_step (I : X.IdealSheafData) (R : E.val.Submodule)
    (hRs : Presheaf.IsSheaf (Opens.grothendieckTopology X) R.toPresheafOfModules.presheaf)
    {U : X.Opens} (hU : IsAffineOpen U) (hisoE : IsIso (E.restrict hU.fromSpec).fromTildeΓ)
    (hisoR : IsIso (specRestriction (⟨R.toPresheafOfModules, hRs⟩ : X.Modules) ⟨U, hU⟩).fromTildeΓ)
    {n m : ℕ} (h : n ≤ m)
    (hz : ∀ (p : Submonoid Γ(X, U)) (A' : Type u) [CommRing A'] [Algebra Γ(X, U) A']
      [IsLocalization p A'] (E' : Type u) [AddCommGroup E'] [Module Γ(X, U) E'] [Module A' E']
      [IsScalarTower Γ(X, U) A' E'] (f : Γ(E, U) →ₗ[Γ(X, U)] E') [IsLocalizedModule p f],
      ArtinReesKernel.transition ((I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) A'))
        ((sub R U).localized' A' p f) h = 0)
    (x : U) {U₀ : X.Opens} (hx₀ : (x : X) ∈ U₀) {s : Γ(E, U₀)} (hsR : s ∈ sub R U₀)
    {V : X.affineOpens} (hV₀ : (V : X.Opens) ≤ U₀) (hxV : (x : X) ∈ (V : X.Opens))
    (hsV : res E hV₀ s ∈
      I.ideal V ^ (m + 1) • (⊤ : Submodule Γ(X, (V : X.Opens)) Γ(E, (V : X.Opens)))) :
    ∃ (W : X.affineOpens) (hW : (W : X.Opens) ≤ U₀), (x : X) ∈ (W : X.Opens) ∧
      res E hW s ∈ I.ideal W ^ (n + 1) • sub R W := by
  have hloc := isLocalizedModule_germₗ E hU hisoE x
  have hlocR := hU.isLocalization_stalk x
  have hz' := hz (hU.primeIdealOf x).asIdeal.primeCompl (X.presheaf.stalk (x : X))
    (E.presheaf.stalk (x : X)) (germₗ E x)
  rw [ArtinReesKernel.transition_eq_zero_iff, ← ArtinReesKernel.localized'_numerator,
    ← ArtinReesKernel.localized'_pow_smul] at hz'
  have hg : E.presheaf.germ U₀ x hx₀ s ∈
      (ArtinReesKernel.numerator (I.ideal ⟨U, hU⟩) (sub R U) m).localized'
        (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal.primeCompl (germₗ E x) := by
    rw [ArtinReesKernel.localized'_numerator]
    refine ⟨?_, ?_⟩
    · obtain ⟨r, hr, c, hc, heq⟩ := exists_germ_eq_smul R hRs ⟨U, hU⟩ hisoR x.2 hx₀ hsR
      have hcp : c ∈ (hU.primeIdealOf x).asIdeal.primeCompl :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (x : X)) _ c).mp
          ((X.mem_basicOpen' c x).mp hc)
      refine ⟨r, hr, ⟨c, hcp⟩, ?_⟩
      rw [IsLocalizedModule.mk'_eq_iff]
      exact heq
    · rw [← TopCat.Presheaf.germ_res_apply E.presheaf (CategoryTheory.homOfLE hV₀) x hxV]
      exact pow_smul_map_mem (X.presheaf.germ (V : X.Opens) x hxV).hom
        (germₛₗ E (V : X.Opens) x hxV) (map_germ_ideal_eq I ⟨U, hU⟩ V x.2 hxV).le
        (fun _ _ => Submodule.mem_top) (m + 1) hsV
  obtain ⟨t, ht, c, hct⟩ := hz' hg
  rw [IsLocalizedModule.mk'_eq_iff] at hct
  change E.presheaf.germ U x x.2 t = X.presheaf.germ U x x.2 (c : Γ(X, U)) •
    E.presheaf.germ U₀ x hx₀ s at hct
  rw [germ_smul_germ] at hct
  obtain ⟨W', hxW', iU, iV, hW'⟩ := TopCat.Presheaf.germ_eq _ x x.2 _ t _ hct
  have hcx : (x : X) ∈ X.basicOpen (c : Γ(X, U)) :=
    mem_basicOpen_of_mem_primeCompl ⟨U, hU⟩ x.2 c.2
  obtain ⟨W, hW, hxW⟩ := exists_affine_le (U := W' ⊓ X.basicOpen (c : Γ(X, U))) ⟨hxW', hcx⟩
  have hWW' : (W : X.Opens) ≤ W' := hW.trans inf_le_left
  have hWU : (W : X.Opens) ≤ U := hWW'.trans iU.le
  have hWU₀ : (W : X.Opens) ≤ U₀ := hWW'.trans (iV.le.trans inf_le_right)
  refine ⟨W, hWU₀, hxW, ?_⟩
  obtain ⟨u, hu⟩ := isUnit_res_of_le_basicOpen (c : Γ(X, U)) hWU (hW.trans inf_le_right)
  have heq : res E hWU t =
      X.presheaf.map (CategoryTheory.homOfLE hWU).op (c : Γ(X, U)) • res E hWU₀ s := by
    change res E iU.le t = res E iV.le
      (X.presheaf.map (CategoryTheory.homOfLE (inf_le_left : U ⊓ U₀ ≤ U)).op (c : Γ(X, U)) •
        res E (inf_le_right : U ⊓ U₀ ≤ U₀) s) at hW'
    have := congrArg (res E hWW') hW'
    rw [res_res, res_res, LinearMap.map_smulₛₗ, res_res] at this
    rw [this]
    congr 1
    change (X.presheaf.map _ ≫ X.presheaf.map _) _ = _
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  have hres : res E hWU t ∈ I.ideal W ^ (n + 1) • sub R W :=
    pow_smul_map_mem _ (res E hWU) (I.map_ideal (U := W) (V := ⟨U, hU⟩) hWU).le
      (fun _ hm => res_mem R hWU hm) (n + 1) ht
  have hs : res E hWU₀ s = ((u⁻¹ : (Γ(X, (W : X.Opens)))ˣ) : Γ(X, (W : X.Opens))) •
      res E hWU t := by
    rw [heq, smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [hs]
  exact Submodule.smul_mem _ _ hres

end Stalks

/-! ### The sheaf version -/

/-- An inverse system in which every object is eventually mapped to zero has a zero limit. -/
theorem isZero_of_isLimit_of_isProZero {C : Type*} [Category C] [HasZeroMorphisms C]
    (F : ℕᵒᵖ ⥤ C)
    (hF : ∀ n : ℕ, ∃ (n' : ℕ) (h : n ≤ n'), F.map (CategoryTheory.homOfLE h).op = 0)
    {c : Cone F} (hc : IsLimit c) : IsZero c.pt := by
  rw [IsZero.iff_id_eq_zero]
  apply hc.hom_ext
  rintro ⟨j⟩
  obtain ⟨n', h, hz⟩ := hF j
  rw [Limits.zero_comp, Category.id_comp, ← c.w (CategoryTheory.homOfLE h).op, hz,
    Limits.comp_zero]

section Noetherian

variable [IsNoetherian X]

/-- **Artin–Rees for coherent sheaves.** Let `X` be a Noetherian scheme, `E` a coherent
`𝒪_X`-module, `R ⊆ E` a coherent submodule sheaf and `I` a quasi-coherent ideal sheaf. For
every `n` there is `n' ≥ n` with `R ∩ I ^ (n' + 1) E ⊆ I ^ (n + 1) R`. -/
theorem exists_numerator_le_denominator (hE : IsCoherent E) (I : X.IdealSheafData)
    (R : E.val.Submodule)
    (hRs : Presheaf.IsSheaf (Opens.grothendieckTopology X) R.toPresheafOfModules.presheaf)
    (hR : IsCoherent (⟨R.toPresheafOfModules, hRs⟩ : X.Modules)) (n : ℕ) :
    ∃ n', n ≤ n' ∧ numerator I R n' ≤ denominator I R n := by
  have hEU := forall_affine_finite_of_isCoherent E hE
  have hRU := forall_affine_finite_of_isCoherent _ hR
  have key : ∀ U : X.affineOpens, ∃ (m : ℕ) (h : n ≤ m),
      ∀ (p : Submonoid Γ(X, (U : X.Opens))) (A' : Type u) [CommRing A']
        [Algebra Γ(X, (U : X.Opens)) A'] [IsLocalization p A'] (E' : Type u) [AddCommGroup E']
        [Module Γ(X, (U : X.Opens)) E'] [Module A' E'] [IsScalarTower Γ(X, (U : X.Opens)) A' E']
        (f : Γ(E, (U : X.Opens)) →ₗ[Γ(X, (U : X.Opens))] E') [IsLocalizedModule p f],
        ArtinReesKernel.transition ((I.ideal U).map (algebraMap Γ(X, (U : X.Opens)) A'))
          ((sub R U).localized' A' p f) h = 0 := by
    intro U
    have := (hEU U).1
    have : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
    exact ArtinReesKernel.exists_transition_localized_eq_zero (I.ideal U) (sub R U) n
  choose N hnN hN using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => (U : X.Opens).isOpen)
    (fun x _ => by
      obtain ⟨V, -, hxV⟩ := exists_affine_le (U := ⊤) (x := x) trivial
      exact Set.mem_iUnion.mpr ⟨V, hxV⟩)
  refine ⟨n ⊔ t.sup N, le_sup_left, ?_⟩
  rintro U₀ s ⟨hsR, hs⟩ x hx
  obtain ⟨V, hV₀, hxV, hsV⟩ := hs x hx
  obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  have hle : N U ≤ n ⊔ t.sup N := le_sup_of_le_right (Finset.le_sup hUt)
  refine local_step I R hRs U.2 (hEU U).2 (hRU U).2 (le_sup_left : n ≤ n ⊔ t.sup N) ?_
    ⟨x, hxU⟩ hx hsR hV₀ hxV hsV
  intro p A' _ _ _ E' _ _ _ _ f _
  have := hN U p A' E' f
  rw [ArtinReesKernel.transition_eq_zero_iff] at this ⊢
  exact (ArtinReesKernel.numerator_antitone _ _ hle).trans this

/-- **The Artin–Rees kernel sheaves are pro-zero.** Let `X` be a Noetherian scheme, `E` a
coherent `𝒪_X`-module, `R ⊆ E` a coherent submodule sheaf and `I` a quasi-coherent ideal sheaf,
and let `K n = (R ∩ I ^ (n + 1) E) / I ^ (n + 1) R`. For every `n` there is `n' ≥ n` such that
the transition map `K n' ⟶ K n` is zero. -/
theorem kernelSystem_isProZero (hE : IsCoherent E) (I : X.IdealSheafData) (R : E.val.Submodule)
    (hRs : Presheaf.IsSheaf (Opens.grothendieckTopology X) R.toPresheafOfModules.presheaf)
    (hR : IsCoherent (⟨R.toPresheafOfModules, hRs⟩ : X.Modules)) (n : ℕ) :
    ∃ (n' : ℕ) (h : n ≤ n'),
      (kernelSystem I (isLocal_of_isSheaf R hRs)).map (CategoryTheory.homOfLE h).op = 0 := by
  obtain ⟨n', h, hle⟩ := exists_numerator_le_denominator hE I R hRs hR n
  exact ⟨n', h, transition_eq_zero I _ h hle⟩

/-- **The inverse limit of the Artin–Rees kernel sheaves vanishes.** -/
theorem isZero_limit_kernelSystem (hE : IsCoherent E) (I : X.IdealSheafData)
    (R : E.val.Submodule)
    (hRs : Presheaf.IsSheaf (Opens.grothendieckTopology X) R.toPresheafOfModules.presheaf)
    (hR : IsCoherent (⟨R.toPresheafOfModules, hRs⟩ : X.Modules)) :
    IsZero (limit (kernelSystem I (isLocal_of_isSheaf R hRs))) :=
  isZero_of_isLimit_of_isProZero _ (kernelSystem_isProZero hE I R hRs hR) (limit.isLimit _)

end Noetherian

end ArtinReesKernelSheaf
end Hartshorne
