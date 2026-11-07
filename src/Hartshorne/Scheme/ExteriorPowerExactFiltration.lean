/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ExteriorPowerFiltrationAlgebra
import Hartshorne.Scheme.SheafAlgebraOperations
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Exterior powers of a short exact sequence of locally free sheaves

Hartshorne, *Algebraic Geometry*, II, Exercise 5.16(d) (p. 128).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
open scoped TensorProduct

namespace Hartshorne

namespace ExteriorPowerExactFiltration

open SheafTensorOperations

section Semilinear

variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* B}
  {M M₁ M₂ N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₂] [Module A M₂] [AddCommGroup N] [Module B N]

/-- Semilinear maps out of an exterior power agreeing on wedges of vectors are equal. -/
lemma exteriorPower_semilinear_ext {n : ℕ} {f g : ⋀[A]^n M →ₛₗ[σ] N}
    (h : ∀ m, f (exteriorPower.ιMulti A n m) = g (exteriorPower.ιMulti A n m)) : f = g := by
  ext x
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨m, rfl⟩ := hy; exact h m
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

/-- Semilinear maps out of a tensor product of exterior powers agreeing on tensors of wedges of
vectors are equal. -/
lemma tensor_exteriorPower_semilinear_ext {a b : ℕ}
    {f g : ⋀[A]^a M₁ ⊗[A] ⋀[A]^b M₂ →ₛₗ[σ] N}
    (h : ∀ m₁ m₂, f (exteriorPower.ιMulti A a m₁ ⊗ₜ exteriorPower.ιMulti A b m₂) =
      g (exteriorPower.ιMulti A a m₁ ⊗ₜ exteriorPower.ιMulti A b m₂)) : f = g := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp [hz, hz']
  | tmul x y =>
    have hy : ∀ m₁, f.comp ((TensorProduct.mk A _ _) (exteriorPower.ιMulti A a m₁)) =
        g.comp ((TensorProduct.mk A _ _) (exteriorPower.ιMulti A a m₁)) := fun m₁ =>
      exteriorPower_semilinear_ext fun m₂ => h m₁ m₂
    have hx : f.comp ((TensorProduct.mk A _ _).flip y) = g.comp ((TensorProduct.mk A _ _).flip y) :=
      exteriorPower_semilinear_ext fun m₁ => LinearMap.congr_fun (hy m₁) y
    exact LinearMap.congr_fun hx x

end Semilinear

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

section PresheafConstructions

variable {L M T : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)}

/-- A morphism of presheaves of modules given by linear maps on sections compatible with the
(semilinear) restriction maps. -/
noncomputable def homOfLinear
    (app : ∀ U, M.obj U →ₗ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U] T.obj U)
    (nat : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (x : M.obj U), app V (M.map i x) =
      T.map i (app U x)) : M ⟶ T where
  app U := ModuleCat.ofHom (app U)
  naturality i := by
    ext x
    exact nat i x

@[simp]
lemma homOfLinear_app_apply
    (app : ∀ U, M.obj U →ₗ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U] T.obj U)
    (nat : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (x : M.obj U), app V (M.map i x) =
      T.map i (app U x)) (U : (Opens X)ᵒᵖ) (x : M.obj U) :
    (homOfLinear app nat).app U x = app U x := rfl

variable (N : M.Submodule)

/-- The quotient of a presheaf of modules by a family of submodules stable under restriction. -/
noncomputable def quotientPresheaf : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfSemilinear (R := R) (fun U => ModuleCat.of _ (M.obj U ⧸ N.obj U))
    (fun {U V} i => (N.obj U).mapQ (N.obj V) (M.restrictₛₗ i) (N.map i))
    (fun U x => by
      induction x using Submodule.Quotient.induction_on with
      | H x => rw [Submodule.mapQ_apply, restrictₛₗ_id])
    (fun i j x => by
      induction x using Submodule.Quotient.induction_on with
      | H x => rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.mapQ_apply,
          restrictₛₗ_comp])

lemma quotientPresheaf_map_mk {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (x : M.obj U) :
    (quotientPresheaf N).map i (Submodule.Quotient.mk x : M.obj U ⧸ N.obj U) =
      (Submodule.Quotient.mk (M.map i x) : M.obj V ⧸ N.obj V) := rfl

/-- The projection onto the quotient presheaf. -/
noncomputable def quotientπ : M ⟶ quotientPresheaf N :=
  homOfLinear (fun U => (N.obj U).mkQ) (fun _ _ => rfl)

@[simp]
lemma quotientπ_app_apply (U : (Opens X)ᵒᵖ) (x : M.obj U) :
    (quotientπ N).app U x = (Submodule.Quotient.mk x : M.obj U ⧸ N.obj U) := rfl

/-- A morphism vanishing on the submodules factors through the quotient presheaf. -/
noncomputable def quotientLift (f : M ⟶ T) (hf : ∀ U x, x ∈ N.obj U → f.app U x = 0) :
    quotientPresheaf N ⟶ T :=
  homOfLinear (fun U => (N.obj U).liftQ (f.app U).hom (fun x hx => hf U x hx)) (fun {U V} i x => by
    induction x using Submodule.Quotient.induction_on with
    | H x => exact PresheafOfModules.naturality_apply f i x)

@[simp]
lemma quotientLift_app_mk (f : M ⟶ T) (hf : ∀ U x, x ∈ N.obj U → f.app U x = 0)
    (U : (Opens X)ᵒᵖ) (x : M.obj U) :
    (quotientLift N f hf).app U (Submodule.Quotient.mk x : M.obj U ⧸ N.obj U) = f.app U x := rfl

lemma quotientπ_quotientLift (f : M ⟶ T) (hf : ∀ U x, x ∈ N.obj U → f.app U x = 0) :
    quotientπ N ≫ quotientLift N f hf = f := by
  ext U x
  rfl

lemma comp_quotientπ_eq_zero (j : L ⟶ M) (hj : ∀ U, LinearMap.range (j.app U).hom ≤ N.obj U) :
    j ≫ quotientπ N = 0 := by
  ext U x
  exact (Submodule.Quotient.mk_eq_zero _).2 (hj U ⟨x, rfl⟩)

/-- The quotient presheaf is the cokernel of any morphism whose images are the given
submodules. -/
noncomputable def isColimitQuotient (j : L ⟶ M)
    (hj : ∀ U, LinearMap.range (j.app U).hom = N.obj U) :
    IsColimit (CokernelCofork.ofπ (quotientπ N)
      (comp_quotientπ_eq_zero N j fun U => (hj U).le)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g hg => quotientLift N g fun U x hx => by
      rw [← hj U] at hx
      obtain ⟨l, rfl⟩ := hx
      have := congrArg (fun φ => (PresheafOfModules.Hom.app φ U).hom l) hg
      simpa using this)
    (fun g hg => quotientπ_quotientLift N g _)
    (fun g hg m hm => by
      ext U x
      induction x using Submodule.Quotient.induction_on with
      | H x => exact congrArg (fun φ => (PresheafOfModules.Hom.app φ U).hom x) hm)

end PresheafConstructions

lemma comp_fin_append {α β : Type*} {m n : ℕ} (g : α → β) (a : Fin m → α) (b : Fin n → α) :
    g ∘ Fin.append a b = Fin.append (g ∘ a) (g ∘ b) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

section ExteriorPresheaf

variable (n : ℕ)

lemma exteriorPresheaf_restrict_ιMulti (F : SheafOfModules.{u} (ringCatSheafOf R))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : Fin n → F.val.obj U) :
    (moduleSheafExteriorPowerPresheaf n F).restrictₛₗ i (exteriorPower.ιMulti _ n m) =
      exteriorPower.ιMulti _ n (fun k => F.val.map i (m k)) :=
  exteriorPowerMap_ιMulti _ _ _ _

/-- The morphism `⋀^n F(U) → ⋀^n G(U)` of exterior-power presheaves induced by `F ⟶ G`. -/
noncomputable def extMap {F G : SheafOfModules.{u} (ringCatSheafOf R)} (φ : F ⟶ G) :
    moduleSheafExteriorPowerPresheaf n F ⟶ moduleSheafExteriorPowerPresheaf n G :=
  homOfLinear (fun U => exteriorPower.map n (φ.val.app U).hom) (fun {U V} i x => by
    have key : (exteriorPower.map n (φ.val.app V).hom).comp
        (exteriorPowerMap n _ (F.val.restrictₛₗ i)) =
        (exteriorPowerMap n _ (G.val.restrictₛₗ i)).comp (exteriorPower.map n (φ.val.app U).hom) :=
      exteriorPower_semilinear_ext fun m => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, exteriorPowerMap_ιMulti,
          exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, exteriorPowerMap_ιMulti]
        congr 1
        funext k
        exact PresheafOfModules.naturality_apply φ.val i (m k)
    exact LinearMap.congr_fun key x)

@[simp]
lemma extMap_app_apply {F G : SheafOfModules.{u} (ringCatSheafOf R)} (φ : F ⟶ G)
    (U : (Opens X)ᵒᵖ) (x : moduleSheafExteriorPowerPresheaf n F |>.obj U) :
    (extMap n φ).app U x = exteriorPower.map n (φ.val.app U).hom x := rfl

end ExteriorPresheaf

section Alpha

variable {F' F : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F)

set_option maxHeartbeats 2000000 in
lemma alpha_natural {p r : ℕ} (hp : p ≤ r) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (x : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U]^p (F'.val.obj U))
    (y : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U]^(r - p) (F.val.obj U)) :
    ExteriorPowerFiltration.alpha (f.val.app V).hom hp
        (exteriorPowerMap p _ (F'.val.restrictₛₗ i) x ⊗ₜ
          exteriorPowerMap (r - p) _ (F.val.restrictₛₗ i) y) =
      exteriorPowerMap r _ (F.val.restrictₛₗ i)
        (ExteriorPowerFiltration.alpha (f.val.app U).hom hp (x ⊗ₜ y)) := by
  have gen : ∀ m₁ m₂, ExteriorPowerFiltration.alpha (f.val.app V).hom hp
      (exteriorPowerMap p _ (F'.val.restrictₛₗ i) (exteriorPower.ιMulti _ p m₁) ⊗ₜ
        exteriorPowerMap (r - p) _ (F.val.restrictₛₗ i) (exteriorPower.ιMulti _ (r - p) m₂)) =
      exteriorPowerMap r _ (F.val.restrictₛₗ i)
        (ExteriorPowerFiltration.alpha (f.val.app U).hom hp
          (exteriorPower.ιMulti _ p m₁ ⊗ₜ exteriorPower.ιMulti _ (r - p) m₂)) := by
    intro m₁ m₂
    rw [exteriorPowerMap_ιMulti, exteriorPowerMap_ιMulti]
    rw [ExteriorPowerFiltration.alpha,
      ExteriorPowerFiltration.alpha]
    rw [ExteriorPowerFiltration.wedgeMap_ιMulti]
    rw [ExteriorPowerFiltration.wedgeMap_ιMulti, exteriorPowerMap_ιMulti]
    congr 1
    funext k
    simp only [Function.comp_apply]
    generalize Fin.cast _ k = j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left, Function.comp_apply]
      exact PresheafOfModules.naturality_apply f.val i (m₁ j)
    · simp only [Fin.append_right, Function.comp_apply, LinearMap.id_apply]
  have hy : ∀ m₁, ((ExteriorPowerFiltration.alpha (f.val.app V).hom hp).comp
      (TensorProduct.mk _ _ _ (exteriorPowerMap p _ (F'.val.restrictₛₗ i)
        (exteriorPower.ιMulti _ p m₁)))).comp (exteriorPowerMap (r - p) _ (F.val.restrictₛₗ i)) =
      (exteriorPowerMap r _ (F.val.restrictₛₗ i)).comp
        ((ExteriorPowerFiltration.alpha (f.val.app U).hom hp).comp
          (TensorProduct.mk _ _ _ (exteriorPower.ιMulti _ p m₁))) := fun m₁ =>
    exteriorPower_semilinear_ext fun m₂ => gen m₁ m₂
  have hx : ((ExteriorPowerFiltration.alpha (f.val.app V).hom hp).comp
      ((TensorProduct.mk _ _ _).flip (exteriorPowerMap (r - p) _ (F.val.restrictₛₗ i) y))).comp
        (exteriorPowerMap p _ (F'.val.restrictₛₗ i)) =
      (exteriorPowerMap r _ (F.val.restrictₛₗ i)).comp
        ((ExteriorPowerFiltration.alpha (f.val.app U).hom hp).comp
          ((TensorProduct.mk _ _ _).flip y)) :=
    exteriorPower_semilinear_ext fun m₁ => LinearMap.congr_fun (hy m₁) y
  exact LinearMap.congr_fun hx x

/-- The presheaf morphism `⋀^p F'(U) ⊗ ⋀^{r-p} F(U) → ⋀^r F(U)`, `x ⊗ y ↦ (⋀^p f)(x) ∧ y`. -/
noncomputable def alphaPre {p r : ℕ} (hp : p ≤ r) :
    moduleSheafExteriorPowerPresheaf p F' ⊗ moduleSheafExteriorPowerPresheaf (r - p) F ⟶
      moduleSheafExteriorPowerPresheaf r F where
  app U := ModuleCat.ofHom (ExteriorPowerFiltration.alpha (f.val.app U).hom hp)
  naturality i := ModuleCat.MonoidalCategory.tensor_ext fun x y => alpha_natural f hp i x y

@[simp]
lemma alphaPre_app_apply {p r : ℕ} (hp : p ≤ r) (U : (Opens X)ᵒᵖ)
    (z : (moduleSheafExteriorPowerPresheaf p F' ⊗ moduleSheafExteriorPowerPresheaf (r - p) F).obj
      U) :
    (alphaPre f hp).app U z = ExteriorPowerFiltration.alpha (f.val.app U).hom hp z := rfl

end Alpha

section Locality

/-- A morphism of presheaves of abelian groups that is bijective on all opens inside a
neighbourhood of `x` is bijective on stalks at `x`. -/
lemma stalkFunctor_map_bijective_of_locally_bijective {Y : TopCat.{u}}
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} Y} (p : P ⟶ Q) {x : Y} {U : Opens Y} (hx : x ∈ U)
    (hp : ∀ V : Opens Y, V ≤ U → Function.Bijective (p.app (op V))) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map p) := by
  constructor
  · intro s t hst
    obtain ⟨V, hVU, hxV, s, rfl⟩ := P.exists_le_germ_eq s hx
    obtain ⟨V', hV'U, hxV', t, rfl⟩ := P.exists_le_germ_eq t hx
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
    obtain ⟨W, hxW, iV, iV', heq⟩ := Q.germ_eq x hxV hxV' _ _ hst
    have hWU : W ≤ U := (leOfHom iV).trans hVU
    have e : ∀ {V₁ V₂ : Opens Y} (i : V₂ ⟶ V₁) (a : ToType (P.obj (op V₁))),
        Q.map i.op (p.app (op V₁) a) = p.app (op V₂) (P.map i.op a) := fun i a => by
      rw [← ConcreteCategory.comp_apply, ← p.naturality, ConcreteCategory.comp_apply]
    rw [e, e] at heq
    have := (hp W hWU).1 heq
    rw [← TopCat.Presheaf.germ_res_apply P iV x hxW,
      ← TopCat.Presheaf.germ_res_apply P iV' x hxW, this]
  · intro t
    obtain ⟨V, hVU, hxV, t, rfl⟩ := Q.exists_le_germ_eq t hx
    obtain ⟨s, rfl⟩ := (hp V hVU).2 t
    exact ⟨P.germ V x hxV s, TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _⟩

/-- A morphism of presheaves of modules that is bijective on all small enough opens becomes an
isomorphism after sheafification. -/
lemma isIso_sheafifyMap_of_locally_bijective
    {P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ V : Opens X, V ≤ U → Function.Bijective (φ.app (op V)).hom) :
    IsIso (SheafAlgebraOperations.sheafifyMap φ) :=
  SheafAlgebraOperations.isIso_sheafifyMap φ fun x => by
    obtain ⟨U, hxU, hU⟩ := h x
    exact stalkFunctor_map_bijective_of_locally_bijective _ hxU hU

end Locality

section Filtration

variable {F' F F'' : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F) (g : F ⟶ F'')

/-- The presheaf version of the standard filtration: on `U` it is the filtration of `⋀^r F(U)`
by the images of `⋀^p F'(U) ⊗ ⋀^{r-p} F(U)`. -/
noncomputable def filPre (r p : ℕ) : (moduleSheafExteriorPowerPresheaf r F).Submodule where
  obj U := ExteriorPowerFiltration.filt (f.val.app U).hom r p
  map {U V} i := by
    intro w hw
    rcases Nat.lt_or_ge r p with hp | hp
    · rw [ExteriorPowerFiltration.filt_of_lt _ hp] at hw
      have hw0 : w = 0 := (Submodule.mem_bot _).1 hw
      subst hw0
      exact Submodule.zero_mem _
    · rw [ExteriorPowerFiltration.filt_of_le _ hp] at hw
      obtain ⟨z, rfl⟩ := hw
      refine Submodule.mem_comap.2 ?_
      rw [ExteriorPowerFiltration.filt_of_le _ hp]
      exact ⟨_, PresheafOfModules.naturality_apply (alphaPre f hp) i z⟩

lemma filPre_obj (r p : ℕ) (U : (Opens X)ᵒᵖ) :
    (filPre f r p).obj U = ExteriorPowerFiltration.filt (f.val.app U).hom r p := rfl

lemma filPre_antitone (r : ℕ) : Antitone (filPre f r) := fun _ _ h _ =>
  ExteriorPowerFiltration.filt_antitone _ r h

lemma filPre_zero (r : ℕ) : filPre f r 0 = ⊤ :=
  PresheafOfModules.Submodule.ext fun _ => ExteriorPowerFiltration.filt_zero _ r

lemma filPre_of_lt {r p : ℕ} (hp : r < p) : filPre f r p = ⊥ :=
  PresheafOfModules.Submodule.ext fun _ => ExteriorPowerFiltration.filt_of_lt _ hp

/-- The presheaf morphism `id ⊗ ⋀^{r-p} g : ⋀^p F' ⊗ ⋀^{r-p} F → ⋀^p F' ⊗ ⋀^{r-p} F''`. -/
noncomputable def betaPre (p r : ℕ) :
    moduleSheafExteriorPowerPresheaf p F' ⊗ moduleSheafExteriorPowerPresheaf (r - p) F ⟶
      moduleSheafExteriorPowerPresheaf p F' ⊗ moduleSheafExteriorPowerPresheaf (r - p) F'' :=
  moduleSheafExteriorPowerPresheaf p F' ◁ extMap (r - p) g

lemma betaPre_app_apply (p r : ℕ) (U : (Opens X)ᵒᵖ)
    (z : (moduleSheafExteriorPowerPresheaf p F' ⊗
      moduleSheafExteriorPowerPresheaf (r - p) F).obj U) :
    (betaPre (F' := F') g p r).app U z =
      LinearMap.lTensor _ (exteriorPower.map (r - p) (g.val.app U).hom) z := rfl

variable {p r : ℕ} (hp : p ≤ r)

/-- The submodules `α_p⁻¹(F^{p+1}) ∩ ker β_p` of `⋀^p F'(U) ⊗ ⋀^{r-p} F(U)`. -/
noncomputable def kerSub :
    (moduleSheafExteriorPowerPresheaf p F' ⊗ moduleSheafExteriorPowerPresheaf (r - p) F).Submodule
    where
  obj U := ((filPre f r (p + 1)).obj U).comap ((alphaPre f hp).app U).hom ⊓
    LinearMap.ker ((betaPre g p r).app U).hom
  map {U V} i := by
    rintro z ⟨hz₁, hz₂⟩
    refine ⟨Submodule.mem_comap.2 ?_, LinearMap.mem_ker.2 ?_⟩
    · exact (congrArg (· ∈ (filPre f r (p + 1)).obj V)
        (PresheafOfModules.naturality_apply (alphaPre f hp) i z)).mpr
        ((filPre f r (p + 1)).map_mem i hz₁)
    · have h2 : (betaPre g p r).app U z = 0 := hz₂
      exact (PresheafOfModules.naturality_apply (betaPre g p r) i z).trans
        ((congrArg _ h2).trans (map_zero _))

/-- The graded piece `F^p / F^{p+1}` of the presheaf filtration, as a submodule of `F^p`. -/
noncomputable def gradSub (r p : ℕ) : (filPre f r p).toPresheafOfModules.Submodule where
  obj U := ((filPre f r (p + 1)).obj U).comap ((filPre f r p).obj U).subtype
  map {U V} i := by
    intro w hw
    exact (filPre f r (p + 1)).map_mem i hw

/-- The corestriction `⋀^p F' ⊗ ⋀^{r-p} F → F^p` of `α_p`. -/
noncomputable def alphaTo :
    moduleSheafExteriorPowerPresheaf p F' ⊗ moduleSheafExteriorPowerPresheaf (r - p) F ⟶
      (filPre f r p).toPresheafOfModules :=
  homOfLinear (fun U => LinearMap.codRestrict _ ((alphaPre f hp).app U).hom
    fun z => ExteriorPowerFiltration.alpha_mem_filt _ hp z) (fun i z =>
      Subtype.ext (PresheafOfModules.naturality_apply (alphaPre f hp) i z))

/-- The comparison presheaf `(⋀^p F' ⊗ ⋀^{r-p} F) / (α_p⁻¹(F^{p+1}) ∩ ker β_p)`. -/
noncomputable abbrev apexPre := quotientPresheaf (kerSub f g hp)

/-- The map from the comparison presheaf to the graded piece `F^p / F^{p+1}`. -/
noncomputable def toGrad : apexPre f g hp ⟶ quotientPresheaf (gradSub f r p) :=
  quotientLift _ (alphaTo f hp ≫ quotientπ _) fun _ _ hz =>
    (Submodule.Quotient.mk_eq_zero _).2 hz.1

/-- The map from the comparison presheaf to `⋀^p F' ⊗ ⋀^{r-p} F''`. -/
noncomputable def toH : apexPre f g hp ⟶
    moduleSheafExteriorPowerPresheaf p F' ⊗ moduleSheafExteriorPowerPresheaf (r - p) F'' :=
  quotientLift _ (betaPre g p r) fun _ _ hz => hz.2

variable {f g} in
/-- On sections over `V`, `0 → F'(V) → F(V) → F''(V) → 0` is a split short exact sequence of
modules, with `F'(V)` and `F''(V)` finite free. -/
structure IsSplitAt (f : F' ⟶ F) (g : F ⟶ F'') (V : (Opens X)ᵒᵖ) : Prop where
  injective : Function.Injective (f.val.app V).hom
  exact : LinearMap.range (f.val.app V).hom = LinearMap.ker (g.val.app V).hom
  split : ∃ s : F''.val.obj V →ₗ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj V] F.val.obj V,
    (g.val.app V).hom ∘ₗ s = LinearMap.id
  free₁ : Module.Free ((R.obj ⋙ forget₂ CommRingCat RingCat).obj V) (F'.val.obj V)
  finite₁ : Module.Finite ((R.obj ⋙ forget₂ CommRingCat RingCat).obj V) (F'.val.obj V)
  free₃ : Module.Free ((R.obj ⋙ forget₂ CommRingCat RingCat).obj V) (F''.val.obj V)
  finite₃ : Module.Finite ((R.obj ⋙ forget₂ CommRingCat RingCat).obj V) (F''.val.obj V)

lemma toGrad_bijective {V : (Opens X)ᵒᵖ} (hV : IsSplitAt f g V) :
    Function.Bijective ((toGrad f g hp).app V).hom := by
  obtain ⟨s, hs⟩ := hV.split
  have := hV.free₁
  have := hV.finite₁
  have := hV.free₃
  have := hV.finite₃
  have key := fun z => ExteriorPowerFiltration.alpha_mem_filt_succ_iff hV.exact hs hV.injective hp z
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    induction t using Submodule.Quotient.induction_on with
    | H z =>
      have h1 : ExteriorPowerFiltration.alpha (f.val.app V).hom hp z ∈
          ExteriorPowerFiltration.filt (f.val.app V).hom r (p + 1) :=
        (Submodule.Quotient.mk_eq_zero ((gradSub f r p).obj V)).1 ht
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨h1, (key z).1 h1⟩
  · intro t
    induction t using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨w, hw⟩ := w
      have hw' : w ∈ LinearMap.range (ExteriorPowerFiltration.alpha (f.val.app V).hom hp) := by
        rw [← ExteriorPowerFiltration.filt_of_le _ hp]
        exact hw
      obtain ⟨z, rfl⟩ := hw'
      exact ⟨Submodule.Quotient.mk z, rfl⟩

lemma toH_bijective {V : (Opens X)ᵒᵖ} (hV : IsSplitAt f g V) :
    Function.Bijective ((toH f g hp).app V).hom := by
  obtain ⟨s, hs⟩ := hV.split
  have := hV.free₁
  have := hV.finite₁
  have := hV.free₃
  have := hV.finite₃
  have key := fun z => ExteriorPowerFiltration.alpha_mem_filt_succ_iff hV.exact hs hV.injective hp z
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    induction t using Submodule.Quotient.induction_on with
    | H z => exact (Submodule.Quotient.mk_eq_zero _).2 ⟨(key z).2 ht, ht⟩
  · intro t
    obtain ⟨z, hz⟩ := ExteriorPowerFiltration.lTensor_map_surjective hs _ (r - p) t
    exact ⟨Submodule.Quotient.mk z, hz⟩

end Filtration

section LocalSplitting

variable {A B : SheafOfModules.{u} (ringCatSheafOf R)}

/-- A monomorphism of `𝒪_X`-modules is injective on sections. -/
lemma app_injective_of_mono (i : A ⟶ B) [Mono i] (U : (Opens X)ᵒᵖ) :
    Function.Injective (i.val.app U).hom := by
  have : PreservesFiniteLimits (SheafOfModules.evaluation (ringCatSheafOf R) U) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits (ringCatSheafOf R) U
  have : Mono ((SheafOfModules.evaluation (ringCatSheafOf R) U).map i) := Functor.map_mono _ _
  exact (ModuleCat.mono_iff_injective _).1 this

/-- Sections of a short exact sequence of `𝒪_X`-modules are exact in the middle. -/
lemma range_eq_ker_of_shortExact {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))}
    (hS : S.ShortExact) (U : (Opens X)ᵒᵖ) :
    LinearMap.range (S.f.val.app U).hom = LinearMap.ker (S.g.val.app U).hom := by
  let G := SheafOfModules.evaluation (ringCatSheafOf R) U
  have hG : PreservesFiniteLimits G := SheafOfModules.Finite.evaluationPreservesFiniteLimits (ringCatSheafOf R) U
  have : G.Additive := ⟨fun {_ _ _ _} => rfl⟩
  have key : PreservesFiniteLimits G → ∀ S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R)),
      S.Exact ∧ Mono S.f → (S.map G).Exact ∧ Mono (G.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae G).out 3 1).mp
  have := hS.mono_f
  exact (key hG S ⟨hS.exact, inferInstance⟩).1.moduleCat_range_eq_ker

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
  have h1 : PreservesColimit D₀ (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)) :=
    inferInstance
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

/-- An epimorphism of `𝒪_X`-modules is locally surjective on sections. -/
lemma exists_local_lift (g : A ⟶ B) [Epi g] {U : Opens X} (t : B.val.obj (op U)) {x : X}
    (hx : x ∈ U) : ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∃ s : A.val.obj (op V), g.val.app (op V) s = B.val.map (homOfLE hVU).op t := by
  have h := toSheaf_preservesColimit (span g g)
  have : Epi ((SheafOfModules.toSheaf (ringCatSheafOf R)).map g) :=
    @preserves_epi_of_preservesColimit _ _ _ _ (SheafOfModules.toSheaf (ringCatSheafOf R)) _ _ g h
      ‹Epi g›
  have h := (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((SheafOfModules.toSheaf (ringCatSheafOf R)).map g)).mpr this
  obtain ⟨V, hVU, ⟨s, hs⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp h U t x hx
  exact ⟨V, hVU, hxV, s, hs⟩

open Ringed in
/-- A local frame of `E` over `U` makes the sections of `E` over each open `V ⊆ U` a finite
free module. -/
lemma free_finite_of_isLocalFrame {E : SheafOfModules.{u} (ringCatSheafOf R)} {U : Opens X}
    {ι : Type u} [Fintype ι] {e : ι → (E.val.presheaf.obj (op U) : Type u)}
    (hE : Ringed.IsLocalFrame E U e) {V : Opens X} (hV : V ≤ U) :
    Module.Free ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (E.val.obj (op V)) ∧
      Module.Finite ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (E.val.obj (op V)) := by
  let eqv : (ι → R.obj.obj (op V)) ≃ₗ[R.obj.obj (op V)] (E.val.presheaf.obj (op V)) :=
    LinearEquiv.ofBijective (Ringed.localFrameMap E e hV) (hE V hV)
  have h1 : Module.Free (R.obj.obj (op V)) (E.val.presheaf.obj (op V)) := Module.Free.of_equiv eqv
  have h2 : Module.Finite (R.obj.obj (op V)) (E.val.presheaf.obj (op V)) := Module.Finite.equiv eqv
  exact ⟨h1, h2⟩

open Ringed in
/-- Near every point, a short exact sequence `0 → F' → F → F'' → 0` with `F'` and `F''` finite
locally free is split on sections over all small opens, with finite free outer terms. -/
lemma exists_isSplitAt {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))}
    (hS : S.ShortExact) (h₁ : Ringed.IsFiniteLocallyFree S.X₁)
    (h₃ : Ringed.IsFiniteLocallyFree S.X₃) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ V : Opens X, V ≤ U → IsSplitAt S.f S.g (op V) := by
  classical
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨U₁, ι₁, _, e₁, hx₁, hE₁⟩ := Ringed.exists_isLocalFrame_of_isFiniteLocallyFree h₁ x
  obtain ⟨U₃, ι₃, _, e₃, hx₃, hE₃⟩ := Ringed.exists_isLocalFrame_of_isFiniteLocallyFree h₃ x
  have hlift : ∀ j : ι₃, ∃ (W : Opens X) (hW : W ≤ U₃), x ∈ W ∧
      ∃ t : S.X₂.val.obj (op W), S.g.val.app (op W) t = S.X₃.val.map (homOfLE hW).op (e₃ j) :=
    fun j => exists_local_lift S.g (e₃ j) hx₃
  choose W hW hxW t ht using hlift
  have hxinf : ∀ s : Finset ι₃, x ∈ s.inf W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s _ ih =>
      rw [Finset.inf_insert]
      exact ⟨hxW j, ih⟩
  refine ⟨U₁ ⊓ U₃ ⊓ Finset.univ.inf W, ⟨⟨hx₁, hx₃⟩, hxinf _⟩, fun V hV => ?_⟩
  have hV₁ : V ≤ U₁ := hV.trans (inf_le_left.trans inf_le_left)
  have hV₃ : V ≤ U₃ := hV.trans (inf_le_left.trans inf_le_right)
  have hVW : ∀ j, V ≤ W j := fun j =>
    hV.trans (inf_le_right.trans (Finset.inf_le (Finset.mem_univ j)))
  obtain ⟨hfree₁, hfin₁⟩ := free_finite_of_isLocalFrame hE₁ hV₁
  obtain ⟨hfree₃, hfin₃⟩ := free_finite_of_isLocalFrame hE₃ hV₃
  refine ⟨app_injective_of_mono S.f _, range_eq_ker_of_shortExact hS _, ?_, hfree₁, hfin₁,
    hfree₃, hfin₃⟩
  let eqv : (ι₃ → R.obj.obj (op V)) ≃ₗ[R.obj.obj (op V)] (S.X₃.val.presheaf.obj (op V)) :=
    LinearEquiv.ofBijective (Ringed.localFrameMap S.X₃ e₃ hV₃) (hE₃ V hV₃)
  let lc : (ι₃ → R.obj.obj (op V)) →ₗ[R.obj.obj (op V)] S.X₂.val.presheaf.obj (op V) :=
    Fintype.linearCombination (R.obj.obj (op V))
      (fun j => S.X₂.val.presheaf.map (homOfLE (hVW j)).op (t j))
  refine ⟨lc ∘ₗ eqv.symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun y => ?_
  obtain ⟨a, rfl⟩ := eqv.surjective y
  change (S.g.val.app (op V)).hom (lc (eqv.symm (eqv a))) = eqv a
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.ofBijective_apply, Ringed.localFrameMap_apply,
    Fintype.linearCombination_apply]
  let gV : S.X₂.val.presheaf.obj (op V) →ₗ[R.obj.obj (op V)] S.X₃.val.presheaf.obj (op V) :=
    (S.g.val.app (op V)).hom
  change gV _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  congr 1
  refine (PresheafOfModules.naturality_apply S.g.val (homOfLE (hVW j)).op (t j)).trans ?_
  rw [ht j]
  exact (PresheafOfModules.map_comp_apply S.X₃.val (homOfLE (hW j)).op (homOfLE (hVW j)).op
    (e₃ j)).symm

end LocalSplitting

section SheafLevel

open SheafAlgebraOperations

/-- The category of `𝒪_X`-modules has a zero object. -/
instance hasZeroObject_sheafOfModules : HasZeroObject (SheafOfModules.{u} (ringCatSheafOf R)) :=
  hasZeroObject_of_hasTerminal_object

set_option synthInstance.maxHeartbeats 200000 in
instance initialMonoClass_sheafOfModules :
    InitialMonoClass (SheafOfModules.{u} (ringCatSheafOf R)) :=
  inferInstance

variable {F' F F'' : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F) (g : F ⟶ F'')

instance (r p : ℕ) : Mono (sheafifyMap (filPre f r p).ι) := by
  have : (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).PreservesMonomorphisms :=
    inferInstance
  exact Functor.map_mono _ _

variable (F) in
/-- The exterior power `⋀^r F` is by definition the sheafification of `U ↦ ⋀^r F(U)`. -/
noncomputable def extPowIso (r : ℕ) : sheafify (moduleSheafExteriorPowerPresheaf r F) ≅
    (moduleSheafExteriorPower r F : SheafOfModules.{u} (ringCatSheafOf R)) :=
  Iso.refl _

/-- The inclusion of the `p`-th step of the standard filtration into `⋀^r F`. -/
noncomputable def filArrow (r p : ℕ) :
    sheafify (filPre f r p).toPresheafOfModules ⟶
      (moduleSheafExteriorPower r F : SheafOfModules.{u} (ringCatSheafOf R)) :=
  sheafifyMap (filPre f r p).ι ≫ (extPowIso F r).hom

instance (r p : ℕ) : Mono (filArrow f r p) := by
  unfold filArrow
  infer_instance

/-- The standard filtration of `⋀^r F` attached to `f : F' ⟶ F`: `F^p` is the image of the
sheafification of the presheaf of images of `⋀^p F'(U) ⊗ ⋀^{r-p} F(U) → ⋀^r F(U)`. -/
noncomputable def filSh (r p : ℕ) :
    Subobject (C := SheafOfModules.{u} (ringCatSheafOf R)) (moduleSheafExteriorPower r F) :=
  Subobject.mk (filArrow f r p)

lemma homOfLE_filArrow (r : ℕ) {p q : ℕ} (h : p ≤ q) :
    sheafifyMap (PresheafOfModules.Submodule.homOfLE (filPre_antitone f r h)) ≫
      filArrow f r p = filArrow f r q := by
  rw [filArrow, filArrow, ← Category.assoc, ← Functor.map_comp,
    PresheafOfModules.Submodule.homOfLE_ι]

lemma filSh_antitone (r : ℕ) : Antitone (filSh f r) := fun _ _ h =>
  Subobject.mk_le_mk_of_comm _ (homOfLE_filArrow f r h)

lemma filSh_zero (r : ℕ) : filSh f r 0 = ⊤ := by
  have : IsIso (sheafifyMap (filPre f r 0).ι) :=
    isIso_sheafifyMap_of_locally_bijective _ fun x => ⟨⊤, trivial, fun V _ => by
      refine ⟨fun a b h => Subtype.ext h, fun w => ?_⟩
      have hw : w ∈ (filPre f r 0).obj (op V) := by
        rw [filPre_zero]
        trivial
      exact ⟨⟨w, hw⟩, rfl⟩⟩
  have : IsIso (filArrow f r 0) := by
    unfold filArrow
    infer_instance
  exact Subobject.mk_eq_top_of_isIso _

lemma filSh_of_lt {r p : ℕ} (hp : r < p) : filSh f r p = ⊥ := by
  rw [filSh, Subobject.mk_eq_bot_iff_zero]
  have : (filPre f r p).ι = 0 := by
    ext U ⟨w, hw⟩
    have hw' : w ∈ (⊥ : (moduleSheafExteriorPowerPresheaf r F).Submodule).obj U := by
      rw [← filPre_of_lt f hp]
      exact hw
    exact (Submodule.mem_bot _).1 hw'
  rw [filArrow, this]
  change (PresheafOfModules.sheafification _).map 0 ≫ _ = 0
  rw [Functor.map_zero, zero_comp]

variable (F' F'') in
/-- `sheafify (U ↦ ⋀^p F'(U) ⊗ ⋀^q F''(U)) ≅ ⋀^p F' ⊗ ⋀^q F''`. -/
noncomputable def sheafifyTensorIso (p q : ℕ) :
    sheafify (moduleSheafExteriorPowerPresheaf p F' ⊗ moduleSheafExteriorPowerPresheaf q F'') ≅
      moduleSheafTensor (moduleSheafExteriorPower p F') (moduleSheafExteriorPower q F'') :=
  @asIso _ _ _ _ (sheafifyMap (moduleSheafExteriorPowerUnit p F' ⊗ₘ
      moduleSheafExteriorPowerUnit q F''))
    (isIso_sheafifyMap _ fun x => stalkMap_tensorHom_bijective _ _ x
      (stalkMap_sheafifyUnit_bijective _ x) (stalkMap_sheafifyUnit_bijective _ x))

lemma ofLE_filSh_eq (r p : ℕ) (h : filSh f r (p + 1) ≤ filSh f r p) :
    Subobject.ofLE _ _ h = ((Subobject.underlyingIso (filArrow f r (p + 1))).hom ≫
      sheafifyMap (PresheafOfModules.Submodule.homOfLE (filPre_antitone f r (Nat.le_succ p)))) ≫
        (Subobject.underlyingIso (filArrow f r p)).inv := by
  have h' : Subobject.mk (filArrow f r (p + 1)) ≤ Subobject.mk (filArrow f r p) := h
  have hk : Subobject.ofMkLEMk _ _ h' =
      sheafifyMap (PresheafOfModules.Submodule.homOfLE (filPre_antitone f r (Nat.le_succ p))) := by
    rw [← cancel_mono (filArrow f r p), Subobject.ofMkLEMk_comp, homOfLE_filArrow f r (Nat.le_succ p)]
  change Subobject.ofLE (Subobject.mk (filArrow f r (p + 1))) (Subobject.mk (filArrow f r p)) h' = _
  rw [← hk, Subobject.ofMkLEMk]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

lemma range_homOfLE_app (r p : ℕ) (U : (Opens X)ᵒᵖ) :
    LinearMap.range ((PresheafOfModules.Submodule.homOfLE
      (filPre_antitone f r (Nat.le_succ p))).app U).hom = (gradSub f r p).obj U := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact v.2
  · intro hw
    exact ⟨⟨w.1, hw⟩, rfl⟩

/-- The cokernel of `F^{p+1} → F^p` is the sheafification of the presheaf `F^p / F^{p+1}`. -/
noncomputable def cokernelIsoSheafifyGrad (r p : ℕ) :
    cokernel (sheafifyMap (PresheafOfModules.Submodule.homOfLE
      (filPre_antitone f r (Nat.le_succ p)))) ≅ sheafify (quotientPresheaf (gradSub f r p)) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (CokernelCofork.mapIsColimit _ (isColimitQuotient (gradSub f r p) _ (range_homOfLE_app f r p))
      (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)))

variable (hloc : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∀ V : Opens X, V ≤ U → IsSplitAt f g (op V))
include hloc

/-- The graded pieces of the standard filtration, assuming the sequence splits locally on
sections. -/
noncomputable def gradedIso {r p : ℕ} (hp : p ≤ r) (h : filSh f r (p + 1) ≤ filSh f r p) :
    cokernel (Subobject.ofLE _ _ h) ≅
      moduleSheafTensor (moduleSheafExteriorPower p F') (moduleSheafExteriorPower (r - p) F'') :=
  haveI : IsIso (sheafifyMap (toGrad f g hp)) :=
    isIso_sheafifyMap_of_locally_bijective _ fun x => by
      obtain ⟨U, hxU, hU⟩ := hloc x
      exact ⟨U, hxU, fun V hV => toGrad_bijective f g hp (hU V hV)⟩
  haveI : IsIso (sheafifyMap (toH f g hp)) :=
    isIso_sheafifyMap_of_locally_bijective _ fun x => by
      obtain ⟨U, hxU, hU⟩ := hloc x
      exact ⟨U, hxU, fun V hV => toH_bijective f g hp (hU V hV)⟩
  cokernelIsoOfEq (ofLE_filSh_eq f r p h) ≪≫
    cokernelCompIsIso ((Subobject.underlyingIso (filArrow f r (p + 1))).hom ≫
      sheafifyMap (PresheafOfModules.Submodule.homOfLE (filPre_antitone f r (Nat.le_succ p))))
      (Subobject.underlyingIso (filArrow f r p)).inv ≪≫
    cokernelEpiComp (Subobject.underlyingIso (filArrow f r (p + 1))).hom
      (sheafifyMap (PresheafOfModules.Submodule.homOfLE (filPre_antitone f r (Nat.le_succ p)))) ≪≫
    cokernelIsoSheafifyGrad f r p ≪≫ (asIso (sheafifyMap (toGrad f g hp))).symm ≪≫
      asIso (sheafifyMap (toH f g hp)) ≪≫ sheafifyTensorIso F' F'' p (r - p)

/-- **The exterior-power filtration of a locally split exact sequence.** -/
theorem exists_filtration_of_locally_split (r : ℕ) :
    ∃ Fil : ℕ → Subobject (C := SheafOfModules.{u} (ringCatSheafOf R))
        (moduleSheafExteriorPower r F),
      Fil 0 = ⊤ ∧ Fil (r + 1) = ⊥ ∧ Antitone Fil ∧
      ∀ p (h : Fil (p + 1) ≤ Fil p), p ≤ r →
        Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
          moduleSheafTensor (moduleSheafExteriorPower p F') (moduleSheafExteriorPower (r - p) F'')) :=
  ⟨filSh f r, filSh_zero f r, filSh_of_lt f (Nat.lt_succ_self r), filSh_antitone f r,
    fun _ h hp => ⟨gradedIso f g hloc hp h⟩⟩

end SheafLevel

section MainTheorem

/-- **Hartshorne II, Exercise 5.16(d).** Let `0 → F' → F → F'' → 0` be a short exact sequence of
locally free `𝒪_X`-modules of finite rank on a ringed space `(X, 𝒪_X)`. Then for every `r` the
exterior power `⋀^r F` has a finite filtration
`⋀^r F = F^0 ⊇ F^1 ⊇ ⋯ ⊇ F^r ⊇ F^{r+1} = 0` (a decreasing chain of subobjects) whose quotients
are `F^p / F^{p+1} ≅ ⋀^p F' ⊗ ⋀^{r-p} F''` for `0 ≤ p ≤ r`. The filtration is the standard one:
`F^p` is the image of `⋀^p F' ⊗ ⋀^{r-p} F → ⋀^r F`. -/
theorem exteriorPower_exact_filtration
    (S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))) (hS : S.ShortExact)
    (h₁ : Ringed.IsFiniteLocallyFree S.X₁) (h₃ : Ringed.IsFiniteLocallyFree S.X₃) :
    Ringed.IsFiniteLocallyFree S.X₂ → ∀ r : ℕ,
    ∃ Fil : ℕ → Subobject (C := SheafOfModules.{u} (ringCatSheafOf R))
        (moduleSheafExteriorPower r S.X₂),
      Fil 0 = ⊤ ∧ Fil (r + 1) = ⊥ ∧ Antitone Fil ∧
      ∀ p (h : Fil (p + 1) ≤ Fil p), p ≤ r →
        Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
          moduleSheafTensor (moduleSheafExteriorPower p S.X₁)
            (moduleSheafExteriorPower (r - p) S.X₃)) := fun _ r =>
  exists_filtration_of_locally_split S.f S.g (fun x => exists_isSplitAt hS h₁ h₃ x) r

end MainTheorem

end ExteriorPowerExactFiltration

end Hartshorne
