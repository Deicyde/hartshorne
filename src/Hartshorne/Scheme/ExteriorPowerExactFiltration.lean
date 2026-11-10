/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ExteriorPowerFiltrationAlgebra
import Hartshorne.Scheme.SheafAlgebraOperations
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Hartshorne.RingedSpace.LocallyFreeRank
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

Let `(X, 𝒪_X)` be a ringed space (a topological space `X` with a sheaf `R` of commutative rings;
`𝒪_X`-modules are `SheafOfModules (ringCatSheafOf R)`) and let `0 → F' → F → F'' → 0` be a short
exact sequence of `𝒪_X`-modules (`S : ShortComplex _`, `S.ShortExact`) with `F'` and `F''` locally
free (of arbitrary rank). For `r ≥ 0` the exterior power `⋀^r F` (`moduleSheafExteriorPower r F`,
the sheafification of `U ↦ ⋀^r F(U)`) carries the standard filtration `F^p` (`filSh`): for `p ≤ r`,
`F^p` is the image of the wedge-product morphism `⋀^p F' ⊗ ⋀^{r-p} F → ⋀^r F` (`wedgeSheafMap`,
`filSh_eq_imageSubobject`), and `F^p = 0` for `p > r`. We prove:

* `exteriorPower_exact_filtration_of_isLocallyFree`: `F^0 = ⋀^r F`, `F^{r+1} = 0`, the `F^p`
  decrease, and `F^p / F^{p+1} ≅ ⋀^p F' ⊗ ⋀^{r-p} F''` for `p ≤ r`;
  `exists_exteriorPower_exact_filtration_of_isLocallyFree` states this in Hartshorne's form (there
  is such a filtration). The finite-rank versions `exteriorPower_exact_filtration` and
  `exists_exteriorPower_exact_filtration` are deprecated;
* `exteriorPower_exact_det`: if `F'`, `F`, `F''` are locally free of ranks `n'`, `n`, `n''`, then
  `⋀^n F ≅ ⋀^{n'} F' ⊗ ⋀^{n''} F''`.

Proof. Everything is first done for presheaves of sections. The presheaf filtration `filPre` is
given on each open `U` by the module-level filtration of
`Hartshorne.Scheme.ExteriorPowerFiltrationAlgebra` applied to `F'(U) → F(U)`. To compare the graded
piece `F^p(U) / F^{p+1}(U)` with `⋀^p F'(U) ⊗ ⋀^{r-p} F''(U)` (there is no map between them on
arbitrary opens, as `F(U) → F''(U)` need not be onto) both are compared with the quotient
`apexPre` of `⋀^p F'(U) ⊗ ⋀^{r-p} F(U)` by `α_p⁻¹(F^{p+1}) ∩ ker(id ⊗ ⋀^{r-p} g)`
(`toGrad`, `toH`). Both comparison maps are bijective on stalks
(`stalk_toGrad_bijective`, `stalk_toH_bijective`): exterior powers and tensor products commute
with stalks (`extStalkEquiv`, `tensorExtStalkEquiv`), the stalk sequence
`0 → F'_x → F_x → F''_x → 0` is exact, and it splits with free outer terms because stalks of
locally free modules are free. So the module-level theorem for free modules of arbitrary rank
applies at each stalk. A morphism of presheaves bijective on stalks becomes an isomorphism after
sheafification, and sheafification preserves monomorphisms and cokernels, which gives the sheaf
statements (`gradedIsoOfIsLocallyFree`). In finite rank the sequence of sections over all small
opens is even split exact with finite free outer terms (`exists_isSplitAt`), which is used for
the determinant: if `n = n' + n''` the filtration of `⋀^n F` collapses (`F^{n'} = ⋀^n F`,
`F^{n'+1} = 0`) because exterior powers of a free module above its rank vanish; otherwise `𝒪_X`
vanishes near every point and all `𝒪_X`-modules are zero (`isZero_of_locally_subsingleton`).
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

-- Unifying the coefficient rings of the sections of `F'` and `F` is slow here.
set_option maxHeartbeats 400000 in
/-- Naturality of `α_p` with respect to restriction of sections. -/
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

section ExteriorStalk

open ModuleSheafTensor

/-- Finitely many open neighbourhoods of `x` contain a common open neighbourhood. -/
lemma exists_open_le_of_finite {x : X} {ι : Type*} [Finite ι] (U : ι → Opens X)
    (hU : ∀ i, x ∈ U i) :
    ∃ V : Opens X, x ∈ V ∧ ∀ i, V ≤ U i := by
  have h : (⋂ i, (U i : Set X)) ∈ nhds x :=
    Filter.iInter_mem.2 fun i => (U i).isOpen.mem_nhds (hU i)
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 h
  exact ⟨⟨t, hto⟩, hxt, fun i => fun y hy => Set.mem_iInter.1 (ht hy) i⟩

/-- A finite family of germs has representatives over a common open neighbourhood. -/
lemma exists_common_sectionGerm {x : X} {ι : Type*} [Finite ι]
    (M : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (m : ι → moduleStalk M x) :
    ∃ (V : Opens X) (hV : x ∈ V) (t : ι → M.obj (op V)), ∀ i, sectionGerm M x V hV (t i) = m i := by
  choose U hU s hs using fun i => exists_sectionGerm M x (m i)
  obtain ⟨V, hV, hVU⟩ := exists_open_le_of_finite U hU
  exact ⟨V, hV, fun i => res M (homOfLE (hVU i)) (s i), fun i => by
    rw [sectionGerm_res, hs]⟩

variable (n : ℕ) (F : SheafOfModules.{u} (ringCatSheafOf R)) (x : X)

/-- The germ map `F(U) → Fₓ`, semilinear over the germ map `𝒪_X(U) → 𝒪_{X,x}`. -/
noncomputable def germₛₗ (U : Opens X) (hU : x ∈ U) :
    F.val.obj (op U) →ₛₗ[((TopCat.Presheaf.germ R.obj U x hU).hom :
      (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) →+* ringSheafStalk R x)]
      moduleStalk F.val x where
  toFun := sectionGerm F.val x U hU
  map_add' := map_add _
  map_smul' := sectionGerm_smul F.val x U hU

/-- The map `⋀^n F(U) → ⋀^n Fₓ` induced by the germ map. -/
noncomputable def extGerm (U : Opens X) (hU : x ∈ U) :
    ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^n (F.val.obj (op U)) →ₛₗ[
      ((TopCat.Presheaf.germ R.obj U x hU).hom :
        (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) →+* ringSheafStalk R x)]
      ⋀[ringSheafStalk R x]^n (moduleStalk F.val x) :=
  exteriorPowerMap n _ (germₛₗ F x U hU)

lemma extGerm_ιMulti (U : Opens X) (hU : x ∈ U) (m : Fin n → F.val.obj (op U)) :
    extGerm n F x U hU (exteriorPower.ιMulti _ n m) =
      exteriorPower.ιMulti _ n (fun i => sectionGerm F.val x U hU (m i)) :=
  exteriorPowerMap_ιMulti _ _ _ _

lemma extGerm_res {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V)
    (y : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^n (F.val.obj (op U))) :
    extGerm n F x V hV ((moduleSheafExteriorPowerPresheaf n F).map i.op y) =
      extGerm n F x U (i.le hV) y :=
  (exteriorPowerMap_comp n (fun a => (TopCat.Presheaf.germ_res_apply R.obj i x hV a).symm)
    (F.val.restrictₛₗ i.op) (germₛₗ F x V hV) (germₛₗ F x U (i.le hV))
    (fun m => (sectionGerm_res F.val x i hV m).symm) y).symm

/-- The comparison map `(⋀^n F)ₓ → ⋀^n Fₓ` from the stalk of the exterior-power presheaf. -/
noncomputable def extStalkToExt :
    moduleStalk (moduleSheafExteriorPowerPresheaf n F) x ⟶
      AddCommGrpCat.of (⋀[ringSheafStalk R x]^n (moduleStalk F.val x)) :=
  stalkDesc (fun U hU => AddCommGrpCat.ofHom (extGerm n F x U hU).toAddMonoidHom)
    (fun _ _ i hV => AddCommGrpCat.ext fun y => extGerm_res n F x i hV y)

lemma extStalkToExt_germ (U : Opens X) (hU : x ∈ U)
    (y : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^n (F.val.obj (op U))) :
    extStalkToExt n F x (sectionGerm (moduleSheafExteriorPowerPresheaf n F) x U hU y) =
      extGerm n F x U hU y :=
  stalkDesc_germ (P := (moduleSheafExteriorPowerPresheaf n F).presheaf) _ _ U hU y

lemma sectionGerm_ιMulti_res {O V : Opens X} (i : O ⟶ V) (hO : x ∈ O)
    (t : Fin n → F.val.obj (op V)) :
    sectionGerm (moduleSheafExteriorPowerPresheaf n F) x O hO
        (exteriorPower.ιMulti _ n (fun k => res F.val i (t k))) =
      sectionGerm (moduleSheafExteriorPowerPresheaf n F) x V (i.le hO)
        (exteriorPower.ιMulti _ n t) :=
  (congrArg (sectionGerm (moduleSheafExteriorPowerPresheaf n F) x O hO)
    (exteriorPresheaf_restrict_ιMulti n F i.op t).symm).trans
    (sectionGerm_res (moduleSheafExteriorPowerPresheaf n F) x i hO _)

/-- Germs of `m₁ ∧ ⋯ ∧ mₙ` only depend on the germs of the `mᵢ`. -/
lemma sectionGerm_ιMulti_indep {V V' : Opens X} (hV : x ∈ V) (hV' : x ∈ V')
    (t : Fin n → F.val.obj (op V)) (t' : Fin n → F.val.obj (op V'))
    (h : ∀ i, sectionGerm F.val x V hV (t i) = sectionGerm F.val x V' hV' (t' i)) :
    sectionGerm (moduleSheafExteriorPowerPresheaf n F) x V hV (exteriorPower.ιMulti _ n t) =
      sectionGerm (moduleSheafExteriorPowerPresheaf n F) x V' hV'
        (exteriorPower.ιMulti _ n t') := by
  choose W hW iV iV' hW' using fun i =>
    TopCat.Presheaf.germ_eq F.val.presheaf x hV hV' (t i) (t' i) (h i)
  obtain ⟨O₀, hO₀, hO₀W⟩ := exists_open_le_of_finite W hW
  let O := O₀ ⊓ (V ⊓ V')
  have hO : x ∈ O := ⟨hO₀, hV, hV'⟩
  have hOV : O ≤ V := inf_le_right.trans inf_le_left
  have hOV' : O ≤ V' := inf_le_right.trans inf_le_right
  refine (sectionGerm_ιMulti_res n F x (homOfLE hOV) hO t).symm.trans
    (Eq.trans ?_ (sectionGerm_ιMulti_res n F x (homOfLE hOV') hO t'))
  congr 2
  funext i
  have hOi : O ≤ W i := inf_le_left.trans (hO₀W i)
  have e := congrArg (res F.val (homOfLE hOi)) (hW' i)
  change res F.val (homOfLE hOi) (res F.val (iV i) (t i)) =
    res F.val (homOfLE hOi) (res F.val (iV' i) (t' i)) at e
  rw [res_res, res_res] at e
  exact e

lemma extStalkToExt_smul (c : ringSheafStalk R x)
    (s : moduleStalk (moduleSheafExteriorPowerPresheaf n F) x) :
    extStalkToExt n F x (c • s) = c • extStalkToExt n F x s := by
  obtain ⟨U, hU, y, rfl⟩ := exists_sectionGerm (moduleSheafExteriorPowerPresheaf n F) x s
  obtain ⟨W, hWU, hW, d, rfl⟩ := exists_le_ringGerm x c hU
  rw [← sectionGerm_res (moduleSheafExteriorPowerPresheaf n F) x (homOfLE hWU) hW y,
    ← sectionGerm_smul]
  erw [extStalkToExt_germ, extStalkToExt_germ, map_smulₛₗ]

/-- The germ of `m₁ ∧ ⋯ ∧ mₙ` for germs `mᵢ`, computed over a common neighbourhood. -/
noncomputable def extStalkMulti (m : Fin n → moduleStalk F.val x) :
    moduleStalk (moduleSheafExteriorPowerPresheaf n F) x :=
  sectionGerm (moduleSheafExteriorPowerPresheaf n F) x
    (exists_common_sectionGerm F.val m).choose
    (exists_common_sectionGerm F.val m).choose_spec.choose
    (exteriorPower.ιMulti _ n (exists_common_sectionGerm F.val m).choose_spec.choose_spec.choose)

lemma extStalkMulti_eq {V : Opens X} (hV : x ∈ V) (t : Fin n → F.val.obj (op V))
    (m : Fin n → moduleStalk F.val x) (ht : ∀ i, sectionGerm F.val x V hV (t i) = m i) :
    extStalkMulti n F x m =
      sectionGerm (moduleSheafExteriorPowerPresheaf n F) x V hV (exteriorPower.ιMulti _ n t) :=
  sectionGerm_ιMulti_indep n F x _ hV _ t fun i =>
    ((exists_common_sectionGerm F.val m).choose_spec.choose_spec.choose_spec i).trans (ht i).symm

lemma sectionGerm_update [DecidableEq (Fin n)] {V : Opens X} (hV : x ∈ V)
    (t : Fin n → F.val.obj (op V))
    (m : Fin n → moduleStalk F.val x) (ht : ∀ i, sectionGerm F.val x V hV (t i) = m i)
    (i : Fin n) (s : F.val.obj (op V)) (a : moduleStalk F.val x)
    (hs : sectionGerm F.val x V hV s = a) (j : Fin n) :
    sectionGerm F.val x V hV (Function.update t i s j) = Function.update m i a j := by
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self, Function.update_self, hs]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj, ht]

/-- The alternating map `(Fₓ)ⁿ → (⋀^n F)ₓ`, `(m₁, …, mₙ) ↦ (m₁ ∧ ⋯ ∧ mₙ)ₓ`. -/
noncomputable def extStalkAlt :
    moduleStalk F.val x [⋀^Fin n]→ₗ[ringSheafStalk R x]
      moduleStalk (moduleSheafExteriorPowerPresheaf n F) x where
  toFun := extStalkMulti n F x
  map_update_add' m i a b := by
    obtain ⟨V, hV, t, ht⟩ := exists_common_sectionGerm F.val (Sum.elim m ![a, b])
    have htm : ∀ j, sectionGerm F.val x V hV (t (Sum.inl j)) = m j := fun j => ht (Sum.inl j)
    have ha : sectionGerm F.val x V hV (t (Sum.inr 0)) = a := ht (Sum.inr 0)
    have hb : sectionGerm F.val x V hV (t (Sum.inr 1)) = b := ht (Sum.inr 1)
    have hab : sectionGerm F.val x V hV (t (Sum.inr 0) + t (Sum.inr 1)) = a + b := by
      rw [map_add, ha, hb]
    rw [extStalkMulti_eq n F x hV _ _ (sectionGerm_update n F x hV _ m htm i _ _ hab),
      extStalkMulti_eq n F x hV _ _ (sectionGerm_update n F x hV _ m htm i _ _ ha),
      extStalkMulti_eq n F x hV _ _ (sectionGerm_update n F x hV _ m htm i _ _ hb),
      AlternatingMap.map_update_add]
    exact map_add (sectionGerm (moduleSheafExteriorPowerPresheaf n F) x V hV) _ _
  map_update_smul' m i c a := by
    obtain ⟨V, hV, t, ht⟩ := exists_common_sectionGerm F.val (Sum.elim m ![a])
    obtain ⟨W, hWV, hW, d, rfl⟩ := exists_le_ringGerm x c hV
    let t' := fun k => res F.val (homOfLE hWV) (t k)
    have ht' : ∀ k, sectionGerm F.val x W hW (t' k) = Sum.elim m ![a] k := fun k =>
      (sectionGerm_res F.val x (homOfLE hWV) hW (t k)).trans (ht k)
    have htm : ∀ j, sectionGerm F.val x W hW (t' (Sum.inl j)) = m j := fun j => ht' (Sum.inl j)
    have ha : sectionGerm F.val x W hW (t' (Sum.inr 0)) = a := ht' (Sum.inr 0)
    have hca : sectionGerm F.val x W hW (d • t' (Sum.inr 0)) =
        TopCat.Presheaf.germ R.obj W x hW d • a := by
      rw [sectionGerm_smul, ha]
    rw [extStalkMulti_eq n F x hW _ _ (sectionGerm_update n F x hW _ m htm i _ _ hca),
      extStalkMulti_eq n F x hW _ _ (sectionGerm_update n F x hW _ m htm i _ _ ha),
      AlternatingMap.map_update_smul]
    exact sectionGerm_smul (moduleSheafExteriorPowerPresheaf n F) x W hW d _
  map_eq_zero_of_eq' m i j hij hne := by
    obtain ⟨V, hV, t, ht⟩ := exists_common_sectionGerm F.val m
    obtain ⟨W, hW, iV, iV', he⟩ := TopCat.Presheaf.germ_eq F.val.presheaf x hV hV (t i) (t j)
      ((ht i).trans (hij.trans (ht j).symm))
    rw [Subsingleton.elim iV' iV] at he
    have ht' : ∀ k, sectionGerm F.val x W hW (res F.val iV (t k)) = m k := fun k =>
      (sectionGerm_res F.val x iV hW (t k)).trans (ht k)
    rw [extStalkMulti_eq n F x hW _ m ht',
      AlternatingMap.map_eq_zero_of_eq _ _ (i := i) (j := j) he hne]
    exact map_zero (sectionGerm (moduleSheafExteriorPowerPresheaf n F) x W hW)

/-- The comparison map `⋀^n Fₓ → (⋀^n F)ₓ`. -/
noncomputable def extToExtStalk :
    ⋀[ringSheafStalk R x]^n (moduleStalk F.val x) →ₗ[ringSheafStalk R x]
      moduleStalk (moduleSheafExteriorPowerPresheaf n F) x :=
  exteriorPower.alternatingMapLinearEquiv (extStalkAlt n F x)

lemma extToExtStalk_ιMulti (m : Fin n → moduleStalk F.val x) :
    extToExtStalk n F x (exteriorPower.ιMulti _ n m) = extStalkMulti n F x m :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

lemma extToExtStalk_extGerm (U : Opens X) (hU : x ∈ U)
    (y : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^n (F.val.obj (op U))) :
    extToExtStalk n F x (extGerm n F x U hU y) =
      sectionGerm (moduleSheafExteriorPowerPresheaf n F) x U hU y := by
  have hy : y ∈ Submodule.span ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
      (Set.range (exteriorPower.ιMulti ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) n
        (M := F.val.obj (op U)))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, rfl⟩ := hy
    rw [extGerm_ιMulti, extToExtStalk_ιMulti]
    exact extStalkMulti_eq n F x hU m _ fun _ => rfl
  | zero =>
    rw [map_zero, map_zero]
    exact (map_zero (sectionGerm (moduleSheafExteriorPowerPresheaf n F) x U hU)).symm
  | add y z _ _ hy hz =>
    rw [map_add, map_add, hy, hz]
    exact (map_add (sectionGerm (moduleSheafExteriorPowerPresheaf n F) x U hU) y z).symm
  | smul c y _ hy =>
    rw [map_smulₛₗ, LinearMap.map_smul, hy]
    exact (sectionGerm_smul (moduleSheafExteriorPowerPresheaf n F) x U hU c y).symm

lemma extStalkToExt_extToExtStalk (z : ⋀[ringSheafStalk R x]^n (moduleStalk F.val x)) :
    extStalkToExt n F x (extToExtStalk n F x z) = z := by
  have hz : z ∈ Submodule.span (ringSheafStalk R x)
      (Set.range (exteriorPower.ιMulti (ringSheafStalk R x) n (M := moduleStalk F.val x))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    obtain ⟨V, hV, t, ht⟩ := exists_common_sectionGerm F.val m
    rw [extToExtStalk_ιMulti, extStalkMulti_eq n F x hV t m ht, extStalkToExt_germ,
      extGerm_ιMulti]
    exact congrArg _ (funext ht)
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul c y _ hy => rw [LinearMap.map_smul, extStalkToExt_smul, hy]

/-- **Exterior powers commute with stalks.** `⋀^n (Fₓ) ≃ (⋀^n F)ₓ` over `𝒪_{X,x}`, where
`(⋀^n F)ₓ` is the stalk of the presheaf `U ↦ ⋀^n F(U)`. -/
noncomputable def extStalkEquiv :
    ⋀[ringSheafStalk R x]^n (moduleStalk F.val x) ≃ₗ[ringSheafStalk R x]
      moduleStalk (moduleSheafExteriorPowerPresheaf n F) x where
  __ := extToExtStalk n F x
  invFun := extStalkToExt n F x
  left_inv := extStalkToExt_extToExtStalk n F x
  right_inv s := by
    obtain ⟨U, hU, y, rfl⟩ := exists_sectionGerm (moduleSheafExteriorPowerPresheaf n F) x s
    change extToExtStalk n F x (extStalkToExt n F x _) = _
    erw [extStalkToExt_germ]
    exact extToExtStalk_extGerm n F x U hU y

lemma extStalkEquiv_symm_germ (U : Opens X) (hU : x ∈ U)
    (y : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^n (F.val.obj (op U))) :
    (extStalkEquiv n F x).symm (sectionGerm (moduleSheafExteriorPowerPresheaf n F) x U hU y) =
      extGerm n F x U hU y :=
  extStalkToExt_germ n F x U hU y

end ExteriorStalk

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

/-- The wedge-product morphism `⋀^p F' ⊗ ⋀^{r-p} F → ⋀^r F` induced by `f : F' ⟶ F`: the
sheafification of `x ⊗ y ↦ (⋀^p f)(x) ∧ y` on sections. -/
noncomputable def wedgeSheafMap {r p : ℕ} (hp : p ≤ r) :
    moduleSheafTensor (moduleSheafExteriorPower p F') (moduleSheafExteriorPower (r - p) F) ⟶
      (moduleSheafExteriorPower r F : SheafOfModules.{u} (ringCatSheafOf R)) :=
  (sheafifyTensorIso F' F p (r - p)).inv ≫ sheafifyMap (alphaPre f hp) ≫ (extPowIso F r).hom

/-- The standard filtration is the filtration by the images of the wedge-product morphisms
`⋀^p F' ⊗ ⋀^{r-p} F → ⋀^r F`. -/
theorem filSh_eq_imageSubobject {r p : ℕ} (hp : p ≤ r) :
    filSh f r p = imageSubobject (wedgeSheafMap f hp) := by
  have hfac : alphaPre f hp = alphaTo f hp ≫ (filPre f r p).ι := by
    ext U z
    rfl
  have hepi : Epi (alphaTo f hp) := PresheafOfModules.epi_of_surjective fun U w => by
    obtain ⟨w, hw⟩ := w
    have hw' : w ∈ LinearMap.range (ExteriorPowerFiltration.alpha (f.val.app U).hom hp) := by
      rw [← ExteriorPowerFiltration.filt_of_le _ hp]
      exact hw
    obtain ⟨z, rfl⟩ := hw'
    exact ⟨z, rfl⟩
  have : Epi ((sheafifyTensorIso F' F p (r - p)).inv ≫ sheafifyMap (alphaTo f hp)) := by
    have : Epi (sheafifyMap (alphaTo f hp)) := Functor.map_epi _ _
    exact epi_comp _ _
  have hcomm : ((sheafifyTensorIso F' F p (r - p)).inv ≫ sheafifyMap (alphaTo f hp)) ≫
      filArrow f r p = wedgeSheafMap f hp := by
    have hmap : sheafifyMap (alphaTo f hp ≫ (filPre f r p).ι) =
        sheafifyMap (alphaTo f hp) ≫ sheafifyMap (filPre f r p).ι := Functor.map_comp _ _ _
    rw [wedgeSheafMap, filArrow, hfac, hmap]
    simp only [Category.assoc]
  have : StrongEpi ((sheafifyTensorIso F' F p (r - p)).inv ≫ sheafifyMap (alphaTo f hp)) :=
    strongEpi_of_epi _
  rw [filSh, imageSubobject]
  exact Subobject.mk_eq_mk_of_comm _ _ (image.isoStrongEpiMono _ _ hcomm)
    (image.isoStrongEpiMono_hom_comp_ι _ _ hcomm)

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

end SheafLevel

section StalkFiltration

open ModuleSheafTensor

variable {x : X}

lemma exists_res_eq_zero_of_sectionGerm_eq_zero
    {M : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} {U : Opens X}
    (hU : x ∈ U) (s : M.obj (op U)) (h : sectionGerm M x U hU s = 0) :
    ∃ (W : Opens X) (i : W ⟶ U), x ∈ W ∧ M.map i.op s = 0 := by
  obtain ⟨W, hW, i, j, e⟩ := TopCat.Presheaf.germ_eq M.presheaf x hU hU s 0
    (h.trans (map_zero (sectionGerm M x U hU)).symm)
  refine ⟨W, i, hW, ?_⟩
  change M.presheaf.map i.op s = 0
  rw [e]
  exact map_zero _

lemma sectionGerm_quotient_mk_eq_zero
    {M : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} (N : M.Submodule)
    {U W : Opens X} (i : W ⟶ U) (hW : x ∈ W) (z : M.obj (op U)) (hz : M.map i.op z ∈ N.obj (op W)) :
    sectionGerm (quotientPresheaf N) x U (i.le hW)
      (Submodule.Quotient.mk z : M.obj (op U) ⧸ N.obj (op U)) = 0 := by
  refine (sectionGerm_res (quotientPresheaf N) x i hW _).symm.trans ?_
  change sectionGerm (quotientPresheaf N) x W hW
    (Submodule.Quotient.mk (M.map i.op z) : M.obj (op W) ⧸ N.obj (op W)) = 0
  have h0 : (Submodule.Quotient.mk (M.map i.op z) : M.obj (op W) ⧸ N.obj (op W)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hz
  exact (congrArg (sectionGerm (quotientPresheaf N) x W hW) h0).trans (map_zero _)

lemma stalkAddMap_injective_of_germ
    {P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} (φ : P ⟶ Q)
    (h : ∀ (U : Opens X) (hU : x ∈ U) (s : P.obj (op U)),
      sectionGerm Q x U hU (φ.app (op U) s) = 0 → sectionGerm P x U hU s = 0) :
    Function.Injective (Ringed.stalkAddMap φ x) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨U, hU, s, rfl⟩ := exists_sectionGerm P x a
  rw [Ringed.stalkAddMap_germ] at ha
  exact h U hU s ha

lemma stalkAddMap_surjective_of_germ
    {P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} (φ : P ⟶ Q)
    (h : ∀ (U : Opens X) (hU : x ∈ U) (t : Q.obj (op U)), ∃ (V : Opens X) (hV : x ∈ V)
      (s : P.obj (op V)), sectionGerm Q x V hV (φ.app (op V) s) = sectionGerm Q x U hU t) :
    Function.Surjective (Ringed.stalkAddMap φ x) := by
  intro b
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm Q x b
  obtain ⟨V, hV, s, hs⟩ := h U hU t
  exact ⟨sectionGerm P x V hV s, (Ringed.stalkAddMap_germ φ x V hV s).trans hs⟩

variable (x)

/-- The germ map `𝒪_X(U) → 𝒪_{X,x}`. -/
noncomputable abbrev ringGerm (U : Opens X) (hU : x ∈ U) :
    (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) →+* ringSheafStalk R x :=
  (TopCat.Presheaf.germ R.obj U x hU).hom

/-- The stalk of `U ↦ ⋀^a P(U) ⊗ ⋀^b Q(U)` is `⋀^a Pₓ ⊗ ⋀^b Qₓ`. -/
noncomputable def tensorExtStalkEquiv (a b : ℕ) (P Q : SheafOfModules.{u} (ringCatSheafOf R)) :
    moduleStalk (moduleSheafExteriorPowerPresheaf a P ⊗ moduleSheafExteriorPowerPresheaf b Q) x
      ≃ₗ[ringSheafStalk R x]
      ⋀[ringSheafStalk R x]^a (moduleStalk P.val x) ⊗[ringSheafStalk R x]
        ⋀[ringSheafStalk R x]^b (moduleStalk Q.val x) :=
  presheafTensorStalkIso _ _ x ≪≫ₗ
    TensorProduct.congr (extStalkEquiv a P x).symm (extStalkEquiv b Q x).symm

lemma tensorExtStalkEquiv_germ_tmul (a b : ℕ) (P Q : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (hU : x ∈ U)
    (y : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^a (P.val.obj (op U)))
    (y' : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^b (Q.val.obj (op U))) :
    tensorExtStalkEquiv x a b P Q
        (sectionGerm (moduleSheafExteriorPowerPresheaf a P ⊗ moduleSheafExteriorPowerPresheaf b Q)
          x U hU (y ⊗ₜ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] y')) =
      extGerm a P x U hU y ⊗ₜ[ringSheafStalk R x] extGerm b Q x U hU y' := by
  change TensorProduct.congr (extStalkEquiv a P x).symm (extStalkEquiv b Q x).symm
    (presheafTensorStalkToTensor _ _ x
      (sectionGerm _ x U hU (y ⊗ₜ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] y'))) = _
  rw [presheafTensorStalkToTensor_germ]
  erw [tensorStalkComponent_tmul]
  rw [TensorProduct.congr_tmul]
  erw [extStalkEquiv_symm_germ, extStalkEquiv_symm_germ]

/-- The germ map `⋀^a P(U) ⊗ ⋀^b Q(U) → ⋀^a Pₓ ⊗ ⋀^b Qₓ`, semilinear over `𝒪_X(U) → 𝒪_{X,x}`. -/
noncomputable def tensorExtGerm (a b : ℕ) (P Q : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (hU : x ∈ U) :
    (⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^a (P.val.obj (op U)) ⊗[
      (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]
      ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^b (Q.val.obj (op U))) →ₛₗ[
      ringGerm (R := R) x U hU]
      ⋀[ringSheafStalk R x]^a (moduleStalk P.val x) ⊗[ringSheafStalk R x]
        ⋀[ringSheafStalk R x]^b (moduleStalk Q.val x) where
  toFun t := tensorExtStalkEquiv x a b P Q
    (sectionGerm (moduleSheafExteriorPowerPresheaf a P ⊗ moduleSheafExteriorPowerPresheaf b Q)
      x U hU t)
  map_add' s t := (congrArg (tensorExtStalkEquiv x a b P Q)
    (map_add (sectionGerm (moduleSheafExteriorPowerPresheaf a P ⊗
      moduleSheafExteriorPowerPresheaf b Q) x U hU) s t)).trans (map_add _ _ _)
  map_smul' c t := (congrArg (tensorExtStalkEquiv x a b P Q)
    (sectionGerm_smul (moduleSheafExteriorPowerPresheaf a P ⊗
      moduleSheafExteriorPowerPresheaf b Q) x U hU c t)).trans (LinearEquiv.map_smul _ _ _)

lemma tensorExtGerm_tmul (a b : ℕ) (P Q : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (hU : x ∈ U)
    (y : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^a (P.val.obj (op U)))
    (y' : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^b (Q.val.obj (op U))) :
    tensorExtGerm x a b P Q U hU (y ⊗ₜ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] y') =
      extGerm a P x U hU y ⊗ₜ[ringSheafStalk R x] extGerm b Q x U hU y' :=
  tensorExtStalkEquiv_germ_tmul x a b P Q U hU y y'

variable {F' F F'' : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F) (g : F ⟶ F'')

set_option maxHeartbeats 1000000 in
/-- `α_p` commutes with taking stalks. -/
lemma extGerm_alpha {p r : ℕ} (hp : p ≤ r) (U : Opens X) (hU : x ∈ U)
    (t : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^p (F'.val.obj (op U)) ⊗[
      (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]
      ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^(r - p) (F.val.obj (op U))) :
    extGerm r F x U hU (ExteriorPowerFiltration.alpha (f.val.app (op U)).hom hp t) =
      ExteriorPowerFiltration.alpha (Ringed.stalkLinearMap f.val x) hp
        (tensorExtGerm x p (r - p) F' F U hU t) := by
  have gen : ∀ m₁ m₂, extGerm r F x U hU (ExteriorPowerFiltration.alpha (f.val.app (op U)).hom hp
      (exteriorPower.ιMulti _ p m₁ ⊗ₜ exteriorPower.ιMulti _ (r - p) m₂)) =
      ExteriorPowerFiltration.alpha (Ringed.stalkLinearMap f.val x) hp
        (tensorExtGerm x p (r - p) F' F U hU
          (exteriorPower.ιMulti _ p m₁ ⊗ₜ exteriorPower.ιMulti _ (r - p) m₂)) := by
    intro m₁ m₂
    rw [tensorExtGerm_tmul]
    rw [extGerm_ιMulti, extGerm_ιMulti]
    unfold ExteriorPowerFiltration.alpha
    rw [ExteriorPowerFiltration.wedgeMap_ιMulti, ExteriorPowerFiltration.wedgeMap_ιMulti]
    rw [extGerm_ιMulti]
    congr 1
    funext k
    simp only [Function.comp_apply]
    generalize Fin.cast _ k = j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left, Function.comp_apply]
      exact (Ringed.stalkAddMap_germ f.val x U hU (m₁ j)).symm
    · simp only [Fin.append_right, Function.comp_apply, LinearMap.id_apply]
  have key : (extGerm r F x U hU).comp (ExteriorPowerFiltration.alpha (f.val.app (op U)).hom hp) =
      (ExteriorPowerFiltration.alpha (Ringed.stalkLinearMap f.val x) hp).comp
        (tensorExtGerm x p (r - p) F' F U hU) :=
    tensor_exteriorPower_semilinear_ext gen
  exact LinearMap.congr_fun key t

set_option maxHeartbeats 1000000 in
/-- `id ⊗ ⋀^q g` commutes with taking stalks. -/
lemma tensorExtGerm_lTensor {p q : ℕ} (U : Opens X) (hU : x ∈ U)
    (t : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^p (F'.val.obj (op U)) ⊗[
      (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]
      ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^q (F.val.obj (op U))) :
    tensorExtGerm x p q F' F'' U hU
        (LinearMap.lTensor (⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^p
          (F'.val.obj (op U))) (exteriorPower.map q (g.val.app (op U)).hom) t) =
      LinearMap.lTensor (⋀[ringSheafStalk R x]^p (moduleStalk F'.val x))
        (exteriorPower.map q (Ringed.stalkLinearMap g.val x))
        (tensorExtGerm x p q F' F U hU t) := by
  have gen : ∀ m₁ m₂, tensorExtGerm x p q F' F'' U hU
      (LinearMap.lTensor (⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^p
        (F'.val.obj (op U))) (exteriorPower.map q (g.val.app (op U)).hom)
        (exteriorPower.ιMulti _ p m₁ ⊗ₜ exteriorPower.ιMulti _ q m₂)) =
      LinearMap.lTensor (⋀[ringSheafStalk R x]^p (moduleStalk F'.val x))
        (exteriorPower.map q (Ringed.stalkLinearMap g.val x))
        (tensorExtGerm x p q F' F U hU
          (exteriorPower.ιMulti _ p m₁ ⊗ₜ exteriorPower.ιMulti _ q m₂)) := by
    intro m₁ m₂
    rw [LinearMap.lTensor_tmul, tensorExtGerm_tmul, tensorExtGerm_tmul, LinearMap.lTensor_tmul,
      exteriorPower.map_apply_ιMulti, extGerm_ιMulti, extGerm_ιMulti, extGerm_ιMulti,
      exteriorPower.map_apply_ιMulti]
    congr 2
    funext k
    exact (Ringed.stalkAddMap_germ g.val x U hU (m₂ k)).symm
  have key : (tensorExtGerm x p q F' F'' U hU).comp
      (LinearMap.lTensor (⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^p
        (F'.val.obj (op U))) (exteriorPower.map q (g.val.app (op U)).hom)) =
      (LinearMap.lTensor (⋀[ringSheafStalk R x]^p (moduleStalk F'.val x))
        (exteriorPower.map q (Ringed.stalkLinearMap g.val x))).comp
        (tensorExtGerm x p q F' F U hU) := by
    refine tensor_exteriorPower_semilinear_ext
      (A := (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
      (B := ringSheafStalk R x) (σ := ringGerm x U hU) (M₁ := F'.val.obj (op U))
      (M₂ := F.val.obj (op U)) (a := p) (b := q)
      (N := ⋀[ringSheafStalk R x]^p (moduleStalk F'.val x) ⊗[ringSheafStalk R x]
        ⋀[ringSheafStalk R x]^q (moduleStalk F''.val x)) fun m₁ m₂ => ?_
    exact gen m₁ m₂
  exact LinearMap.congr_fun key t

/-- Germs of the filtration `F^q ⊆ ⋀^r F` land in the filtration of `⋀^r Fₓ`. -/
lemma extGerm_mem_filt {q r : ℕ} (U : Opens X) (hU : x ∈ U)
    (y : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^r (F.val.obj (op U)))
    (hy : y ∈ ExteriorPowerFiltration.filt (f.val.app (op U)).hom r q) :
    extGerm r F x U hU y ∈ ExteriorPowerFiltration.filt (Ringed.stalkLinearMap f.val x) r q := by
  rcases Nat.lt_or_ge r q with hq | hq
  · rw [ExteriorPowerFiltration.filt_of_lt _ hq] at hy ⊢
    rw [(Submodule.mem_bot _).1 hy, map_zero]
    exact Submodule.zero_mem _
  · rw [ExteriorPowerFiltration.filt_of_le _ hq] at hy ⊢
    obtain ⟨t, rfl⟩ := hy
    exact ⟨tensorExtGerm x q (r - q) F' F U hU t, (extGerm_alpha x f hq U hU t).symm⟩

/-- If the germ of `y ∈ ⋀^r F(U)` lies in the filtration of `⋀^r Fₓ`, then `y` lies in the
filtration near `x`. -/
lemma exists_mem_filt_of_extGerm {q r : ℕ} (U : Opens X) (hU : x ∈ U)
    (y : ⋀[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^r (F.val.obj (op U)))
    (hy : extGerm r F x U hU y ∈ ExteriorPowerFiltration.filt (Ringed.stalkLinearMap f.val x) r q) :
    ∃ (W : Opens X) (i : W ⟶ U), x ∈ W ∧ (moduleSheafExteriorPowerPresheaf r F).map i.op y ∈
      ExteriorPowerFiltration.filt (f.val.app (op W)).hom r q := by
  rcases Nat.lt_or_ge r q with hq | hq
  · rw [ExteriorPowerFiltration.filt_of_lt _ hq] at hy
    have h0 : sectionGerm (moduleSheafExteriorPowerPresheaf r F) x U hU y = 0 := by
      apply (extStalkEquiv r F x).symm.injective
      rw [extStalkEquiv_symm_germ, map_zero]
      exact (Submodule.mem_bot _).1 hy
    obtain ⟨W, i, hW, e⟩ := exists_res_eq_zero_of_sectionGerm_eq_zero hU _ h0
    refine ⟨W, i, hW, ?_⟩
    rw [e]
    exact Submodule.zero_mem _
  · rw [ExteriorPowerFiltration.filt_of_le _ hq] at hy
    obtain ⟨w, hw⟩ := hy
    obtain ⟨w', rfl⟩ := (tensorExtStalkEquiv x q (r - q) F' F).surjective w
    obtain ⟨V, hV, t, rfl⟩ := exists_sectionGerm
      (moduleSheafExteriorPowerPresheaf q F' ⊗ moduleSheafExteriorPowerPresheaf (r - q) F) x w'
    have e1 : extGerm r F x V hV ((alphaPre f hq).app (op V) t) = extGerm r F x U hU y :=
      (extGerm_alpha x f hq V hV t).trans hw
    have e2 : sectionGerm (moduleSheafExteriorPowerPresheaf r F) x V hV
        ((alphaPre f hq).app (op V) t) =
          sectionGerm (moduleSheafExteriorPowerPresheaf r F) x U hU y := by
      apply (extStalkEquiv r F x).symm.injective
      erw [extStalkEquiv_symm_germ, extStalkEquiv_symm_germ]
      exact e1
    obtain ⟨W, hW, iV, iU, e3⟩ := TopCat.Presheaf.germ_eq _ x hV hU _ _ e2
    refine ⟨W, iU, hW, ?_⟩
    rw [ExteriorPowerFiltration.filt_of_le _ hq]
    refine ⟨_, (PresheafOfModules.naturality_apply (alphaPre f hq) iV.op t).trans ?_⟩
    exact e3

variable {x} in
/-- A class in the comparison presheaf has zero germ as soon as `α_p(z)` has germ in the
filtration step `p + 1` and `(id ⊗ ⋀^{r-p} g)(z)` has zero germ. -/
lemma sectionGerm_apex_mk_eq_zero {p r : ℕ} (hp : p ≤ r) {U : Opens X} (hU : x ∈ U)
    (z : (moduleSheafExteriorPowerPresheaf p F' ⊗ moduleSheafExteriorPowerPresheaf (r - p) F).obj
      (op U))
    (h1 : extGerm r F x U hU ((alphaPre f hp).app (op U) z) ∈
      ExteriorPowerFiltration.filt (Ringed.stalkLinearMap f.val x) r (p + 1))
    (h2 : sectionGerm (moduleSheafExteriorPowerPresheaf p F' ⊗
      moduleSheafExteriorPowerPresheaf (r - p) F'') x U hU ((betaPre g p r).app (op U) z) = 0) :
    sectionGerm (apexPre f g hp) x U hU (Submodule.Quotient.mk z) = 0 := by
  obtain ⟨W₁, i₁, hW₁, hm⟩ := exists_mem_filt_of_extGerm x f U hU _ h1
  obtain ⟨W₂, i₂, hW₂, hz⟩ := exists_res_eq_zero_of_sectionGerm_eq_zero hU _ h2
  let j₁ : W₁ ⊓ W₂ ⟶ W₁ := homOfLE inf_le_left
  let j₂ : W₁ ⊓ W₂ ⟶ W₂ := homOfLE inf_le_right
  refine sectionGerm_quotient_mk_eq_zero (kerSub f g hp) (j₁ ≫ i₁) ⟨hW₁, hW₂⟩ z ⟨?_, ?_⟩
  · change (alphaPre f hp).app _ (_ : (moduleSheafExteriorPowerPresheaf p F' ⊗
      moduleSheafExteriorPowerPresheaf (r - p) F).obj _) ∈ (filPre f r (p + 1)).obj _
    rw [PresheafOfModules.naturality_apply, op_comp, PresheafOfModules.map_comp_apply]
    exact (filPre f r (p + 1)).map_mem j₁.op hm
  · change (betaPre g p r).app _ (_ : (moduleSheafExteriorPowerPresheaf p F' ⊗
      moduleSheafExteriorPowerPresheaf (r - p) F).obj _) = 0
    rw [PresheafOfModules.naturality_apply, Subsingleton.elim (j₁ ≫ i₁) (j₂ ≫ i₂), op_comp,
      PresheafOfModules.map_comp_apply, hz]
    exact map_zero _

end StalkFiltration

section StalkBijective

open ModuleSheafTensor

variable {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))} (hS : S.ShortExact) (x : X)
include hS

lemma stalk_f_injective : Function.Injective (Ringed.stalkLinearMap S.f.val x) := by
  have := hS.mono_f
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨U, hU, s, rfl⟩ := exists_sectionGerm S.X₁.val x a
  rw [Ringed.stalkLinearMap_apply, Ringed.stalkAddMap_germ] at ha
  obtain ⟨W, i, hW, e⟩ := exists_res_eq_zero_of_sectionGerm_eq_zero hU _ ha
  rw [← PresheafOfModules.naturality_apply] at e
  have e' := app_injective_of_mono S.f (op W) (e.trans (map_zero _).symm)
  refine (sectionGerm_res S.X₁.val x i hW s).symm.trans ?_
  change sectionGerm S.X₁.val x W hW (S.X₁.val.map i.op s) = 0
  rw [e']
  exact map_zero _

lemma stalk_g_surjective : Function.Surjective (Ringed.stalkLinearMap S.g.val x) := by
  have := hS.epi_g
  intro b
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm S.X₃.val x b
  obtain ⟨V, hVU, hV, s, hs⟩ := exists_local_lift S.g t hU
  refine ⟨sectionGerm S.X₂.val x V hV s, ?_⟩
  rw [Ringed.stalkLinearMap_apply, Ringed.stalkAddMap_germ, hs]
  exact sectionGerm_res S.X₃.val x (homOfLE hVU) hV t

lemma stalk_range_eq_ker :
    LinearMap.range (Ringed.stalkLinearMap S.f.val x) =
      LinearMap.ker (Ringed.stalkLinearMap S.g.val x) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨U, hU, s, rfl⟩ := exists_sectionGerm S.X₁.val x a
    rw [LinearMap.mem_ker, Ringed.stalkLinearMap_apply, Ringed.stalkLinearMap_apply,
      Ringed.stalkAddMap_germ, Ringed.stalkAddMap_germ]
    have h : S.g.val.app (op U) (S.f.val.app (op U) s) = 0 := by
      have := congrArg (fun φ : S.X₁ ⟶ S.X₃ => φ.val.app (op U) s) S.zero
      exact this
    rw [h]
    exact map_zero _
  · intro b hb
    obtain ⟨U, hU, s, rfl⟩ := exists_sectionGerm S.X₂.val x b
    rw [LinearMap.mem_ker, Ringed.stalkLinearMap_apply, Ringed.stalkAddMap_germ] at hb
    obtain ⟨W, i, hW, e⟩ := exists_res_eq_zero_of_sectionGerm_eq_zero hU _ hb
    rw [← PresheafOfModules.naturality_apply] at e
    have hmem : S.X₂.val.map i.op s ∈ LinearMap.ker (S.g.val.app (op W)).hom := e
    rw [← range_eq_ker_of_shortExact hS] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨sectionGerm S.X₁.val x W hW a, ?_⟩
    rw [Ringed.stalkLinearMap_apply, Ringed.stalkAddMap_germ]
    exact (congrArg (sectionGerm S.X₂.val x W hW) ha).trans (sectionGerm_res S.X₂.val x i hW s)

variable (h₁ : Ringed.IsLocallyFree S.X₁) (h₃ : Ringed.IsLocallyFree S.X₃)
include h₁ h₃

omit h₁ in
lemma exists_stalk_section :
    ∃ s : moduleStalk S.X₃.val x →ₗ[ringSheafStalk R x] moduleStalk S.X₂.val x,
      Ringed.stalkLinearMap S.g.val x ∘ₗ s = LinearMap.id := by
  have : Module.Free (ringSheafStalk R x) (moduleStalk S.X₃.val x) :=
    Ringed.moduleStalk_free_of_isLocallyFree h₃ x
  exact Module.projective_lifting_property _ _ (stalk_g_surjective hS x)

lemma alpha_mem_filt_succ_iff_stalk {p r : ℕ} (hp : p ≤ r)
    (z : ⋀[ringSheafStalk R x]^p (moduleStalk S.X₁.val x) ⊗[ringSheafStalk R x]
      ⋀[ringSheafStalk R x]^(r - p) (moduleStalk S.X₂.val x)) :
    ExteriorPowerFiltration.alpha (Ringed.stalkLinearMap S.f.val x) hp z ∈
        ExteriorPowerFiltration.filt (Ringed.stalkLinearMap S.f.val x) r (p + 1) ↔
      LinearMap.lTensor _ (exteriorPower.map (r - p) (Ringed.stalkLinearMap S.g.val x)) z = 0 := by
  obtain ⟨s, hs⟩ := exists_stalk_section hS x h₃
  have : Module.Free (ringSheafStalk R x) (moduleStalk S.X₁.val x) :=
    Ringed.moduleStalk_free_of_isLocallyFree h₁ x
  have : Module.Free (ringSheafStalk R x) (moduleStalk S.X₃.val x) :=
    Ringed.moduleStalk_free_of_isLocallyFree h₃ x
  exact ExteriorPowerFiltration.alpha_mem_filt_succ_iff (stalk_range_eq_ker hS x) hs
    (stalk_f_injective hS x) hp z

/-- The comparison map to the graded piece is bijective on stalks. -/
theorem stalk_toGrad_bijective {p r : ℕ} (hp : p ≤ r) :
    Function.Bijective (Ringed.stalkAddMap (toGrad S.f S.g hp) x) := by
  refine ⟨stalkAddMap_injective_of_germ _ fun U hU s hs => ?_,
    stalkAddMap_surjective_of_germ _ fun U hU t => ?_⟩
  · induction s using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨W, i, hW, e⟩ := exists_res_eq_zero_of_sectionGerm_eq_zero hU _ hs
      change (Submodule.Quotient.mk _ : _ ⧸ (gradSub S.f r p).obj (op W)) = 0 at e
      have h1 : (moduleSheafExteriorPowerPresheaf r S.X₂).map i.op
          ((alphaPre S.f hp).app (op U) z) ∈ (filPre S.f r (p + 1)).obj (op W) := by
        have := (Submodule.Quotient.mk_eq_zero _).1 e
        exact this
      have h2 : extGerm r S.X₂ x U hU ((alphaPre S.f hp).app (op U) z) ∈
          ExteriorPowerFiltration.filt (Ringed.stalkLinearMap S.f.val x) r (p + 1) := by
        have := extGerm_mem_filt x S.f W hW _ h1
        convert this using 1
        exact (extGerm_res r S.X₂ x i hW _).symm
      have h3 := h2
      erw [extGerm_alpha x S.f hp] at h3
      rw [alpha_mem_filt_succ_iff_stalk hS x h₁ h₃ hp, ← tensorExtGerm_lTensor x S.g U hU z] at h3
      have h4 : sectionGerm (moduleSheafExteriorPowerPresheaf p S.X₁ ⊗
          moduleSheafExteriorPowerPresheaf (r - p) S.X₃) x U hU
          ((betaPre S.g p r).app (op U) z) = 0 :=
        (tensorExtStalkEquiv x p (r - p) S.X₁ S.X₃).map_eq_zero_iff.1 h3
      exact sectionGerm_apex_mk_eq_zero S.f S.g hp hU z h2 h4
  · induction t using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨w, hw⟩ := w
      have hw' : w ∈ LinearMap.range
          (ExteriorPowerFiltration.alpha (S.f.val.app (op U)).hom hp) := by
        rw [← ExteriorPowerFiltration.filt_of_le _ hp]
        exact hw
      obtain ⟨z, rfl⟩ := hw'
      exact ⟨U, hU, Submodule.Quotient.mk z, rfl⟩

/-- The comparison map to `⋀^p F' ⊗ ⋀^{r-p} F''` is bijective on stalks. -/
theorem stalk_toH_bijective {p r : ℕ} (hp : p ≤ r) :
    Function.Bijective (Ringed.stalkAddMap (toH S.f S.g hp) x) := by
  refine ⟨stalkAddMap_injective_of_germ _ fun U hU s hs => ?_,
    stalkAddMap_surjective_of_germ _ fun U hU t => ?_⟩
  · induction s using Submodule.Quotient.induction_on with
    | H z =>
      have h3 : tensorExtGerm x p (r - p) S.X₁ S.X₃ U hU
          ((betaPre S.g p r).app (op U) z) = 0 := by
        change tensorExtStalkEquiv x p (r - p) S.X₁ S.X₃ (sectionGerm _ x U hU _) = 0
        erw [hs]
        exact map_zero _
      erw [tensorExtGerm_lTensor] at h3
      rw [← alpha_mem_filt_succ_iff_stalk hS x h₁ h₃ hp] at h3
      have h4 : extGerm r S.X₂ x U hU ((alphaPre S.f hp).app (op U) z) ∈
          ExteriorPowerFiltration.filt (Ringed.stalkLinearMap S.f.val x) r (p + 1) := by
        erw [extGerm_alpha x S.f hp]
        exact h3
      exact sectionGerm_apex_mk_eq_zero S.f S.g hp hU z h4 hs
  · obtain ⟨s, hs⟩ := exists_stalk_section hS x h₃
    obtain ⟨u, hu⟩ := ExteriorPowerFiltration.lTensor_map_surjective hs _ (r - p)
      (tensorExtGerm x p (r - p) S.X₁ S.X₃ U hU t)
    obtain ⟨u', rfl⟩ := (tensorExtStalkEquiv x p (r - p) S.X₁ S.X₂).surjective u
    obtain ⟨V, hV, v, rfl⟩ := exists_sectionGerm _ x u'
    refine ⟨V, hV, Submodule.Quotient.mk v, ?_⟩
    apply (tensorExtStalkEquiv x p (r - p) S.X₁ S.X₃).injective
    change tensorExtGerm x p (r - p) S.X₁ S.X₃ V hV ((betaPre S.g p r).app (op V) v) =
      tensorExtGerm x p (r - p) S.X₁ S.X₃ U hU t
    erw [tensorExtGerm_lTensor]
    exact hu

end StalkBijective

section LocallyFreeMain

open SheafAlgebraOperations

variable {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))} (hS : S.ShortExact)
  (h₁ : Ringed.IsLocallyFree S.X₁) (h₃ : Ringed.IsLocallyFree S.X₃)

/-- The graded pieces of the standard filtration, for a short exact sequence whose outer terms
are locally free of arbitrary rank. -/
noncomputable def gradedIsoOfIsLocallyFree {r p : ℕ} (hp : p ≤ r)
    (h : filSh S.f r (p + 1) ≤ filSh S.f r p) :
    cokernel (Subobject.ofLE _ _ h) ≅
      moduleSheafTensor (moduleSheafExteriorPower p S.X₁) (moduleSheafExteriorPower (r - p) S.X₃) :=
  haveI : IsIso (sheafifyMap (toGrad S.f S.g hp)) :=
    isIso_sheafifyMap _ fun x => stalk_toGrad_bijective hS x h₁ h₃ hp
  haveI : IsIso (sheafifyMap (toH S.f S.g hp)) :=
    isIso_sheafifyMap _ fun x => stalk_toH_bijective hS x h₁ h₃ hp
  cokernelIsoOfEq (ofLE_filSh_eq S.f r p h) ≪≫
    cokernelCompIsIso ((Subobject.underlyingIso (filArrow S.f r (p + 1))).hom ≫
      sheafifyMap (PresheafOfModules.Submodule.homOfLE (filPre_antitone S.f r (Nat.le_succ p))))
      (Subobject.underlyingIso (filArrow S.f r p)).inv ≪≫
    cokernelEpiComp (Subobject.underlyingIso (filArrow S.f r (p + 1))).hom
      (sheafifyMap (PresheafOfModules.Submodule.homOfLE (filPre_antitone S.f r (Nat.le_succ p)))) ≪≫
    cokernelIsoSheafifyGrad S.f r p ≪≫ (asIso (sheafifyMap (toGrad S.f S.g hp))).symm ≪≫
      asIso (sheafifyMap (toH S.f S.g hp)) ≪≫ sheafifyTensorIso S.X₁ S.X₃ p (r - p)

end LocallyFreeMain

section Determinant

open SheafAlgebraOperations

variable {F' F F'' : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F)

lemma filSh_eq_top_of_locally {r p : ℕ}
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ V : Opens X, V ≤ U → (filPre f r p).obj (op V) = ⊤) : filSh f r p = ⊤ := by
  have : IsIso (sheafifyMap (filPre f r p).ι) :=
    isIso_sheafifyMap_of_locally_bijective _ fun x => by
      obtain ⟨U, hxU, hU⟩ := h x
      refine ⟨U, hxU, fun V hV => ⟨fun a b hab => Subtype.ext hab, fun w => ?_⟩⟩
      have hw : w ∈ (filPre f r p).obj (op V) := by
        rw [hU V hV]
        trivial
      exact ⟨⟨w, hw⟩, rfl⟩
  have : IsIso (filArrow f r p) := by
    unfold filArrow
    infer_instance
  exact Subobject.mk_eq_top_of_isIso _

lemma filSh_eq_bot_of_locally {r p : ℕ}
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ V : Opens X, V ≤ U → (filPre f r p).obj (op V) = ⊥) : filSh f r p = ⊥ := by
  let j := PresheafOfModules.Submodule.homOfLE
    (bot_le : (⊥ : (moduleSheafExteriorPowerPresheaf r F).Submodule) ≤ filPre f r p)
  have : IsIso (sheafifyMap j) :=
    isIso_sheafifyMap_of_locally_bijective _ fun x => by
      obtain ⟨U, hxU, hU⟩ := h x
      refine ⟨U, hxU, fun V hV => ⟨fun a b _ => ?_, fun w => ?_⟩⟩
      · have ha : a.1 = 0 := (Submodule.mem_bot _).1 a.2
        have hb : b.1 = 0 := (Submodule.mem_bot _).1 b.2
        exact Subtype.ext (ha.trans hb.symm)
      · have key : ∀ (N : Submodule ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V))
            ((moduleSheafExteriorPowerPresheaf r F).obj (op V))) (y), y ∈ N → N = ⊥ → y = 0 := by
          rintro N y hy rfl
          exact (Submodule.mem_bot _).1 hy
        have hw : w.1 = 0 := key _ _ w.2 (hU V hV)
        refine ⟨0, Subtype.ext ?_⟩
        exact (congrArg Subtype.val (map_zero (j.app (op V)).hom)).trans hw.symm
  have hι : (⊥ : (moduleSheafExteriorPowerPresheaf r F).Submodule).ι = 0 := by
    ext U ⟨w, hw⟩
    exact (Submodule.mem_bot _).1 hw
  have hcomp : sheafifyMap j ≫ filArrow f r p = 0 := by
    rw [filArrow, ← Category.assoc, ← Functor.map_comp, PresheafOfModules.Submodule.homOfLE_ι, hι]
    change (PresheafOfModules.sheafification _).map 0 ≫ _ = 0
    rw [Functor.map_zero, zero_comp]
  rw [filSh, Subobject.mk_eq_bot_iff_zero, ← cancel_epi (sheafifyMap j), hcomp, comp_zero]

/-- The cokernel of the inclusion of the zero subobject into `B` is `B`. -/
noncomputable def cokernelOfLEBotIso {Y : SheafOfModules.{u} (ringCatSheafOf R)}
    {A B : Subobject Y} (hA : A = ⊥) (h : A ≤ B) :
    cokernel (Subobject.ofLE A B h) ≅ (B : SheafOfModules.{u} (ringCatSheafOf R)) :=
  have h0 : Subobject.ofLE A B h = 0 := by
    subst hA
    exact (IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero).eq_of_src _ _
  cokernelIsoOfEq h0 ≪≫ cokernelZeroIsoTarget

open Ringed in
/-- A locally free module of rank `n` has, near every point, sections over all small opens
that are free with a basis indexed by `n` elements. -/
lemma exists_basis_of_isLocallyFreeOfRank {E : SheafOfModules.{u} (ringCatSheafOf R)} {n : ℕ}
    (hE : Ringed.IsLocallyFreeOfRank E n) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ V : Opens X, V ≤ U →
      Nonempty (Module.Basis (ULift.{u} (Fin n))
        ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (E.val.obj (op V))) := by
  classical
  obtain ⟨U, hxU, ⟨α⟩⟩ := hE x
  refine ⟨U, hxU, fun V hV => ?_⟩
  have hfr := Ringed.isLocalFrame_of_over_iso α
  let eqv : (ULift.{u} (Fin n) → R.obj.obj (op V)) ≃ₗ[R.obj.obj (op V)]
      E.val.presheaf.obj (op V) :=
    LinearEquiv.ofBijective (Ringed.localFrameMap E _ hV) (hfr V hV)
  have b : Module.Basis (ULift.{u} (Fin n)) (R.obj.obj (op V)) (E.val.presheaf.obj (op V)) :=
    (Pi.basisFun _ _).map eqv
  exact ⟨b⟩

/-- An `𝒪_X`-module is zero if every point has a neighbourhood on which `𝒪_X` vanishes. -/
lemma isZero_of_locally_subsingleton
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      Subsingleton ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)))
    (M : SheafOfModules.{u} (ringCatSheafOf R)) : IsZero M := by
  choose U hxU hU using h
  have hsub : ∀ W : Opens X, ∀ s : M.val.obj (op W), s = 0 := by
    intro W s
    let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
    refine TopCat.Sheaf.eq_of_locally_eq' Fsh (fun x : W => W ⊓ U x) W
      (fun _ => homOfLE inf_le_left) (fun y hy => ?_) s 0 (fun x => ?_)
    · exact Opens.mem_iSup.2 ⟨⟨y, hy⟩, hy, hxU y⟩
    · have := hU x
      have hW : Subsingleton ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op (W ⊓ U x))) := by
        let φ := ((R.obj ⋙ forget₂ CommRingCat RingCat).map
          (homOfLE (inf_le_right : W ⊓ U x ≤ U x)).op).hom
        refine subsingleton_of_zero_eq_one ?_
        rw [← map_zero φ, ← map_one φ, Subsingleton.elim (0 : (R.obj ⋙ forget₂ CommRingCat RingCat).obj
          (op (U x))) 1]
      have hM : Subsingleton (M.val.obj (op (W ⊓ U x))) :=
        Module.subsingleton ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op (W ⊓ U x))) _
      exact @Subsingleton.elim _ hM _ _
  refine (IsZero.iff_id_eq_zero M).2 ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext s
  exact (hsub W.unop _).trans (hsub W.unop _).symm

end Determinant

section MainTheorem

/-- **Hartshorne II, Exercise 5.16(d).** Let `0 → F' → F → F'' → 0` be a short exact sequence of
locally free `𝒪_X`-modules (of arbitrary rank) on a ringed space `(X, 𝒪_X)`, and `r ≥ 0`. The
standard filtration `F^p ⊆ ⋀^r F` (`filSh`), with `F^p` the image of the wedge-product morphism
`⋀^p F' ⊗ ⋀^{r-p} F → ⋀^r F` for `p ≤ r`, is a finite filtration
`⋀^r F = F^0 ⊇ F^1 ⊇ ⋯ ⊇ F^r ⊇ F^{r+1} = 0` by subobjects whose quotients are
`F^p / F^{p+1} ≅ ⋀^p F' ⊗ ⋀^{r-p} F''` for `0 ≤ p ≤ r`. -/
theorem exteriorPower_exact_filtration_of_isLocallyFree
    (S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))) (hS : S.ShortExact)
    (h₁ : Ringed.IsLocallyFree S.X₁) (h₃ : Ringed.IsLocallyFree S.X₃) :
    Ringed.IsLocallyFree S.X₂ → ∀ r : ℕ,
      (∀ p (hp : p ≤ r), filSh S.f r p = imageSubobject (wedgeSheafMap S.f hp)) ∧
      filSh S.f r 0 = ⊤ ∧ filSh S.f r (r + 1) = ⊥ ∧ Antitone (filSh S.f r) ∧
      ∀ p (h : filSh S.f r (p + 1) ≤ filSh S.f r p), p ≤ r →
        Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
          moduleSheafTensor (moduleSheafExteriorPower p S.X₁)
            (moduleSheafExteriorPower (r - p) S.X₃)) := fun _ r =>
  ⟨fun _ hp => filSh_eq_imageSubobject S.f hp, filSh_zero S.f r,
    filSh_of_lt S.f (Nat.lt_succ_self r), filSh_antitone S.f r,
    fun _ h hp => ⟨gradedIsoOfIsLocallyFree hS h₁ h₃ hp h⟩⟩

/-- **Hartshorne II, Exercise 5.16(d)**, in the book's wording: for a short exact sequence
`0 → F' → F → F'' → 0` of locally free `𝒪_X`-modules (of arbitrary rank) and every `r`, there is
a finite filtration `⋀^r F = F^0 ⊇ F^1 ⊇ ⋯ ⊇ F^r ⊇ F^{r+1} = 0` with quotients
`F^p / F^{p+1} ≅ ⋀^p F' ⊗ ⋀^{r-p} F''` for each `p`. -/
theorem exists_exteriorPower_exact_filtration_of_isLocallyFree
    (S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))) (hS : S.ShortExact)
    (h₁ : Ringed.IsLocallyFree S.X₁) (h₃ : Ringed.IsLocallyFree S.X₃) :
    Ringed.IsLocallyFree S.X₂ → ∀ r : ℕ,
      ∃ Fil : ℕ → Subobject (C := SheafOfModules.{u} (ringCatSheafOf R))
          (moduleSheafExteriorPower r S.X₂),
        Fil 0 = ⊤ ∧ Fil (r + 1) = ⊥ ∧ Antitone Fil ∧
        ∀ p (h : Fil (p + 1) ≤ Fil p), p ≤ r →
          Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
            moduleSheafTensor (moduleSheafExteriorPower p S.X₁)
              (moduleSheafExteriorPower (r - p) S.X₃)) := fun h₂ r =>
  have h := exteriorPower_exact_filtration_of_isLocallyFree S hS h₁ h₃ h₂ r
  ⟨filSh S.f r, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The finite-rank case of `exteriorPower_exact_filtration_of_isLocallyFree`. -/
@[deprecated exteriorPower_exact_filtration_of_isLocallyFree (since := "2026-11-09")]
theorem exteriorPower_exact_filtration
    (S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))) (hS : S.ShortExact)
    (h₁ : Ringed.IsFiniteLocallyFree S.X₁) (h₃ : Ringed.IsFiniteLocallyFree S.X₃) :
    Ringed.IsFiniteLocallyFree S.X₂ → ∀ r : ℕ,
      (∀ p (hp : p ≤ r), filSh S.f r p = imageSubobject (wedgeSheafMap S.f hp)) ∧
      filSh S.f r 0 = ⊤ ∧ filSh S.f r (r + 1) = ⊥ ∧ Antitone (filSh S.f r) ∧
      ∀ p (h : filSh S.f r (p + 1) ≤ filSh S.f r p), p ≤ r →
        Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
          moduleSheafTensor (moduleSheafExteriorPower p S.X₁)
            (moduleSheafExteriorPower (r - p) S.X₃)) := fun h₂ =>
  exteriorPower_exact_filtration_of_isLocallyFree S hS h₁.isLocallyFree h₃.isLocallyFree
    h₂.isLocallyFree

/-- The finite-rank case of `exists_exteriorPower_exact_filtration_of_isLocallyFree`. -/
@[deprecated exists_exteriorPower_exact_filtration_of_isLocallyFree (since := "2026-11-09")]
theorem exists_exteriorPower_exact_filtration
    (S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))) (hS : S.ShortExact)
    (h₁ : Ringed.IsFiniteLocallyFree S.X₁) (h₃ : Ringed.IsFiniteLocallyFree S.X₃) :
    Ringed.IsFiniteLocallyFree S.X₂ → ∀ r : ℕ,
      ∃ Fil : ℕ → Subobject (C := SheafOfModules.{u} (ringCatSheafOf R))
          (moduleSheafExteriorPower r S.X₂),
        Fil 0 = ⊤ ∧ Fil (r + 1) = ⊥ ∧ Antitone Fil ∧
        ∀ p (h : Fil (p + 1) ≤ Fil p), p ≤ r →
          Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
            moduleSheafTensor (moduleSheafExteriorPower p S.X₁)
              (moduleSheafExteriorPower (r - p) S.X₃)) := fun h₂ =>
  exists_exteriorPower_exact_filtration_of_isLocallyFree S hS h₁.isLocallyFree h₃.isLocallyFree
    h₂.isLocallyFree

/-- Near every point of a short exact sequence of locally free modules of ranks `n'`, `n`, `n''`,
the sequence is split on sections over small opens, and those sections are free with bases of
sizes `n'`, `n`, `n''`. -/
lemma exists_rank_data {S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))}
    (hS : S.ShortExact) {n' n n'' : ℕ} (h₁ : Ringed.IsLocallyFreeOfRank S.X₁ n')
    (h₂ : Ringed.IsLocallyFreeOfRank S.X₂ n) (h₃ : Ringed.IsLocallyFreeOfRank S.X₃ n'') (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ V : Opens X, V ≤ U → IsSplitAt S.f S.g (op V) ∧
      Nonempty (Module.Basis (ULift.{u} (Fin n'))
        ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (S.X₁.val.obj (op V))) ∧
      Nonempty (Module.Basis (ULift.{u} (Fin n))
        ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (S.X₂.val.obj (op V))) ∧
      Nonempty (Module.Basis (ULift.{u} (Fin n''))
        ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) (S.X₃.val.obj (op V))) := by
  obtain ⟨U₀, hx₀, hU₀⟩ := exists_isSplitAt hS h₁.isFiniteLocallyFree h₃.isFiniteLocallyFree x
  obtain ⟨U₁, hx₁, hU₁⟩ := exists_basis_of_isLocallyFreeOfRank h₁ x
  obtain ⟨U₂, hx₂, hU₂⟩ := exists_basis_of_isLocallyFreeOfRank h₂ x
  obtain ⟨U₃, hx₃, hU₃⟩ := exists_basis_of_isLocallyFreeOfRank h₃ x
  refine ⟨U₀ ⊓ U₁ ⊓ U₂ ⊓ U₃, ⟨⟨⟨hx₀, hx₁⟩, hx₂⟩, hx₃⟩, fun V hV => ⟨hU₀ V ?_, hU₁ V ?_,
    hU₂ V ?_, hU₃ V ?_⟩⟩
  · exact hV.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  · exact hV.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  · exact hV.trans (inf_le_left.trans inf_le_right)
  · exact hV.trans inf_le_right

/-- **Hartshorne II, Exercise 5.16(d), top degree.** If `0 → F' → F → F'' → 0` is a short exact
sequence of `𝒪_X`-modules with `F'`, `F`, `F''` locally free of ranks `n'`, `n`, `n''`, then
`⋀^n F ≅ ⋀^{n'} F' ⊗ ⋀^{n''} F''`, that is, `det F ≅ det F' ⊗ det F''`. -/
theorem exteriorPower_exact_det
    (S : ShortComplex (SheafOfModules.{u} (ringCatSheafOf R))) (hS : S.ShortExact)
    {n' n n'' : ℕ} (h₁ : Ringed.IsLocallyFreeOfRank S.X₁ n')
    (h₂ : Ringed.IsLocallyFreeOfRank S.X₂ n) (h₃ : Ringed.IsLocallyFreeOfRank S.X₃ n'') :
    Nonempty (Iso (C := SheafOfModules.{u} (ringCatSheafOf R))
      (moduleSheafExteriorPower n S.X₂)
      (moduleSheafTensor (moduleSheafExteriorPower n' S.X₁)
        (moduleSheafExteriorPower n'' S.X₃))) := by
  have hdata := exists_rank_data hS h₁ h₂ h₃
  by_cases hn : n = n' + n''
  · have hloc : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
        ∀ V : Opens X, V ≤ U → IsSplitAt S.f S.g (op V) := fun x => by
      obtain ⟨U, hx, hU⟩ := hdata x
      exact ⟨U, hx, fun V hV => (hU V hV).1⟩
    have htop : filSh S.f n n' = ⊤ := filSh_eq_top_of_locally S.f fun x => by
      obtain ⟨U, hx, hU⟩ := hdata x
      refine ⟨U, hx, fun V hV => ?_⟩
      obtain ⟨hsplit, -, -, ⟨b₃⟩⟩ := hU V hV
      obtain ⟨s, hs⟩ := hsplit.split
      have := hsplit.free₁
      have := hsplit.finite₁
      have := hsplit.free₃
      have := hsplit.finite₃
      exact ExteriorPowerFiltration.filt_eq_top_of_subsingleton hsplit.injective hsplit.exact hs
        n' (by omega) fun k hk => ExteriorPowerFiltration.exteriorPower_subsingleton_of_basis b₃
          (by simp only [Fintype.card_ulift, Fintype.card_fin]; omega)
    have hbot : filSh S.f n (n' + 1) = ⊥ := filSh_eq_bot_of_locally S.f fun x => by
      obtain ⟨U, hx, hU⟩ := hdata x
      refine ⟨U, hx, fun V hV => ?_⟩
      obtain ⟨-, ⟨b₁⟩, -, -⟩ := hU V hV
      exact ExteriorPowerFiltration.filt_eq_bot_of_subsingleton _
        (ExteriorPowerFiltration.exteriorPower_subsingleton_of_basis b₁
          (by simp only [Fintype.card_ulift, Fintype.card_fin]; omega))
    have hle : filSh S.f n (n' + 1) ≤ filSh S.f n n' := filSh_antitone S.f n (Nat.le_succ n')
    have hp : n' ≤ n := by omega
    exact ⟨(Subobject.isoOfEqMk _ (𝟙 _) (htop.trans (Subobject.mk_eq_top_of_isIso _).symm)).symm ≪≫
      (cokernelOfLEBotIso hbot hle).symm ≪≫ gradedIso S.f S.g hloc hp hle ≪≫
      eqToIso (by rw [show n - n' = n'' by omega])⟩
  · have hzero : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
        Subsingleton ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) := fun x => by
      obtain ⟨U, hx, hU⟩ := hdata x
      refine ⟨U, hx, ?_⟩
      obtain ⟨hsplit, ⟨b₁⟩, ⟨b₂⟩, ⟨b₃⟩⟩ := hU U le_rfl
      rcases subsingleton_or_nontrivial ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
        with h | h
      · exact h
      · exfalso
        apply hn
        obtain ⟨s, hs⟩ := hsplit.split
        have := hsplit.free₁
        have := hsplit.finite₁
        have := hsplit.free₃
        have := hsplit.finite₃
        have e := (ExteriorPowerFiltration.splitEquiv hsplit.exact hs hsplit.injective).finrank_eq
        rw [Module.finrank_prod, Module.finrank_eq_card_basis b₁, Module.finrank_eq_card_basis b₂,
          Module.finrank_eq_card_basis b₃] at e
        simp only [Fintype.card_ulift, Fintype.card_fin] at e
        omega
    exact ⟨(isZero_of_locally_subsingleton hzero _).iso (isZero_of_locally_subsingleton hzero _)⟩

end MainTheorem

end ExteriorPowerExactFiltration

end Hartshorne
