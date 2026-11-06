/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Hartshorne.Scheme.Differentials.AffineRelativeDifferentials
import Hartshorne.Scheme.FiniteType

/-!
# Quasi-coherence and coherence of differentials

Hartshorne, *Algebraic Geometry*, II.8, Remark 8.9.1 (p. 175).

For every morphism of schemes `f : X ⟶ Y` the relative differential sheaf `Ω_{X/Y}` is
quasi-coherent, and it is coherent when `Y` is Noetherian and `f` is of finite type.

The key point is that `Ω_{X/Y}` is local: if `j : U ⟶ X` and `i : V ⟶ Y` are open immersions
with `j ≫ f = g ≫ i`, then `Ω_{X/Y}|_U ≅ Ω_{U/V}`.  This is proved by showing that the
restriction corepresents derivations on `U` relative to `g`, combining

* the adjunction between restriction and pushforward along `j`;
* the universal property of `Ω_{X/Y}`;
* an identification of derivations on `U` relative to `j ≫ f` with derivations on `X` relative
  to `f` valued in the pushforward, and of derivations relative to `j ≫ f = g ≫ i` with
  derivations relative to `g`.

Both identifications rest on a criterion for the vanishing condition of a relative derivation:
a Leibniz family `d` vanishes on the image of `f⁻¹ 𝒪_Y → 𝒪_X` as soon as it kills every section
`f^♯ t` with `t ∈ Γ(Y, V)`, because the sections killed by `d` form a subsheaf of rings through
which the structure map of `f` factors.

On an affine open `U = Spec B` mapping into an affine open `V = Spec A`, this gives
`Ω_{X/Y}|_U ≅ Ω_{Spec B/Spec A} ≅ (Ω_{B/A})~`, and such opens cover `X`.  For a morphism locally
of finite type, `Ω_{B/A}` is a finitely generated `B`-module.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.RelDiffLocal

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)}
  (d : ∀ {U : X.Opensᵒᵖ}, X.presheaf.obj U →+ M.obj U)
  (d_mul : ∀ {U : X.Opensᵒᵖ} (a b : X.presheaf.obj U), d (a * b) = a • d b + b • d a)
  (d_map : ∀ {U V : X.Opensᵒᵖ} (i : U ⟶ V) (x : X.presheaf.obj U),
    d (X.presheaf.map i x) = M.map i (d x))

include d_mul in
theorem d_one' (U : X.Opensᵒᵖ) : d (U := U) 1 = 0 := by
  have h := d_mul (U := U) 1 1
  simp only [mul_one, one_smul] at h
  simpa using h

/-- Sections killed by `d`. -/
def kerSubring (U : X.Opens) : Subring (X.presheaf.obj (op U)) where
  carrier := {s | d (U := op U) s = 0}
  mul_mem' {a b} ha hb := by
    change d (a * b) = 0
    rw [d_mul, show d a = 0 from ha, show d b = 0 from hb, smul_zero, smul_zero, add_zero]
  one_mem' := d_one' d d_mul _
  add_mem' {a b} ha hb := by
    change d (a + b) = 0
    rw [map_add, show d a = 0 from ha, show d b = 0 from hb, add_zero]
  zero_mem' := map_zero (d (U := op U))
  neg_mem' {a} ha := by
    change d (-a) = 0
    rw [map_neg, show d a = 0 from ha, neg_zero]

/-- The presheaf of sections killed by `d`. -/
noncomputable def kerPresheaf : TopCat.Presheaf CommRingCat X where
  obj U := CommRingCat.of (kerSubring d d_mul U.unop)
  map {_ _} i := CommRingCat.ofHom ((X.presheaf.map i).hom.restrict _ _
    (fun s hs => by
      change d (X.presheaf.map i s) = 0
      rw [d_map, show d s = 0 from hs, map_zero]; rfl))
  map_id U := by
    ext x
    change X.presheaf.map (𝟙 U) x.1 = x.1
    simp
  map_comp i j := by
    ext x
    change X.presheaf.map (i ≫ j) x.1 = X.presheaf.map j (X.presheaf.map i x.1)
    simp

variable (hsep : ∀ {ι : Type u} (U : ι → X.Opens) (m : M.obj (op (iSup U))),
    (∀ i, M.map (Opens.leSupr U i).op m = 0) → m = 0)

include hsep in
theorem kerPresheaf_isSheaf : (kerPresheaf d d_mul d_map).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hsf' : TopCat.Presheaf.IsCompatible X.presheaf U (fun i => (sf i).1) :=
    fun i j => congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hsu⟩ := X.sheaf.existsUnique_gluing U _ hsf'
  have hmem : s ∈ kerSubring d d_mul (iSup U) := by
    change d s = 0
    refine hsep U _ fun i => ?_
    exact (d_map (Opens.leSupr U i).op s).symm.trans ((congrArg d (hs i)).trans (sf i).2)
  exact ⟨⟨s, hmem⟩, fun i => Subtype.ext (hs i),
    fun t ht => Subtype.ext (hsu t.1 fun i => congrArg Subtype.val (ht i))⟩

/-- The sheaf of sections killed by `d`. -/
noncomputable def kerSheaf : TopCat.Sheaf CommRingCat X :=
  ⟨kerPresheaf d d_mul d_map, kerPresheaf_isSheaf d d_mul d_map hsep⟩

/-- Its inclusion into the structure sheaf. -/
noncomputable def kerSheafι : kerSheaf d d_mul d_map hsep ⟶ X.sheaf :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (R := kerSubring d d_mul U.unop)
        (S := X.presheaf.obj U) (kerSubring d d_mul U.unop).subtype
      naturality _ _ _ := rfl }

variable (hk : ∀ (V : Y.Opens) (t : Γ(Y, V)), d (U := op (f ⁻¹ᵁ V)) (f.app V t) = 0)

/-- The structure map of `f` factors through the subsheaf killed by `d`. -/
noncomputable def cFactor : Y.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat f.base).obj (kerSheaf d d_mul d_map hsep) :=
  ObjectProperty.homMk
    { app V := CommRingCat.ofHom (R := Y.presheaf.obj V)
        (S := kerSubring d d_mul ((Opens.map f.base).obj V.unop))
        ((f.c.app V).hom.codRestrict _ (fun t => hk V.unop t))
      naturality _ _ _ := by
        ext
        exact Subtype.ext (ConcreteCategory.congr_hom (f.c.naturality _) _) }

include hk in
theorem inverseImageStructureSheafMap_eq :
    Scheme.inverseImageStructureSheafMap f =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv _ _).symm
        (cFactor f d d_mul d_map hsep hk) ≫ kerSheafι d d_mul d_map hsep := by
  rw [Scheme.inverseImageStructureSheafMap, ← Adjunction.homEquiv_naturality_right_symm]
  rfl

include d_mul d_map hsep hk in
/-- A family of Leibniz maps killing the sections `f^♯ t` kills the whole image of
`f⁻¹ 𝒪_Y → 𝒪_X`. -/
theorem d_app_of_kills (U : X.Opensᵒᵖ) (a : (Scheme.inverseImageStructureSheaf f).obj.obj U) :
    d ((Scheme.inverseImageStructureSheafMap f).hom.app U a) = 0 := by
  have h := congrArg (fun φ => φ.hom.app U a)
    (inverseImageStructureSheafMap_eq f d d_mul d_map hsep hk)
  simp only at h
  rw [h]
  exact ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv _ _).symm
    (cFactor f d d_mul d_map hsep hk)).hom.app U a).property

end AlgebraicGeometry.RelDiffLocal

namespace AlgebraicGeometry.RelDiffLocal

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem modules_sep (N : X.Modules) {ι : Type u} (U : ι → X.Opens) (m : N.val.obj (op (iSup U)))
    (h : ∀ i, N.val.map (Opens.leSupr U i).op m = 0) : m = 0 :=
  TopCat.Sheaf.eq_of_locally_eq (F := ⟨N.presheaf, N.isSheaf⟩) U m 0
    (fun i => (h i).trans (map_zero _).symm)

/-- A relative derivation kills the sections `f^♯ t`. -/
theorem kills_of_derivation {N : X.Modules}
    (D : N.val.Derivation' (Scheme.inverseImageStructureSheafMap f).hom)
    (V : Y.Opens) (t : Γ(Y, V)) : D.d (X := op (f ⁻¹ᵁ V)) (f.app V t) = 0 := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base
  have h₁ : adj.homEquiv _ _ (Scheme.inverseImageStructureSheafMap f) =
      ObjectProperty.homMk f.c :=
    (adj.homEquiv _ _).apply_symm_apply _
  have h₂ := congrArg (fun φ => φ.hom.app (op V) t) ((adj.homEquiv_unit _ _ _).symm.trans h₁)
  simp only at h₂
  exact (congrArg D.d h₂.symm).trans (D.d_app _)

/-- Build a relative derivation from a Leibniz family killing the sections `f^♯ t`. -/
noncomputable def derivationOfKills
    {M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)}
    (d : ∀ {U : X.Opensᵒᵖ}, X.presheaf.obj U →+ M.obj U)
    (d_mul : ∀ {U : X.Opensᵒᵖ} (a b : X.presheaf.obj U), d (a * b) = a • d b + b • d a)
    (d_map : ∀ {U V : X.Opensᵒᵖ} (i : U ⟶ V) (x : X.presheaf.obj U),
      d (X.presheaf.map i x) = M.map i (d x))
    (hsep : ∀ {ι : Type u} (U : ι → X.Opens) (m : M.obj (op (iSup U))),
      (∀ i, M.map (Opens.leSupr U i).op m = 0) → m = 0)
    (hk : ∀ (V : Y.Opens) (t : Γ(Y, V)), d (U := op (f ⁻¹ᵁ V)) (f.app V t) = 0) :
    M.Derivation' (Scheme.inverseImageStructureSheafMap f).hom where
  d := d
  d_mul := d_mul
  d_map := d_map
  d_app {U} a := d_app_of_kills f d d_mul d_map hsep hk U a


end AlgebraicGeometry.RelDiffLocal

namespace AlgebraicGeometry.RelDiffLocal

variable {X Y Z : Scheme.{u}}

/-- `d` kills the sections `h^♯ t`. -/
def Kills (h : X ⟶ Z) {M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)}
    (d : ∀ {U : X.Opensᵒᵖ}, X.presheaf.obj U →+ M.obj U) : Prop :=
  ∀ (V : Z.Opens) (t : Γ(Z, V)), d (U := op (h ⁻¹ᵁ V)) (h.app V t) = 0

theorem kills_comp_iff (g : X ⟶ Y) (i : Y ⟶ Z) [IsOpenImmersion i]
    {M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)}
    (d : ∀ {U : X.Opensᵒᵖ}, X.presheaf.obj U →+ M.obj U)
    (d_map : ∀ {U V : X.Opensᵒᵖ} (i : U ⟶ V) (x : X.presheaf.obj U),
      d (X.presheaf.map i x) = M.map i (d x)) :
    Kills (g ≫ i) d ↔ Kills g d := by
  refine ⟨fun h W t => ?_, fun h W t => h (i ⁻¹ᵁ W) (i.app W t)⟩
  have hW : i ⁻¹ᵁ i ''ᵁ W = W := i.preimage_image_eq W
  have e : t = Y.presheaf.map (eqToHom hW.symm).op (i.app _ ((i.appIso W).inv t)) := by
    rw [Scheme.Hom.appIso_inv_app_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    simp
  have key := h (i ''ᵁ W) ((i.appIso W).inv t)
  rw [e, ← ConcreteCategory.comp_apply, g.naturality, ConcreteCategory.comp_apply, d_map]
  exact (congrArg _ key).trans (map_zero _)

end AlgebraicGeometry.RelDiffLocal

namespace AlgebraicGeometry.RelDiffLocal

variable {X Y Z : Scheme.{u}}

/-- Relative derivations for two morphisms with the same killing condition coincide. -/
noncomputable def derivationEquivOfKills (h : X ⟶ Y) (h' : X ⟶ Z)
    (H : ∀ {M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)}
      (d : ∀ {U : X.Opensᵒᵖ}, X.presheaf.obj U →+ M.obj U),
      (∀ {U V : X.Opensᵒᵖ} (i : U ⟶ V) (x : X.presheaf.obj U),
        d (X.presheaf.map i x) = M.map i (d x)) → (Kills h d ↔ Kills h' d))
    (N : X.Modules) :
    N.val.Derivation' (Scheme.inverseImageStructureSheafMap h).hom ≃
      N.val.Derivation' (Scheme.inverseImageStructureSheafMap h').hom where
  toFun D := derivationOfKills (M := N.val) h' D.d D.d_mul D.d_map (modules_sep N)
    ((H (M := N.val) D.d D.d_map).1 (kills_of_derivation h D))
  invFun D := derivationOfKills (M := N.val) h D.d D.d_mul D.d_map (modules_sep N)
    ((H (M := N.val) D.d D.d_map).2 (kills_of_derivation h' D))
  left_inv _ := rfl
  right_inv _ := rfl

variable (f : X ⟶ Y) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Push a derivation on `U` relative to `j ≫ f` forward to `X`. -/
noncomputable def pushDerivation (N : U.Modules)
    (D : N.val.Derivation' (Scheme.inverseImageStructureSheafMap (j ≫ f)).hom) :
    ((Scheme.Modules.pushforward j).obj N).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom :=
  derivationOfKills (M := ((Scheme.Modules.pushforward j).obj N).val) f
    (fun {W} => D.d.comp (j.app W.unop).hom.toAddMonoidHom)
    (fun {W} a b => (congrArg D.d (map_mul (j.app W.unop).hom a b)).trans (D.d_mul _ _))
    (fun {_ _} i x => (congrArg D.d (ConcreteCategory.congr_hom (j.naturality i) x)).trans
      (D.d_map _ _))
    (modules_sep _)
    (fun V t => kills_of_derivation (j ≫ f) D V t)

theorem appIso_inv_app_map (W : U.Opens) (a : Γ(U, W)) :
    U.presheaf.map (eqToHom (j.preimage_image_eq W).symm).op
      (j.app (j ''ᵁ W) ((j.appIso W).inv a)) = a := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    j.appIso_inv_app_presheafMap]
  rfl

omit [IsOpenImmersion j] in
theorem presheaf_map_map (N : U.Modules) {A B B' C : U.Opensᵒᵖ} (p : A ⟶ B) (q : B ⟶ C)
    (p' : A ⟶ B') (q' : B' ⟶ C) (x : N.presheaf.obj A) :
    N.presheaf.map q (N.presheaf.map p x) = N.presheaf.map q' (N.presheaf.map p' x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

variable {f j} in
/-- The restricted derivation on sections. -/
noncomputable def resD {N : U.Modules}
    (D : ((Scheme.Modules.pushforward j).obj N).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom) (W : U.Opens) (s : Γ(U, W)) : Γ(N, W) :=
  N.presheaf.map (eqToHom (j.preimage_image_eq W).symm).op
    (D.d (X := op (j ''ᵁ W)) ((j.appIso W).inv s))

variable {j} in
theorem map_leibniz_aux (N : U.Modules) (W : U.Opens) (a b : Γ(U, W))
    (x y z : Γ(N, j ⁻¹ᵁ j ''ᵁ W))
    (h : x = j.app _ ((j.appIso W).inv a) • y + j.app _ ((j.appIso W).inv b) • z) :
    N.presheaf.map (eqToHom (j.preimage_image_eq W).symm).op x =
      a • N.presheaf.map (eqToHom (j.preimage_image_eq W).symm).op y +
        b • N.presheaf.map (eqToHom (j.preimage_image_eq W).symm).op z := by
  rw [h, map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul, appIso_inv_app_map,
    appIso_inv_app_map]

variable {f j} in
theorem resD_mul {N : U.Modules}
    (D : ((Scheme.Modules.pushforward j).obj N).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom) (W : U.Opens) (a b : Γ(U, W)) :
    resD D W (a * b) = a • resD D W b + b • resD D W a :=
  map_leibniz_aux N W a b _ _ _ ((congrArg D.d (map_mul _ a b)).trans (D.d_mul _ _))

variable {f j} in
theorem resD_map {N : U.Modules}
    (D : ((Scheme.Modules.pushforward j).obj N).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom) {W W' : U.Opens} (i : W' ⟶ W) (s : Γ(U, W)) :
    resD D W' (U.presheaf.map i.op s) = N.presheaf.map i.op (resD D W s) := by
  unfold resD
  have e1 : (j.appIso W').inv (U.presheaf.map i.op s) =
      X.presheaf.map (j.opensFunctor.op.map i.op) ((j.appIso W).inv s) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, j.appIso_inv_naturality]
  have e2 : (show Γ(N, j ⁻¹ᵁ j ''ᵁ W') from
      D.d (X := op (j ''ᵁ W')) (X.presheaf.map (j.opensFunctor.op.map i.op) ((j.appIso W).inv s))) =
      N.presheaf.map ((Opens.map j.base).map (j.opensFunctor.map i)).op
        (show Γ(N, j ⁻¹ᵁ j ''ᵁ W) from D.d (X := op (j ''ᵁ W)) ((j.appIso W).inv s)) :=
    D.d_map _ _
  rw [e1]
  exact (congrArg (N.presheaf.map _) e2).trans (presheaf_map_map N _ _ _ _ _)

variable {f j} in
/-- `resD` as an additive map. -/
noncomputable def resDHom {N : U.Modules}
    (D : ((Scheme.Modules.pushforward j).obj N).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom) (W : U.Opens) : Γ(U, W) →+ Γ(N, W) :=
  AddMonoidHom.mk' (resD D W) (fun a b =>
    (congrArg (N.presheaf.map _) ((congrArg D.d (map_add _ a b)).trans (map_add D.d _ _))).trans
      (map_add _ _ _))

variable {f j} in
theorem resD_kills {N : U.Modules}
    (D : ((Scheme.Modules.pushforward j).obj N).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom) (V : Y.Opens) (t : Γ(Y, V)) :
    resD D ((j ≫ f) ⁻¹ᵁ V) ((j ≫ f).app V t) = 0 := by
  unfold resD
  have e1 : (j.appIso (j ⁻¹ᵁ f ⁻¹ᵁ V)).inv (j.app (f ⁻¹ᵁ V) (f.app V t)) =
      X.presheaf.map (homOfLE (j.image_preimage_le (f ⁻¹ᵁ V))).op (f.app V t) := by
    rw [← ConcreteCategory.comp_apply, j.app_appIso_inv]
    rfl
  have e2 : (show Γ(N, j ⁻¹ᵁ j ''ᵁ j ⁻¹ᵁ f ⁻¹ᵁ V) from D.d (X := op (j ''ᵁ j ⁻¹ᵁ f ⁻¹ᵁ V))
      (X.presheaf.map (homOfLE (j.image_preimage_le (f ⁻¹ᵁ V))).op (f.app V t))) =
      N.presheaf.map ((Opens.map j.base).map (homOfLE (j.image_preimage_le (f ⁻¹ᵁ V)))).op
        (show Γ(N, j ⁻¹ᵁ f ⁻¹ᵁ V) from D.d (X := op (f ⁻¹ᵁ V)) (f.app V t)) :=
    D.d_map _ _
  have e3 : (show Γ(N, j ⁻¹ᵁ f ⁻¹ᵁ V) from D.d (X := op (f ⁻¹ᵁ V)) (f.app V t)) = 0 :=
    kills_of_derivation f D V t
  change N.presheaf.map _ (D.d (X := op (j ''ᵁ j ⁻¹ᵁ f ⁻¹ᵁ V))
    ((j.appIso (j ⁻¹ᵁ f ⁻¹ᵁ V)).inv (j.app (f ⁻¹ᵁ V) (f.app V t)))) = 0
  rw [e1]
  exact (congrArg (N.presheaf.map _) (e2.trans ((congrArg _ e3).trans (map_zero _)))).trans
    (map_zero _)

/-- Restrict a derivation relative to `f` with values in `j_* N` to a derivation on `U`
relative to `j ≫ f`. -/
noncomputable def resDerivation (N : U.Modules)
    (D : ((Scheme.Modules.pushforward j).obj N).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom) :
    N.val.Derivation' (Scheme.inverseImageStructureSheafMap (j ≫ f)).hom :=
  derivationOfKills (M := N.val) (j ≫ f) (fun {W} => resDHom D W.unop)
    (fun {W} a b => resD_mul D W.unop a b) (fun {_ _} i x => resD_map D i.unop x)
    (modules_sep N) (fun V t => resD_kills D V t)

/-- Derivations on `U` relative to `j ≫ f` are derivations on `X` relative to `f` with values
in the pushforward. -/
noncomputable def pushEquiv (N : U.Modules) :
    N.val.Derivation' (Scheme.inverseImageStructureSheafMap (j ≫ f)).hom ≃
      ((Scheme.Modules.pushforward j).obj N).val.Derivation'
        (Scheme.inverseImageStructureSheafMap f).hom where
  toFun := pushDerivation f j N
  invFun := resDerivation f j N
  left_inv D := by
    ext W s
    have h := appIso_inv_app_map j W.unop s
    exact (D.d_map (eqToHom (j.preimage_image_eq W.unop).symm).op
      (j.app _ ((j.appIso W.unop).inv s))).symm.trans (congrArg D.d h)
  right_inv D := by
    ext W s
    change resD D (j ⁻¹ᵁ W.unop) (j.app W.unop s) = D.d s
    unfold resD
    have e1 : ∀ s' : Γ(X, W.unop), (j.appIso (j ⁻¹ᵁ W.unop)).inv (j.app W.unop s') =
        X.presheaf.map (homOfLE (j.image_preimage_le W.unop)).op s' := by
      intro s'
      rw [← ConcreteCategory.comp_apply, j.app_appIso_inv]
      rfl
    have e2 : (show Γ(N, j ⁻¹ᵁ j ''ᵁ j ⁻¹ᵁ W.unop) from D.d (X := op (j ''ᵁ j ⁻¹ᵁ W.unop))
        (X.presheaf.map (homOfLE (j.image_preimage_le W.unop)).op s)) =
        N.presheaf.map ((Opens.map j.base).map (homOfLE (j.image_preimage_le W.unop))).op
          (show Γ(N, j ⁻¹ᵁ W.unop) from D.d (X := W) s) :=
      D.d_map _ _
    rw [e1 s]
    refine (congrArg (N.presheaf.map _) e2).trans ?_
    refine (presheaf_map_map N _ _ (𝟙 _) (𝟙 _) _).trans ?_
    rw [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, ConcreteCategory.id_apply]

end AlgebraicGeometry.RelDiffLocal

namespace AlgebraicGeometry.RelDiffLocal

variable {X Y U V : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ X) [IsOpenImmersion j] (g : U ⟶ V)
  (i : V ⟶ Y) [IsOpenImmersion i] (w : j ≫ f = g ≫ i)

variable {f j} in
theorem resD_postcomp {N N' : U.Modules} (τ : N ⟶ N')
    (D : ((Scheme.Modules.pushforward j).obj N).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom) (W : U.Opens) (s : Γ(U, W)) :
    resD (D.postcomp ((Scheme.Modules.pushforward j).map τ).val) W s = τ.app W (resD D W s) := by
  unfold resD
  exact (PresheafOfModules.naturality_apply τ.val (eqToHom (j.preimage_image_eq W).symm).op
    (D.d (X := op (j ''ᵁ W)) ((j.appIso W).inv s))).symm

omit [IsOpenImmersion j] in
include w in
theorem kills_iff_of_comm
    {M : PresheafOfModules.{u} (U.presheaf ⋙ forget₂ CommRingCat RingCat)}
    (d : ∀ {W : U.Opensᵒᵖ}, U.presheaf.obj W →+ M.obj W)
    (d_map : ∀ {W W' : U.Opensᵒᵖ} (i : W ⟶ W') (x : U.presheaf.obj W),
      d (U.presheaf.map i x) = M.map i (d x)) :
    Kills (j ≫ f) d ↔ Kills g d := by
  rw [w]
  exact kills_comp_iff g i d d_map

/-- The restriction of `Ω_{X/Y}` to `U` corepresents derivations on `U` relative to `g`. -/
noncomputable def restrictCorepresentable :
    (Scheme.relativeDerivationsFunctor g).CorepresentableBy
      ((Scheme.relativeDifferentials f).restrict j) where
  homEquiv {N} := ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).trans
    ((Scheme.relativeDifferentialsHomEquiv f _).trans ((pushEquiv f j N).symm.trans
      (derivationEquivOfKills (j ≫ f) g (fun d hd => kills_iff_of_comm f j g i w d hd) N)))
  homEquiv_comp {N N'} τ α := by
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right, Scheme.relativeDifferentialsHomEquiv_naturality]
    apply PresheafOfModules.Derivation.ext
    ext W s
    exact resD_postcomp τ _ W.unop s

end AlgebraicGeometry.RelDiffLocal

namespace AlgebraicGeometry.RelDiffLocal

variable {X Y U V : Scheme.{u}}

/-- `Ω_{X/Y}` restricted along an open immersion `U → X` lying over an open immersion
`V → Y` is `Ω_{U/V}`. -/
noncomputable def restrictIso (f : X ⟶ Y) (j : U ⟶ X) [IsOpenImmersion j] (g : U ⟶ V)
    (i : V ⟶ Y) [IsOpenImmersion i] (w : j ≫ f = g ≫ i) :
    Scheme.relativeDifferentials g ≅ (Scheme.relativeDifferentials f).restrict j :=
  (Scheme.relativeDifferentialsCorepresentable g).uniqueUpToIso
    (restrictCorepresentable f j g i w)

/-- On an affine open `U` mapping into an affine open `V`, `Ω_{X/Y}|_U ≅ (Ω_{B/A})~` where
`A = Γ(Y, V)` and `B = Γ(X, U)`. -/
noncomputable def affineIso (f : X ⟶ Y) (U : X.affineOpens) (V : Y.affineOpens)
    (h : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens)) :
    letI := (f.appLE V U h).hom.toAlgebra
    Hartshorne.specRestriction (Scheme.relativeDifferentials f) U ≅
      (tilde.functor Γ(X, (U : X.Opens))).obj
        (ModuleCat.of Γ(X, (U : X.Opens)) Ω[Γ(X, (U : X.Opens))⁄Γ(Y, (V : Y.Opens))]) :=
  letI := (f.appLE V U h).hom.toAlgebra
  haveI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  (restrictIso f U.2.fromSpec
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, (V : Y.Opens)) Γ(X, (U : X.Opens)))))
    V.2.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 h).symm).symm ≪≫
    Scheme.relativeDifferentialsSpecIso Γ(Y, (V : Y.Opens)) Γ(X, (U : X.Opens))

theorem iSup_affine_le_preimage (f : X ⟶ Y) :
    (⨆ p : {p : X.affineOpens × Y.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : Y.Opens)},
      (p.1.1 : X.Opens)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) hxV (f ⁻¹ᵁ V).2
  exact Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, hxU⟩

end AlgebraicGeometry.RelDiffLocal

namespace AlgebraicGeometry

open RelDiffLocal

variable {X Y : Scheme.{u}}

/-- Hartshorne II, Remark 8.9.1: for every morphism of schemes `f : X ⟶ Y`, the relative
differential sheaf `Ω_{X/Y}` is quasi-coherent. -/
theorem Scheme.relativeDifferentials_isQuasicoherent (f : X ⟶ Y) :
    (Scheme.relativeDifferentials f).IsQuasicoherent := by
  have key : Hartshorne.HasAffineTildeCover (Scheme.relativeDifferentials f) := by
    refine ⟨{p : X.affineOpens × Y.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : Y.Opens)},
      fun p => p.1.1, iSup_affine_le_preimage f, fun p => ?_⟩
    let := (f.appLE p.1.2 p.1.1 p.2).hom.toAlgebra
    exact ⟨_, ⟨(affineIso f p.1.1 p.1.2 p.2).symm⟩⟩
  exact ((Hartshorne.quasicoherent_affine_local_tfae (Scheme.relativeDifferentials f)).out 1 0).1
    key

/-- For a morphism locally of finite type, `Ω_{X/Y}` is coherent in Hartshorne's sense: it is
associated to a finitely generated module on every member of an affine open cover. -/
theorem Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType (f : X ⟶ Y)
    [LocallyOfFiniteType f] : Hartshorne.IsCoherent (Scheme.relativeDifferentials f) := by
  refine ⟨{p : X.affineOpens × Y.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : Y.Opens)},
    fun p => p.1.1, iSup_affine_le_preimage f, fun p => ?_⟩
  let := (f.appLE p.1.2 p.1.1 p.2).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, (p.1.2 : Y.Opens)) Γ(X, (p.1.1 : X.Opens)) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance p.1.2 p.1.1 p.2
  exact ⟨ModuleCat.of _ Ω[Γ(X, (p.1.1 : X.Opens))⁄Γ(Y, (p.1.2 : Y.Opens))],
    inferInstanceAs (Module.Finite _ Ω[Γ(X, (p.1.1 : X.Opens))⁄Γ(Y, (p.1.2 : Y.Opens))]),
    ⟨(affineIso f p.1.1 p.1.2 p.2).symm⟩⟩

/-- Hartshorne II, Remark 8.9.1: if `Y` is Noetherian and `f : X ⟶ Y` is of finite type, then
`Ω_{X/Y}` is coherent.  Coherence in Hartshorne's sense already follows from `f` being locally
of finite type; the Noetherian hypothesis is the setting of the source. -/
theorem Scheme.relativeDifferentials_isCoherent (f : X ⟶ Y) [IsNoetherian Y]
    (hf : Hartshorne.FiniteType f) : Hartshorne.IsCoherent (Scheme.relativeDifferentials f) :=
  haveI : LocallyOfFiniteType f := hf.1
  Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f

end AlgebraicGeometry

