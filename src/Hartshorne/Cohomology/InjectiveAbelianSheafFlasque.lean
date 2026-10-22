/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.OpenExtensionByZero
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Injective abelian sheaves are flasque

The source representer is the original extension by zero of the genuine constant
integral sheaf. Its comparison with free Yoneda is a sheafified comparison.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hartshorne

universe u

/-- The genuine constant integral sheaf on the open subspace, not a constant presheaf. -/
noncomputable def openIntegerConstantSheaf {X : TopCat.{u}} (U : Opens X) :
    (TopCat.of U).Sheaf AddCommGrpCat.{u} :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology (TopCat.of U))
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))

/-- The source's `Z_U`: the original extension by zero of the genuine constant integral sheaf. -/
noncomputable def openIntegerExtensionByZero {X : TopCat.{u}} (U : Opens X) :
    X.Sheaf AddCommGrpCat.{u} :=
  openExtensionByZero U (openIntegerConstantSheaf U)

/-- The literal group seed into the old conditional presheaf over `U`, using the
actual constant-presheaf sheafification unit on the open subspace. -/
noncomputable def openIntegerRawSeed {X : TopCat.{u}} (U : Opens X) :
    AddCommGrpCat.of (ULift.{u} ℤ) ⟶
      (openExtensionByZeroPresheaf U (openIntegerConstantSheaf U)).obj (op U) :=
  AddCommGrpCat.ofHom
    (((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of U))
      ((Functor.const (Opens (TopCat.of U))ᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))).app
          (op ((Opens.map U.inclusion').obj U))).hom.codRestrict _
            (fun _ => Or.inl le_rfl))

/-- The canonical raw comparison, determined by the literal integral seed over `U`.
This map is not asserted to be pointwise invertible. -/
noncomputable def openIntegerRawBeta {X : TopCat.{u}} (U : Opens X) :
    CategoryTheory.Presheaf.freeYoneda U (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      openExtensionByZeroPresheaf U (openIntegerConstantSheaf U) :=
  CategoryTheory.Presheaf.freeYonedaHomEquiv.symm (openIntegerRawSeed U)

/-- The comparison of SHEAVES with the actual source representer `Z_U`.
Invertibility is a separate proof obligation. -/
noncomputable def openIntegerBeta {X : TopCat.{u}} (U : Opens X) :
    CategoryTheory.Sheaf.freeYoneda (Opens.grothendieckTopology X) U
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ openIntegerExtensionByZero U :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (openIntegerRawBeta U)

/-- The raw comparison carries the identity-indexed summand to the literal old seed. -/
theorem openIntegerRawBeta_seed {X : TopCat.{u}} (U : Opens X) :
    Sigma.ι (fun (_ : U ⟶ U) => AddCommGrpCat.of (ULift.{u} ℤ)) (𝟙 U) ≫
        (openIntegerRawBeta U).app (op U) = openIntegerRawSeed U := by
  change CategoryTheory.Presheaf.freeYonedaHomEquiv (openIntegerRawBeta U) =
    openIntegerRawSeed U
  exact (CategoryTheory.Presheaf.freeYonedaHomEquiv).apply_symm_apply (openIntegerRawSeed U)

/-- On image opens, the free presheaf has its canonical single integral summand. -/
private noncomputable def openIntegerFreeImageIso {X : TopCat.{u}} (U : Opens X)
    (W : Opens (TopCat.of U)) :
    (CategoryTheory.Presheaf.freeYoneda U (AddCommGrpCat.of (ULift.{u} ℤ))).obj
        (op (U.isOpenEmbedding.functor.obj W)) ≅ AddCommGrpCat.of (ULift.{u} ℤ) := by
  letI : Unique (U.isOpenEmbedding.functor.obj W ⟶ U) :=
    { default := homOfLE (by rintro x ⟨y, _, rfl⟩; exact y.property)
      uniq := fun _ => Subsingleton.elim _ _ }
  exact coproductUniqueIso (fun _ : U.isOpenEmbedding.functor.obj W ⟶ U =>
    AddCommGrpCat.of (ULift.{u} ℤ))

/-- The constant-specific old conditional group on an image open is the genuine
constant SHEAF's group of sections there, including locally varying sections. -/
private noncomputable def openIntegerRawImageIso {X : TopCat.{u}} (U : Opens X)
    (W : Opens (TopCat.of U)) :
    (openExtensionByZeroPresheaf U (openIntegerConstantSheaf U)).obj
        (op (U.isOpenEmbedding.functor.obj W)) ≅
      (openIntegerConstantSheaf U).presheaf.obj (op W) := by
  have hW : U.isOpenEmbedding.functor.obj W ≤ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  let e :
      (openExtensionByZeroPresheaf U (openIntegerConstantSheaf U)).obj
          (op (U.isOpenEmbedding.functor.obj W)) ≃+
        (openIntegerConstantSheaf U).presheaf.obj
          (op ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj W))) :=
    { toFun := fun s => s.val
      invFun := fun s => ⟨s, Or.inl hW⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact e.toAddCommGrpIso ≪≫ (openIntegerConstantSheaf U).presheaf.mapIso
    (eqToIso (Opens.map_functor_eq (U := U) W)).op.symm

/-- Every index of the canonical one-summand image comparison is the identity on integers. -/
private theorem openIntegerFreeImageIso_ι {X : TopCat.{u}} (U : Opens X)
    (W : Opens (TopCat.of U)) (h : U.isOpenEmbedding.functor.obj W ⟶ U) :
    Sigma.ι (fun (_ : U.isOpenEmbedding.functor.obj W ⟶ U) =>
      AddCommGrpCat.of (ULift.{u} ℤ)) h ≫ (openIntegerFreeImageIso U W).hom =
        𝟙 (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  unfold openIntegerFreeImageIso
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The free-image comparison is natural on all opens of the subspace. -/
private noncomputable def openIntegerFreeImageNatIso {X : TopCat.{u}} (U : Opens X) :
    U.isOpenEmbedding.functor.op ⋙
        CategoryTheory.Presheaf.freeYoneda U (AddCommGrpCat.of (ULift.{u} ℤ)) ≅
      (Functor.const (Opens (TopCat.of U))ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  NatIso.ofComponents (fun W => openIntegerFreeImageIso U W.unop) (by
    intro V W f
    apply Sigma.hom_ext
    intro h
    let M := AddCommGrpCat.of (ULift.{u} ℤ)
    let q := U.isOpenEmbedding.functor
    change Sigma.ι (fun _ : q.obj V.unop ⟶ U => M) h ≫
      Sigma.map' (fun k : q.obj V.unop ⟶ U => q.map f.unop ≫ k) (fun _ => 𝟙 M) ≫
        (openIntegerFreeImageIso U W.unop).hom =
      Sigma.ι (fun _ : q.obj V.unop ⟶ U => M) h ≫
        (openIntegerFreeImageIso U V.unop).hom ≫ 𝟙 M
    rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp,
      openIntegerFreeImageIso_ι, ← Category.assoc, openIntegerFreeImageIso_ι,
      Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
/-- The constant-specific old conditional image comparison is natural. -/
private noncomputable def openIntegerRawImageNatIso {X : TopCat.{u}} (U : Opens X) :
    U.isOpenEmbedding.functor.op ⋙
        openExtensionByZeroPresheaf U (openIntegerConstantSheaf U) ≅
      (openIntegerConstantSheaf U).presheaf :=
  NatIso.ofComponents (fun W => openIntegerRawImageIso U W.unop) (by
    intro V W f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    let P := (openIntegerConstantSheaf U).presheaf
    let p := (Opens.map U.inclusion').op
    let q := U.isOpenEmbedding.functor.op
    let aV := (eqToIso (Opens.map_functor_eq (U := U) V.unop)).inv.op
    let aW := (eqToIso (Opens.map_functor_eq (U := U) W.unop)).inv.op
    change (P.map aW).hom ((P.map (p.map (q.map f))).hom s.val) =
      (P.map f).hom ((P.map aV).hom s.val)
    have h : p.map (q.map f) ≫ aW = aV ≫ f := Subsingleton.elim _ _
    have hh := congrArg P.map h
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hh
    exact congrArg (fun g => g.hom s.val) hh)

/-- The raw comparison on every indexed integral summand is the old seed restricted there. -/
private theorem openIntegerRawBeta_ι {X : TopCat.{u}} (U V : Opens X) (h : V ⟶ U) :
    Sigma.ι (fun (_ : V ⟶ U) => AddCommGrpCat.of (ULift.{u} ℤ)) h ≫
        (openIntegerRawBeta U).app (op V) = openIntegerRawSeed U ≫
          (openExtensionByZeroPresheaf U (openIntegerConstantSheaf U)).map h.op := by
  change Sigma.ι (fun (_ : V ⟶ U) => AddCommGrpCat.of (ULift.{u} ℤ)) h ≫
    Sigma.desc (fun k : V ⟶ U => openIntegerRawSeed U ≫
      (openExtensionByZeroPresheaf U (openIntegerConstantSheaf U)).map k.op) = _
  exact Sigma.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The literal old seed, restricted to an image open, is the ACTUAL constant-sheaf unit. -/
private theorem openIntegerSeed_image {X : TopCat.{u}} (U : Opens X)
    (W : Opens (TopCat.of U)) (h : U.isOpenEmbedding.functor.obj W ⟶ U) :
    openIntegerRawSeed U ≫
        (openExtensionByZeroPresheaf U (openIntegerConstantSheaf U)).map h.op ≫
          (openIntegerRawImageIso U W).hom =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of U))
        ((Functor.const (Opens (TopCat.of U))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op W) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  let P := (openIntegerConstantSheaf U).presheaf
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of U))
    ((Functor.const (Opens (TopCat.of U))ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  let a := (Opens.map U.inclusion').op.map h.op
  let b := (eqToIso (Opens.map_functor_eq (U := U) W)).inv.op
  change (P.map b).hom ((P.map a).hom
    ((η.app (op ((Opens.map U.inclusion').obj U))).hom n)) = (η.app (op W)).hom n
  have he := (η.naturality (a ≫ b)).symm
  change η.app (op ((Opens.map U.inclusion').obj U)) ≫ P.map (a ≫ b) =
    𝟙 (AddCommGrpCat.of (ULift.{u} ℤ)) ≫ η.app (op W) at he
  rw [Category.id_comp, CategoryTheory.Functor.map_comp] at he
  exact congrArg (fun g => g.hom n) he

set_option backward.isDefEq.respectTransparency false in
/-- The image-open beta comparison is the actual constant-presheaf sheafification unit. -/
private theorem openIntegerRawBeta_image {X : TopCat.{u}} (U : Opens X)
    (W : Opens (TopCat.of U)) :
    (openIntegerRawBeta U).app (op (U.isOpenEmbedding.functor.obj W)) ≫
        (openIntegerRawImageIso U W).hom =
      (openIntegerFreeImageIso U W).hom ≫
        (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of U))
          ((Functor.const (Opens (TopCat.of U))ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op W) := by
  apply Sigma.hom_ext
  intro h
  rw [← Category.assoc, openIntegerRawBeta_ι, Category.assoc, openIntegerSeed_image]
  conv_rhs => rw [← Category.assoc, openIntegerFreeImageIso_ι, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Naturally on image opens, beta is conjugate to the actual constant-presheaf unit. -/
private theorem openIntegerRawBeta_imageUnit {X : TopCat.{u}} (U : Opens X) :
    Functor.whiskerLeft U.isOpenEmbedding.functor.op (openIntegerRawBeta U) ≫
        (openIntegerRawImageNatIso U).hom =
      (openIntegerFreeImageNatIso U).hom ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of U))
          ((Functor.const (Opens (TopCat.of U))ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ))) := by
  apply NatTrans.ext
  funext W
  exact openIntegerRawBeta_image U W.unop

set_option backward.isDefEq.respectTransparency false in
/-- On subspace stalks, beta is invertible because the ACTUAL constant unit is stalkwise invertible. -/
private theorem openIntegerRawBeta_restricted_stalk_isIso {X : TopCat.{u}} (U : Opens X)
    (x : U) :
    IsIso ((TopCat.Presheaf.stalkFunctor (X := TopCat.of U) AddCommGrpCat.{u} x).map
      (Functor.whiskerLeft U.isOpenEmbedding.functor.op (openIntegerRawBeta U))) := by
  let P := (Functor.const (Opens (TopCat.of U))ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of U)) P
  have he : Functor.whiskerLeft U.isOpenEmbedding.functor.op (openIntegerRawBeta U) =
      (openIntegerFreeImageNatIso U).hom ≫ η ≫ (openIntegerRawImageNatIso U).inv := by
    apply (cancel_mono (openIntegerRawImageNatIso U).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact openIntegerRawBeta_imageUnit U
  let := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  rw [he, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Cofinality transfers the beta-specific subspace-stalk isomorphism to inside ambient points. -/
private theorem openIntegerRawBeta_stalk_isIso_inside {X : TopCat.{u}} (U : Opens X)
    (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map
      (openIntegerRawBeta U)) := by
  let := Functor.initial_of_adjunction
    (U.isOpenEmbedding.adjunctionNhds (f := U.inclusion') x)
  let e := Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft (OpenNhds (x : X))ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
      (OpenNhds.inclusion (x : X)).op)
    (Functor.Final.colimIso (U.isOpenEmbedding.functorNhds x).op)
  apply (NatIso.isIso_map_iff e (openIntegerRawBeta U)).mp
  change IsIso ((TopCat.Presheaf.stalkFunctor (X := TopCat.of U) AddCommGrpCat.{u} x).map
    (Functor.whiskerLeft U.isOpenEmbedding.functor.op (openIntegerRawBeta U)))
  exact openIntegerRawBeta_restricted_stalk_isIso U x

set_option backward.isDefEq.respectTransparency false in
/-- Outside U, every germ of the ACTUAL conditional integral presheaf is zero. -/
private theorem openIntegerRaw_stalk_isZero_outside {X : TopCat.{u}} (U : Opens X)
    (x : X) (hx : x ∉ U) :
    IsZero ((openExtensionByZeroPresheaf U (openIntegerConstantSheaf U)).stalk x) := by
  let P := openExtensionByZeroPresheaf U (openIntegerConstantSheaf U)
  have hz (t : P.stalk x) : t = 0 := by
    obtain ⟨V, hV, s, rfl⟩ := P.exists_germ_eq t
    have hs : s = 0 := by
      apply Subtype.ext
      rcases s.property with h | h
      · exact (hx (h hV)).elim
      · exact h
    rw [hs]
    exact map_zero (P.germ V x hV).hom
  apply (IsZero.iff_id_eq_zero (P.stalk x)).2
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  exact hz

set_option backward.isDefEq.respectTransparency false in
/-- Outside U, every representing free coproduct has empty index set, so every germ is zero. -/
private theorem openIntegerFree_stalk_isZero_outside {X : TopCat.{u}} (U : Opens X)
    (x : X) (hx : x ∉ U) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (CategoryTheory.Presheaf.freeYoneda U (AddCommGrpCat.of (ULift.{u} ℤ)))) := by
  let P : TopCat.Presheaf AddCommGrpCat.{u} X :=
    CategoryTheory.Presheaf.freeYoneda U (AddCommGrpCat.of (ULift.{u} ℤ))
  have hz (t : P.stalk x) : t = 0 := by
    obtain ⟨V, hV, s, rfl⟩ := P.exists_germ_eq t
    have hs : s = 0 := by
      have he : 𝟙 (P.obj (op V)) = 0 := by
        apply Sigma.hom_ext
        intro h
        exact (hx ((leOfHom h) hV)).elim
      exact congrArg (fun f => f.hom s) he
    rw [hs]
    exact map_zero (P.germ V x hV).hom
  apply (IsZero.iff_id_eq_zero (P.stalk x)).2
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  exact hz

set_option backward.isDefEq.respectTransparency false in
/-- The canonical raw beta is stalkwise invertible, without being pointwise invertible. -/
private theorem openIntegerRawBeta_stalk_isIso {X : TopCat.{u}} (U : Opens X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (openIntegerRawBeta U)) := by
  by_cases hx : x ∈ U
  · exact openIntegerRawBeta_stalk_isIso_inside U ⟨x, hx⟩
  · exact (openIntegerFree_stalk_isZero_outside U x hx).isIso
      (openIntegerRaw_stalk_isZero_outside U x hx) _

set_option backward.isDefEq.respectTransparency false in
/-- Sheafifying the literal raw seed gives a genuine isomorphism with the source's Z_U. -/
theorem openIntegerBeta_isIso {X : TopCat.{u}} (U : Opens X) :
    IsIso (openIntegerBeta U) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (openIntegerBeta U)).2
  intro x
  let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let P : TopCat.Presheaf AddCommGrpCat.{u} X :=
    CategoryTheory.Presheaf.freeYoneda U (AddCommGrpCat.of (ULift.{u} ℤ))
  let Q := openExtensionByZeroPresheaf U (openIntegerConstantSheaf U)
  let J := Opens.grothendieckTopology X
  let := openIntegerRawBeta_stalk_isIso U x
  let := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  let := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} Q
  have he : S.map (CategoryTheory.toSheafify J P) ≫ S.map (openIntegerBeta U).hom =
      S.map (openIntegerRawBeta U) ≫ S.map (CategoryTheory.toSheafify J Q) := by
    change S.map (CategoryTheory.toSheafify J P) ≫
        S.map (CategoryTheory.sheafifyMap J (openIntegerRawBeta U)) =
      S.map (openIntegerRawBeta U) ≫ S.map (CategoryTheory.toSheafify J Q)
    simpa only [P, Q, Functor.map_comp] using
      (congrArg S.map (CategoryTheory.toSheafify_naturality (J := J)
        (openIntegerRawBeta U))).symm
  exact IsIso.of_isIso_fac_left he

/-- The literal source generator: the old conditional seed at 1, followed by its sheafification unit. -/
noncomputable def openIntegerGenerator {X : TopCat.{u}} (U : Opens X) :
    (openIntegerExtensionByZero U).presheaf.obj (op U) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (openExtensionByZeroPresheaf U (openIntegerConstantSheaf U))).app (op U)).hom
      ((openIntegerRawSeed U).hom (ULift.up 1))

set_option backward.isDefEq.respectTransparency false in
/-- The transported free-Yoneda Hom map agrees with the literal old unit and seed. -/
private theorem openIntegerFreeHom_beta {X : TopCat.{u}} (U : Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) (φ : openIntegerExtensionByZero U ⟶ F) :
    CategoryTheory.Sheaf.freeYonedaHomEquiv (openIntegerBeta U ≫ φ) =
      openIntegerRawSeed U ≫
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (openExtensionByZeroPresheaf U (openIntegerConstantSheaf U))).app (op U) ≫
        φ.hom.app (op U) := by
  change CategoryTheory.Presheaf.freeYonedaHomEquiv
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) _ ≫
        (CategoryTheory.sheafifyMap _ (openIntegerRawBeta U) ≫ φ.hom)) = _
  rw [← Category.assoc, ← CategoryTheory.toSheafify_naturality]
  simp only [CategoryTheory.Presheaf.freeYonedaHomEquiv_comp, openIntegerRawBeta,
    Equiv.apply_symm_apply, NatTrans.comp_app, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Hom from the ACTUAL source Z_U represents sections additively, by evaluation at its old generator. -/
noncomputable def openIntegerSectionsAddEquiv {X : TopCat.{u}} (U : Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    (openIntegerExtensionByZero U ⟶ F) ≃+ F.presheaf.obj (op U) := by
  let := openIntegerBeta_isIso U
  let E : (openIntegerExtensionByZero U ⟶ F) ≃ F.presheaf.obj (op U) :=
    (Iso.homCongr (asIso (openIntegerBeta U)).symm (Iso.refl F)).trans
      (CategoryTheory.Sheaf.freeYonedaHomEquiv.trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv (F.presheaf.obj (op U))).toEquiv)
  have heval (φ : openIntegerExtensionByZero U ⟶ F) :
      E φ = (φ.hom.app (op U)).hom (openIntegerGenerator U) := by
    change (CategoryTheory.Sheaf.freeYonedaHomEquiv
      (openIntegerBeta U ≫ φ ≫ 𝟙 F)).hom (ULift.up 1) = _
    rw [Category.comp_id, openIntegerFreeHom_beta]
    rfl
  refine AddEquiv.mk' E ?_
  intro φ ψ
  rw [heval (φ + ψ), heval φ, heval ψ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The additive Hom equivalence is literally evaluation on the old conditional-unit generator. -/
theorem openIntegerSectionsAddEquiv_apply {X : TopCat.{u}} (U : Opens X)
    (F : X.Sheaf AddCommGrpCat.{u}) (φ : openIntegerExtensionByZero U ⟶ F) :
    openIntegerSectionsAddEquiv U F φ = (φ.hom.app (op U)).hom (openIntegerGenerator U) := by
  change (CategoryTheory.Sheaf.freeYonedaHomEquiv
    (openIntegerBeta U ≫ φ ≫ 𝟙 F)).hom (ULift.up 1) = _
  rw [Category.comp_id, openIntegerFreeHom_beta]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical free-presheaf map induced by an inclusion of opens. -/
private noncomputable def openIntegerFreeMap {X : TopCat.{u}} {V U : Opens X}
    (i : V ⟶ U) :
    CategoryTheory.Presheaf.freeYoneda V (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      CategoryTheory.Presheaf.freeYoneda U (AddCommGrpCat.of (ULift.{u} ℤ)) where
  app W := Sigma.map' (fun h : W.unop ⟶ V => h ≫ i)
    (fun _ => 𝟙 (AddCommGrpCat.of (ULift.{u} ℤ)))
  naturality A B f := by
    apply Sigma.hom_ext
    intro h
    let M := AddCommGrpCat.of (ULift.{u} ℤ)
    change Sigma.ι (fun _ : A.unop ⟶ V => M) h ≫
        (Sigma.map' (f := fun _ : A.unop ⟶ V => M) (g := fun _ : B.unop ⟶ V => M)
          (fun k : A.unop ⟶ V => f.unop ≫ k) (fun _ => 𝟙 M) ≫
          Sigma.map' (f := fun _ : B.unop ⟶ V => M) (g := fun _ : B.unop ⟶ U => M)
            (fun k : B.unop ⟶ V => k ≫ i) (fun _ => 𝟙 M)) =
      Sigma.ι (fun _ : A.unop ⟶ V => M) h ≫
        (Sigma.map' (f := fun _ : A.unop ⟶ V => M) (g := fun _ : A.unop ⟶ U => M)
          (fun k : A.unop ⟶ V => k ≫ i) (fun _ => 𝟙 M) ≫
          Sigma.map' (f := fun _ : A.unop ⟶ U => M) (g := fun _ : B.unop ⟶ U => M)
            (fun k : A.unop ⟶ U => f.unop ≫ k) (fun _ => 𝟙 M))
    rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp,
      Sigma.ι_comp_map', Category.id_comp, ← Category.assoc,
      Sigma.ι_comp_map', Category.id_comp, Sigma.ι_comp_map', Category.id_comp]
    rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity of the thin-open index map makes the canonical free-presheaf map a mono. -/
private theorem openIntegerFreeMap_mono {X : TopCat.{u}} {V U : Opens X}
    (i : V ⟶ U) : Mono (openIntegerFreeMap i) := by
  have : ∀ W : (Opens X)ᵒᵖ, Mono ((openIntegerFreeMap i).app W) := by
    intro W
    let M := AddCommGrpCat.of (ULift.{u} ℤ)
    change Mono (Sigma.map' (f := fun _ : W.unop ⟶ V => M)
      (g := fun _ : W.unop ⟶ U => M) (fun h : W.unop ⟶ V => h ≫ i) (fun _ => 𝟙 M))
    exact MonoCoprod.mono_map'_of_injective (fun _ : W.unop ⟶ U => M)
      (fun h : W.unop ⟶ V => h ≫ i) (fun _ _ _ => Subsingleton.elim _ _)
  exact NatTrans.mono_of_mono_app (openIntegerFreeMap i)

set_option backward.isDefEq.respectTransparency false in
/-- The ACTUAL source inclusion Z_V→Z_U, transported by the same canonical seed comparisons. -/
noncomputable def openIntegerInclusion {X : TopCat.{u}} {V U : Opens X}
    (i : V ⟶ U) : openIntegerExtensionByZero V ⟶ openIntegerExtensionByZero U := by
  let := openIntegerBeta_isIso V
  exact (asIso (openIntegerBeta V)).inv ≫
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (openIntegerFreeMap i) ≫ openIntegerBeta U

set_option backward.isDefEq.respectTransparency false in
/-- The natural inclusion of the ACTUAL source extension-by-zero sheaves is a monomorphism. -/
theorem openIntegerInclusion_mono {X : TopCat.{u}} {V U : Opens X}
    (i : V ⟶ U) : Mono (openIntegerInclusion i) := by
  let := openIntegerBeta_isIso V
  let := openIntegerBeta_isIso U
  let := openIntegerFreeMap_mono i
  change Mono ((asIso (openIntegerBeta V)).inv ≫
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (openIntegerFreeMap i) ≫ openIntegerBeta U)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The free-presheaf Hom equivalence sends an open inclusion to actual section restriction. -/
private theorem openIntegerFreeHom_restriction {X : TopCat.{u}} {V U : Opens X}
    (i : V ⟶ U) (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (φ : CategoryTheory.Presheaf.freeYoneda U (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ F) :
    CategoryTheory.Presheaf.freeYonedaHomEquiv (openIntegerFreeMap i ≫ φ) =
      CategoryTheory.Presheaf.freeYonedaHomEquiv φ ≫ F.map i.op := by
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  change Sigma.ι (fun _ : V ⟶ V => M) (𝟙 V) ≫
      ((openIntegerFreeMap i).app (op V) ≫ φ.app (op V)) =
    (Sigma.ι (fun _ : U ⟶ U => M) (𝟙 U) ≫ φ.app (op U)) ≫ F.map i.op
  have hs : Sigma.ι (fun _ : V ⟶ V => M) (𝟙 V) ≫
      (openIntegerFreeMap i).app (op V) = Sigma.ι (fun _ : V ⟶ U => M) i := by
    change Sigma.ι (fun _ : V ⟶ V => M) (𝟙 V) ≫
      Sigma.map' (f := fun _ : V ⟶ V => M) (g := fun _ : V ⟶ U => M)
        (fun h : V ⟶ V => h ≫ i) (fun _ => 𝟙 M) = _
    simp only [Sigma.ι_comp_map', Category.id_comp]
  rw [← Category.assoc, hs]
  have hn := congrArg (fun f => Sigma.ι (fun _ : U ⟶ U => M) (𝟙 U) ≫ f)
    (φ.naturality i.op)
  have ht : Sigma.ι (fun _ : U ⟶ U => M) (𝟙 U) ≫
      (CategoryTheory.Presheaf.freeYoneda U M).map i.op =
        Sigma.ι (fun _ : V ⟶ U => M) i := by
    change Sigma.ι (fun _ : U ⟶ U => M) (𝟙 U) ≫
      Sigma.map' (f := fun _ : U ⟶ U => M) (g := fun _ : V ⟶ U => M)
        (fun h : U ⟶ U => i ≫ h) (fun _ => 𝟙 M) = _
    simp only [Sigma.ι_comp_map', Category.id_comp, Category.comp_id]
  change Sigma.ι (fun _ : U ⟶ U => M) (𝟙 U) ≫
      ((CategoryTheory.Presheaf.freeYoneda U M).map i.op ≫ φ.app (op V)) =
    Sigma.ι (fun _ : U ⟶ U => M) (𝟙 U) ≫ (φ.app (op U) ≫ F.map i.op) at hn
  simpa only [← Category.assoc, ht] using hn

set_option backward.isDefEq.respectTransparency false in
/-- Sheafification preserves the canonical free-Hom restriction square through its actual unit. -/
private theorem openIntegerSheafFreeHom_restriction {X : TopCat.{u}} {V U : Opens X}
    (i : V ⟶ U) (F : X.Sheaf AddCommGrpCat.{u})
    (φ : CategoryTheory.Sheaf.freeYoneda (Opens.grothendieckTopology X) U
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ F) :
    CategoryTheory.Sheaf.freeYonedaHomEquiv
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          (openIntegerFreeMap i) ≫ φ) =
      CategoryTheory.Sheaf.freeYonedaHomEquiv φ ≫ F.presheaf.map i.op := by
  let J := Opens.grothendieckTopology X
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  change CategoryTheory.Presheaf.freeYonedaHomEquiv
      (CategoryTheory.toSheafify J (CategoryTheory.Presheaf.freeYoneda V M) ≫
        (CategoryTheory.sheafifyMap J (openIntegerFreeMap i) ≫ φ.hom)) =
    CategoryTheory.Presheaf.freeYonedaHomEquiv
      (CategoryTheory.toSheafify J (CategoryTheory.Presheaf.freeYoneda U M) ≫ φ.hom) ≫
        F.presheaf.map i.op
  rw [← Category.assoc, ← CategoryTheory.toSheafify_naturality, Category.assoc]
  exact openIntegerFreeHom_restriction i F.presheaf _

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with the ACTUAL source inclusion is the literal restriction of sections. -/
theorem openIntegerSectionsAddEquiv_restriction {X : TopCat.{u}} {V U : Opens X}
    (i : V ⟶ U) (F : X.Sheaf AddCommGrpCat.{u})
    (φ : openIntegerExtensionByZero U ⟶ F) :
    openIntegerSectionsAddEquiv V F (openIntegerInclusion i ≫ φ) =
      (F.presheaf.map i.op).hom (openIntegerSectionsAddEquiv U F φ) := by
  let := openIntegerBeta_isIso V
  change (CategoryTheory.Sheaf.freeYonedaHomEquiv
      (openIntegerBeta V ≫ (openIntegerInclusion i ≫ φ) ≫ 𝟙 F)).hom (ULift.up 1) =
    (F.presheaf.map i.op).hom
      ((CategoryTheory.Sheaf.freeYonedaHomEquiv (openIntegerBeta U ≫ φ ≫ 𝟙 F)).hom (ULift.up 1))
  rw [Category.comp_id, Category.comp_id]
  have he : openIntegerBeta V ≫ (openIntegerInclusion i ≫ φ) =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        (openIntegerFreeMap i) ≫ (openIntegerBeta U ≫ φ) := by
    change (asIso (openIntegerBeta V)).hom ≫
        (((asIso (openIntegerBeta V)).inv ≫
          (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
            (openIntegerFreeMap i) ≫ openIntegerBeta U) ≫ φ) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [he, openIntegerSheafFreeHom_restriction]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The ACTUAL inclusion carries the old generator to the literal restriction of the old generator. -/
theorem openIntegerInclusion_generator {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U) :
    ((openIntegerInclusion i).hom.app (op V)).hom (openIntegerGenerator V) =
      ((openIntegerExtensionByZero U).presheaf.map i.op).hom (openIntegerGenerator U) := by
  have h := openIntegerSectionsAddEquiv_restriction i (openIntegerExtensionByZero U)
    (𝟙 (openIntegerExtensionByZero U))
  rw [Category.comp_id, openIntegerSectionsAddEquiv_apply,
    openIntegerSectionsAddEquiv_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The source Hom-section equivalence is natural in every target abelian sheaf. -/
theorem openIntegerSectionsAddEquiv_naturality {X : TopCat.{u}} (U : Opens X)
    (F G : X.Sheaf AddCommGrpCat.{u}) (φ : openIntegerExtensionByZero U ⟶ F)
    (δ : F ⟶ G) : openIntegerSectionsAddEquiv U G (φ ≫ δ) =
      (δ.hom.app (op U)).hom (openIntegerSectionsAddEquiv U F φ) := by
  rw [openIntegerSectionsAddEquiv_apply, openIntegerSectionsAddEquiv_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every injective object in the ACTUAL abelian-sheaf category is flasque.
The source argument lifts through Z_V→Z_U using its literal section-representing equivalence. -/
theorem injectiveAbelianSheaf_isFlasque {X : TopCat.{u}}
    (F : X.Sheaf AddCommGrpCat.{u}) [CategoryTheory.Injective F] :
    TopCat.Sheaf.IsFlasque F := by
  refine ⟨?_⟩
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro t
  let φ : openIntegerExtensionByZero V.unop ⟶ F :=
    (openIntegerSectionsAddEquiv V.unop F).symm t
  let := openIntegerInclusion_mono i.unop
  let ψ : openIntegerExtensionByZero U.unop ⟶ F :=
    CategoryTheory.Injective.factorThru φ (openIntegerInclusion i.unop)
  refine ⟨openIntegerSectionsAddEquiv U.unop F ψ, ?_⟩
  change (F.presheaf.map i).hom (openIntegerSectionsAddEquiv U.unop F ψ) = t
  change (F.presheaf.map i.unop.op).hom (openIntegerSectionsAddEquiv U.unop F ψ) = t
  rw [← openIntegerSectionsAddEquiv_restriction i.unop F ψ]
  change openIntegerSectionsAddEquiv V.unop F
    (openIntegerInclusion i.unop ≫
      CategoryTheory.Injective.factorThru φ (openIntegerInclusion i.unop)) = t
  rw [CategoryTheory.Injective.comp_factorThru]
  exact (openIntegerSectionsAddEquiv V.unop F).apply_symm_apply t

end Hartshorne
