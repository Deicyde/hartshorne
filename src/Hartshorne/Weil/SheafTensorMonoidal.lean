/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Weil.EtaleTateTwist
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.CategoryTheory.Monoidal.Closed.Transport
import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The symmetric monoidal category of abelian sheaves on a site

For a site `(C, J)` whose abelian presheaves have associated sheaves, the tensor product of two
abelian sheaves `F` and `G` is `Hartshorne.sheafTensor J F G`, the sheafification of the
sectionwise tensor product `U ↦ F(U) ⊗_ℤ G(U)` (in `Hartshorne.Weil.EtaleTateTwist`). This file
makes the category of abelian sheaves a symmetric monoidal category with this tensor product and
with unit the constant sheaf `ℤ`.

Abelian groups are given the symmetric monoidal closed structure of the tensor product,
transported from modules over `ℤ` (lifted to the universe of the groups) along the equivalence
`uliftIntModuleEquivAb`; this is a `def` (`abTensorMonoidal`), not an instance, since abelian
groups also carry the cartesian monoidal structure. Abelian presheaves then carry the sectionwise
tensor product, and Mathlib's monoidal localization (`CategoryTheory.Sheaf.monoidalCategory`)
descends it, with its symmetry, to sheaves, provided that the morphisms inverted by
sheafification are stable under tensor products. That holds on small sites by Mathlib's
internal-Hom argument, and transfers to essentially small sites
(`abSheafW_isMonoidal_of_essentiallySmall`), to sites with an essentially small cover-dense full
subsite having the same abelian sheaves (`abSheafW_isMonoidal_of_isCoverDense`), and in particular
to the small étale site of a scheme (`AlgebraicGeometry.Scheme.etaleW_isMonoidal`), through its
affine étale subsite.

## Main declarations

- `Hartshorne.sheafTensorMonoidal J`, `Hartshorne.sheafTensorSymmetric J`: the monoidal and
  symmetric structures on `Sheaf J Ab`; the unit is the constant sheaf `ℤ`
  (`sheafTensorUnit_eq`).
- `Hartshorne.sheafTensorIsoTensor J F G : sheafTensor J F G ≅ F ⊗ G`, sending the local section
  `f ⊗ g` to `f ⊗ g` (`sheafTensorIsoTensor_hom_tmul`) and natural in `F` and `G`
  (`sheafTensorMap_comp_isoTensor`).
- The associator, unitors and braiding on local sections:
  `AbSheaf.associator_hom_tmulSection`, `AbSheaf.leftUnitor_hom_tmulSection`,
  `AbSheaf.rightUnitor_hom_tmulSection`, `AbSheaf.braiding_hom_tmulSection`.
- `Hartshorne.sheafificationBraided J`: sheafification is a braided monoidal functor.
- `Hartshorne.sheafTensorPowSuccAddIso`: `F^{⊗(a+1)} ⊗ F^{⊗(b+1)} ≅ F^{⊗(a+b+2)}`.
-/

universe u v w v' w'

open CategoryTheory MonoidalCategory Limits Opposite
open scoped TensorProduct

namespace Hartshorne

section AbTensor

/-- An abelian group, as a module over `ℤ` (lifted to universe `u`). -/
@[simps]
noncomputable def abToULiftIntModule : Ab.{u} ⥤ ModuleCat.{u} (ULift.{u} ℤ) where
  obj A := ModuleCat.of (ULift.{u} ℤ) A
  map f := ModuleCat.ofHom
    { toFun := f
      map_add' := map_add f.hom
      map_smul' r x := by
        change f (r.down • x) = r.down • f x
        exact map_zsmul f.hom r.down x }

/-- Modules over `ℤ` (lifted to universe `u`) are the same as abelian groups. -/
noncomputable def uliftIntModuleEquivAb : ModuleCat.{u} (ULift.{u} ℤ) ≌ Ab.{u} where
  functor := forget₂ _ _
  inverse := abToULiftIntModule
  unitIso := NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      map_add' _ _ := rfl
      map_smul' r m := by
        rw [RingHom.id_apply]
        have h := @Int.cast_smul_eq_zsmul (ULift.{u} ℤ) M _ _ M.isModule r.down m
        rw [show ((r.down : ℤ) : ULift.{u} ℤ) = r by ext; simp] at h
        rw [h]
        rfl
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ ↦ rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  functor_unitIso_comp _ := rfl

/-- The tensor-product monoidal structure on abelian groups, transported from modules over
`ℤ`. It is not an instance, since abelian groups also carry the cartesian monoidal structure. -/
@[instance_reducible]
noncomputable def abTensorMonoidal : MonoidalCategory Ab.{u} :=
  Monoidal.transport uliftIntModuleEquivAb

attribute [local instance] abTensorMonoidal

/-- The tensor product of abelian groups is the tensor product over `ℤ` (lifted). -/
lemma abTensor_tensorObj (A B : Ab.{u}) :
    A ⊗ B = AddCommGrpCat.of (A ⊗[ULift.{u} ℤ] B) := rfl

/-- The symmetric structure on the tensor product of abelian groups. -/
@[instance_reducible]
noncomputable def abTensorSymmetric : SymmetricCategory Ab.{u} :=
  inferInstanceAs (SymmetricCategory (Monoidal.Transported uliftIntModuleEquivAb))

/-- The tensor product of abelian groups is closed. -/
@[instance_reducible]
noncomputable def abTensorClosed : MonoidalClosed Ab.{u} :=
  inferInstanceAs (MonoidalClosed (Monoidal.Transported uliftIntModuleEquivAb))

attribute [local instance] abTensorSymmetric abTensorClosed

/-- The comparison of the tensor products over `ℤ` and over `ℤ` lifted to universe `u`. -/
noncomputable def intTensorAddEquiv (A B : Ab.{u}) :
    (A ⊗[ℤ] B) ≃+ (A ⊗[ULift.{u} ℤ] B) :=
  (TensorProduct.equivOfCompatibleSMul ℤ (ULift.{u} ℤ) ℤ A B).symm.toAddEquiv

@[simp]
lemma intTensorAddEquiv_tmul (A B : Ab.{u}) (a : A) (b : B) :
    intTensorAddEquiv A B (a ⊗ₜ b) = a ⊗ₜ b := rfl

end AbTensor

section Localization

attribute [local instance] abTensorMonoidal abTensorSymmetric abTensorClosed

variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)

/-- On an essentially small site, the morphisms of abelian presheaves inverted by sheafification
are stable under tensor products. -/
theorem abSheafW_isMonoidal_of_essentiallySmall [EssentiallySmall.{u} C] :
    (J.W (A := Ab.{u})).IsMonoidal :=
  GrothendieckTopology.W.transport_isMonoidal J Ab.{u}
    ((equivSmallModel.{u} C).inverse.inducedTopology J) (equivSmallModel.{u} C).inverse

/-- If a site has an essentially small cover-dense full subsite with the same category of
abelian sheaves, the morphisms of abelian presheaves inverted by sheafification are stable under
tensor products. -/
theorem abSheafW_isMonoidal_of_isCoverDense {D : Type w'} [Category.{v'} D]
    [EssentiallySmall.{u} D] (K : GrothendieckTopology D) (G : D ⥤ C) [G.IsCoverDense J]
    [G.Full] [G.IsContinuous K J] [(G.sheafPushforwardContinuous Ab.{u} K J).EssSurj] :
    (J.W (A := Ab.{u})).IsMonoidal :=
  have := abSheafW_isMonoidal_of_essentiallySmall.{u} K
  GrothendieckTopology.W.transport_isMonoidal J Ab.{u} K G

end Localization

end Hartshorne

namespace AlgebraicGeometry.Scheme

attribute [local instance] Hartshorne.abTensorMonoidal Hartshorne.abTensorSymmetric
  Hartshorne.abTensorClosed

/-- On the small étale site, the morphisms of abelian presheaves inverted by sheafification are
stable under tensor products. -/
instance etaleW_isMonoidal (X : Scheme.{u}) :
    (X.smallEtaleTopology.W (A := Ab.{u})).IsMonoidal :=
  Hartshorne.abSheafW_isMonoidal_of_isCoverDense.{u} _ (AffineEtale.topology X)
    (AffineEtale.Spec X)

end AlgebraicGeometry.Scheme

namespace Hartshorne

section PresheafComparison

attribute [local instance] abTensorMonoidal

variable {C : Type w} [Category.{v} C]

/-- The sectionwise tensor product over `ℤ` is isomorphic to the tensor product of abelian
presheaves, by the identity on the sections `a ⊗ b`. -/
noncomputable def presheafTensorIsoTensor (P Q : Cᵒᵖ ⥤ Ab.{u}) : presheafTensor P Q ≅ P ⊗ Q :=
  NatIso.ofComponents (fun U ↦ (intTensorAddEquiv (P.obj U) (Q.obj U)).toAddCommGrpIso) (by
    intro U V f
    ext x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul a b => rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))

/-- The comparison of presheaf tensor products is compatible with tensor products of
morphisms. -/
lemma presheafTensorMap_comp_isoTensor {P P' Q Q' : Cᵒᵖ ⥤ Ab.{u}} (α : P ⟶ P') (β : Q ⟶ Q') :
    presheafTensorMap α β ≫ (presheafTensorIsoTensor P' Q').hom =
      (presheafTensorIsoTensor P Q).hom ≫ (α ⊗ₘ β) := by
  ext U x
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a b => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end PresheafComparison

section SheafTensor

attribute [local instance] abTensorMonoidal abTensorSymmetric abTensorClosed

variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{u}]
  [(J.W (A := Ab.{u})).IsMonoidal]

/-- **The monoidal category of abelian sheaves** on a site, obtained by localizing the
sectionwise tensor product of abelian presheaves along sheafification. -/
@[instance_reducible]
noncomputable def sheafTensorMonoidal : MonoidalCategory (Sheaf J Ab.{u}) :=
  Sheaf.monoidalCategory J Ab.{u}

attribute [local instance] sheafTensorMonoidal

/-- The braided structure on the monoidal category of abelian sheaves. -/
@[instance_reducible]
noncomputable def sheafTensorBraided : BraidedCategory (Sheaf J Ab.{u}) :=
  Sheaf.braidedCategory J Ab.{u}

/-- The symmetric structure on the monoidal category of abelian sheaves. -/
@[instance_reducible]
noncomputable def sheafTensorSymmetric : SymmetricCategory (Sheaf J Ab.{u}) :=
  Sheaf.symmetricCategory J Ab.{u}

/-- The braiding of the symmetric structure is that of `sheafTensorBraided`. -/
lemma sheafTensorSymmetric_toBraidedCategory :
    (sheafTensorSymmetric J).toBraidedCategory = sheafTensorBraided J := rfl

attribute [local instance] sheafTensorBraided

/-- The unit object is the constant sheaf `ℤ`. -/
lemma sheafTensorUnit_eq :
    𝟙_ (Sheaf J Ab.{u}) = (constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) := rfl

/-- Sheafification is a braided (symmetric) monoidal functor. -/
noncomputable abbrev sheafificationBraided : (presheafToSheaf J Ab.{u}).Braided :=
  inferInstance

/-- The forgetful functor from sheaves to presheaves is lax monoidal, as the right adjoint of
sheafification. -/
@[instance_reducible]
noncomputable def sheafToPresheafLaxMonoidal : (sheafToPresheaf J Ab.{u}).LaxMonoidal :=
  (sheafificationAdjunction J Ab.{u}).rightAdjointLaxMonoidal

attribute [local instance] sheafToPresheafLaxMonoidal

variable {J} (F G H : Sheaf J Ab.{u})

namespace AbSheaf

/-- The canonical map from the sectionwise tensor product of the underlying presheaves to the
underlying presheaf of `F ⊗ G`. -/
noncomputable def tensorπ : F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u}) F G

/-- The local section `f ⊗ g` of `F ⊗ G`. -/
noncomputable def tmulSection {U : Cᵒᵖ} (f : F.obj.obj U) (g : G.obj.obj U) :
    (F ⊗ G).obj.obj U :=
  (tensorπ F G).app U (f ⊗ₜ[ULift.{u} ℤ] g)

/-- The local section of the constant sheaf `ℤ` given by an integer. -/
noncomputable def intSection (U : Cᵒᵖ) (n : ℤ) : (𝟙_ (Sheaf J Ab.{u})).obj.obj U :=
  (Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u})).app U (ULift.up n)

/-- The associator sends `(f ⊗ g) ⊗ h` to `f ⊗ (g ⊗ h)`. -/
theorem associator_hom_tmulSection {U : Cᵒᵖ} (f : F.obj.obj U) (g : G.obj.obj U)
    (h : H.obj.obj U) :
    (α_ F G H).hom.hom.app U (tmulSection (F ⊗ G) H (tmulSection F G f g) h) =
      tmulSection F (G ⊗ H) f (tmulSection G H g h) :=
  congrArg (fun k ↦ (k.app U) ((f ⊗ₜ g) ⊗ₜ h))
    (Functor.LaxMonoidal.associativity (sheafToPresheaf J Ab.{u}) F G H)

/-- The left unitor sends `n ⊗ f` to `n • f`. -/
theorem leftUnitor_hom_tmulSection {U : Cᵒᵖ} (n : ℤ) (f : F.obj.obj U) :
    (λ_ F).hom.hom.app U (tmulSection (𝟙_ _) F (intSection U n) f) = n • f :=
  (congrArg (fun k ↦ (k.app U) (ULift.up n ⊗ₜ f))
    (Functor.LaxMonoidal.left_unitality (sheafToPresheaf J Ab.{u}) F)).symm

/-- The right unitor sends `f ⊗ n` to `n • f`. -/
theorem rightUnitor_hom_tmulSection {U : Cᵒᵖ} (n : ℤ) (f : F.obj.obj U) :
    (ρ_ F).hom.hom.app U (tmulSection F (𝟙_ _) f (intSection U n)) = n • f :=
  (congrArg (fun k ↦ (k.app U) (f ⊗ₜ ULift.up n))
    (Functor.LaxMonoidal.right_unitality (sheafToPresheaf J Ab.{u}) F)).symm

/-- The comparison map is compatible with the braidings. -/
lemma tensorπ_braiding :
    tensorπ F G ≫ (β_ F G).hom.hom = (β_ F.obj G.obj).hom ≫ tensorπ G F := by
  simp only [tensorπ, Adjunction.rightAdjointLaxMonoidal_μ]
  change _ ≫ (sheafToPresheaf J Ab.{u}).map (β_ F G).hom = _
  change _ = (β_ ((sheafToPresheaf J Ab.{u}).obj F) ((sheafToPresheaf J Ab.{u}).obj G)).hom ≫ _
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp,
    ← (sheafificationAdjunction J Ab.{u}).unit_naturality_assoc, ← Functor.map_comp]
  congr 2
  rw [Functor.map_braiding]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc, BraidedCategory.braiding_naturality]

/-- The braiding sends `f ⊗ g` to `g ⊗ f`. -/
theorem braiding_hom_tmulSection {U : Cᵒᵖ} (f : F.obj.obj U) (g : G.obj.obj U) :
    (β_ F G).hom.hom.app U (tmulSection F G f g) = tmulSection G F g f :=
  congrArg (fun k ↦ (k.app U) (f ⊗ₜ g)) (tensorπ_braiding F G)

variable {F G} {F' G' : Sheaf J Ab.{u}}

/-- `(φ ⊗ ψ)(f ⊗ g) = φ f ⊗ ψ g`. -/
theorem tensorHom_tmulSection (φ : F ⟶ F') (ψ : G ⟶ G') {U : Cᵒᵖ} (f : F.obj.obj U)
    (g : G.obj.obj U) :
    (φ ⊗ₘ ψ).hom.app U (tmulSection F G f g) = tmulSection F' G' (φ.hom.app U f) (ψ.hom.app U g) :=
  (congrArg (fun k ↦ (k.app U) (f ⊗ₜ g))
    (Functor.LaxMonoidal.μ_natural (sheafToPresheaf J Ab.{u}) φ ψ)).symm

end AbSheaf

open AbSheaf

variable (J)

/-- **The comparison isomorphism** between the sheafified sectionwise tensor product over `ℤ`
and the tensor product of the monoidal structure. -/
noncomputable def sheafTensorIsoTensor : sheafTensor J F G ≅ F ⊗ G :=
  (presheafToSheaf J Ab.{u}).mapIso (presheafTensorIsoTensor F.obj G.obj) ≪≫
    (Functor.Monoidal.μIso (presheafToSheaf J Ab.{u}) F.obj G.obj).symm ≪≫
    tensorIso (asIso ((sheafificationAdjunction J Ab.{u}).counit.app F))
      (asIso ((sheafificationAdjunction J Ab.{u}).counit.app G))

/-- The comparison isomorphism, precomposed with the sheafification map, is `tensorπ`. -/
lemma toSheafify_comp_sheafTensorIsoTensor :
    toSheafify J (presheafTensor F.obj G.obj) ≫ (sheafTensorIsoTensor J F G).hom.hom =
      (presheafTensorIsoTensor F.obj G.obj).hom ≫ tensorπ F G := by
  simp only [tensorπ, Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
  erw [← (sheafificationAdjunction J Ab.{u}).unit_naturality_assoc]
  rfl

/-- The comparison isomorphism sends the local section `f ⊗ g` of the sheafified sectionwise
tensor product to the local section `f ⊗ g` of `F ⊗ G`. -/
theorem sheafTensorIsoTensor_hom_tmul {U : Cᵒᵖ} (f : F.obj.obj U) (g : G.obj.obj U) :
    (sheafTensorIsoTensor J F G).hom.hom.app U
        ((toSheafify J (presheafTensor F.obj G.obj)).app U (f ⊗ₜ[ℤ] g)) =
      tmulSection F G f g :=
  congrArg (fun k ↦ (k.app U) (f ⊗ₜ g)) (toSheafify_comp_sheafTensorIsoTensor J F G)

variable {J F G} {F' G' : Sheaf J Ab.{u}}

/-- The comparison isomorphism is natural: it carries `sheafTensorMap α β` to `α ⊗ β`. -/
theorem sheafTensorMap_comp_isoTensor (α : F ⟶ F') (β : G ⟶ G') :
    sheafTensorMap J α β ≫ (sheafTensorIsoTensor J F' G').hom =
      (sheafTensorIsoTensor J F G).hom ≫ (α ⊗ₘ β) := by
  apply ((sheafificationAdjunction J Ab.{u}).homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change toSheafify J _ ≫ (sheafTensorMap J α β).hom ≫ (sheafTensorIsoTensor J F' G').hom.hom =
    (toSheafify J _ ≫ (sheafTensorIsoTensor J F G).hom.hom) ≫ (α ⊗ₘ β).hom
  have h1 : toSheafify J (presheafTensor F.obj G.obj) ≫ (sheafTensorMap J α β).hom =
      presheafTensorMap α.hom β.hom ≫ toSheafify J (presheafTensor F'.obj G'.obj) :=
    (toSheafify_naturality J (presheafTensorMap α.hom β.hom)).symm
  calc toSheafify J _ ≫ (sheafTensorMap J α β).hom ≫ (sheafTensorIsoTensor J F' G').hom.hom
      = (toSheafify J _ ≫ (sheafTensorMap J α β).hom) ≫ (sheafTensorIsoTensor J F' G').hom.hom :=
        (Category.assoc _ _ _).symm
    _ = presheafTensorMap α.hom β.hom ≫ toSheafify J _ ≫ (sheafTensorIsoTensor J F' G').hom.hom := by
        rw [h1]; exact Category.assoc _ _ _
    _ = presheafTensorMap α.hom β.hom ≫ (presheafTensorIsoTensor F'.obj G'.obj).hom ≫
          tensorπ F' G' := by
        rw [toSheafify_comp_sheafTensorIsoTensor]
    _ = (presheafTensorIsoTensor F.obj G.obj).hom ≫ (α.hom ⊗ₘ β.hom) ≫ tensorπ F' G' := by
        rw [← Category.assoc, presheafTensorMap_comp_isoTensor, Category.assoc]
    _ = ((presheafTensorIsoTensor F.obj G.obj).hom ≫ tensorπ F G) ≫ (α ⊗ₘ β).hom := by
        rw [Category.assoc]
        exact congrArg (_ ≫ ·) (Functor.LaxMonoidal.μ_natural (sheafToPresheaf J Ab.{u}) α β)
    _ = (toSheafify J _ ≫ (sheafTensorIsoTensor J F G).hom.hom) ≫ (α ⊗ₘ β).hom := by
        rw [toSheafify_comp_sheafTensorIsoTensor]

end SheafTensor

section Powers

attribute [local instance] abTensorMonoidal abTensorSymmetric abTensorClosed

variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{u}]

/-- The tensor product of sheaves carries isomorphisms in the first variable to isomorphisms. -/
@[simps]
noncomputable def sheafTensorIsoLeft {F F' : Sheaf J Ab.{u}} (e : F ≅ F') (G : Sheaf J Ab.{u}) :
    sheafTensor J F G ≅ sheafTensor J F' G where
  hom := sheafTensorMap J e.hom (𝟙 G)
  inv := sheafTensorMap J e.inv (𝟙 G)
  hom_inv_id := by rw [← sheafTensorMap_comp, e.hom_inv_id, Category.id_comp, sheafTensorMap_id]
  inv_hom_id := by rw [← sheafTensorMap_comp, e.inv_hom_id, Category.id_comp, sheafTensorMap_id]

variable [(J.W (A := Ab.{u})).IsMonoidal]

attribute [local instance] sheafTensorMonoidal

/-- The associativity isomorphism `(F ⊗ G) ⊗ H ≅ F ⊗ (G ⊗ H)` for the sheafified sectionwise
tensor product. -/
noncomputable def sheafTensorAssocIso (F G H : Sheaf J Ab.{u}) :
    sheafTensor J (sheafTensor J F G) H ≅ sheafTensor J F (sheafTensor J G H) :=
  sheafTensorIsoTensor J _ _ ≪≫ whiskerRightIso (sheafTensorIsoTensor J F G) H ≪≫ α_ F G H ≪≫
    (whiskerLeftIso F (sheafTensorIsoTensor J G H)).symm ≪≫ (sheafTensorIsoTensor J _ _).symm

/-- `F^{⊗(a+1)} ⊗ F^{⊗(b+1)} ≅ F^{⊗(a+b+2)}`, built from the associativity isomorphisms. -/
noncomputable def sheafTensorPowSuccAddIso (F : Sheaf J Ab.{u}) (a : ℕ) :
    (b : ℕ) → sheafTensor J (sheafTensorPowSucc J F a) (sheafTensorPowSucc J F b) ≅
      sheafTensorPowSucc J F (a + b + 1)
  | 0 => Iso.refl _
  | b + 1 => (sheafTensorAssocIso J _ _ _).symm ≪≫
      sheafTensorIsoLeft J (sheafTensorPowSuccAddIso F a b) F

end Powers

end Hartshorne
