/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeSpec
import Hartshorne.Scheme.SheafTensorAlgebras
import Hartshorne.Scheme.InvertibleSectionClearingDenominators

/-!
# Quasi-coherent sheaves of algebras as quasi-coherent algebras

Supplements Hartshorne II, Exercise 5.17 (p. 128). A quasi-coherent `𝒪_Y`-module `M` with a
commutative sheaf of `𝒪_Y`-algebras structure (a multiplication and a unit compatible with
restriction, `ModuleSheafAlgebra`) is a quasi-coherent `𝒪_Y`-algebra in the sense of
`Hartshorne.QuasiCoherentAlgebra`: its rings of sections over the affine opens of `Y`, with the
structure maps `r ↦ r • 1`, satisfy `A(D(r)) = A(U)_r`. This last condition is Hartshorne's
Lemma II.5.3 for the quasi-coherent module `M` (sections over `D(r)` are, after multiplication by
a power of `r`, restrictions of sections over `U`, and sections vanishing on `D(r)` are killed by a
power of `r`).

## Main definitions

* `ModuleSheafAlgebra.IsCommutative`: the multiplication of a sheaf of algebras is commutative.
* `ModuleSheafAlgebra.sectionsRing`: the commutative ring `M(U)` of sections over an open `U`.
* `ModuleSheafAlgebra.toQuasiCoherentAlgebra`: the quasi-coherent algebra of a commutative sheaf
  of algebras on a quasi-coherent module; its sections over an affine open `U` are the ring
  `M(U)` (`toQuasiCoherentAlgebra_sections_obj`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

open SheafAlgebraOperations

noncomputable section

namespace ModuleSheafAlgebra

variable {Y : Scheme.{u}} {M : Y.Modules} (S : ModuleSheafAlgebra (R := Y.sheaf) M)

/-- The multiplication of a sheaf of `𝒪_Y`-algebras is commutative. -/
def IsCommutative : Prop :=
  ∀ (U : Y.Opensᵒᵖ) (a b : M.val.obj U), S.mul.app U a b = S.mul.app U b a

variable {S} (hS : S.IsCommutative)

/-- The commutative ring structure on the sections `M(U)` of a commutative sheaf of algebras. -/
@[instance_reducible]
def sectionsCommRing (U : Y.Opens) : CommRing Γ(M, U) :=
  { (inferInstance : AddCommGroup Γ(M, U)) with
    mul := fun a b => S.mul.app (op U) a b
    one := S.one (op U)
    left_distrib := fun a b c => map_add (S.mul.app (op U) a) b c
    right_distrib := fun a b c => LinearMap.congr_fun ((S.mul.app (op U)).map_add a b) c
    zero_mul := fun a => LinearMap.congr_fun (S.mul.app (op U)).map_zero a
    mul_zero := fun a => map_zero _
    mul_assoc := S.mul_assoc (op U)
    one_mul := S.one_mul (op U)
    mul_one := S.mul_one (op U)
    mul_comm := hS (op U) }

-- `hS` only tags the type, so that the commutative ring instance below can use it.
set_option linter.unusedVariables false in
/-- The sections `Γ(M, U)`, with the commutative ring structure of the sheaf of algebras. -/
@[nolint unusedArguments]
def SectionsType (hS : S.IsCommutative) (U : Y.Opens) : Type u := Γ(M, U)

instance (U : Y.Opens) : CommRing (SectionsType hS U) := sectionsCommRing hS U

/-- The commutative ring `M(U)` of sections of a commutative sheaf of algebras over an open `U`. -/
abbrev sectionsRing (U : Y.Opens) : CommRingCat.{u} := CommRingCat.of (SectionsType hS U)

/-- An element of `Γ(M, U)` as an element of the ring `M(U)`. -/
def toSectionsRing {U : Y.Opens} (a : Γ(M, U)) : sectionsRing hS U := a

/-- An element of the ring `M(U)` as an element of `Γ(M, U)`. -/
def ofSectionsRing {U : Y.Opens} (a : sectionsRing hS U) : Γ(M, U) := a

variable (S) in
/-- The unit section `1 ∈ Γ(M, U)`. -/
def oneSection (U : Y.Opens) : Γ(M, U) := S.one (op U)

lemma toSectionsRing_mul {U : Y.Opens} (a b : Γ(M, U)) :
    toSectionsRing hS a * toSectionsRing hS b = toSectionsRing hS (S.mul.app (op U) a b) := rfl

lemma toSectionsRing_one {U : Y.Opens} :
    (1 : sectionsRing hS U) = toSectionsRing hS (S.one (op U)) := rfl

lemma toSectionsRing_sub {U : Y.Opens} (a b : Γ(M, U)) :
    toSectionsRing hS a - toSectionsRing hS b = toSectionsRing hS (a - b) := rfl

@[simp] lemma ofSectionsRing_toSectionsRing {U : Y.Opens} (a : Γ(M, U)) :
    ofSectionsRing hS (toSectionsRing hS a) = a := rfl

@[simp] lemma toSectionsRing_ofSectionsRing {U : Y.Opens} (a : sectionsRing hS U) :
    toSectionsRing hS (ofSectionsRing hS a) = a := rfl

/-- Restriction of sections is a ring homomorphism. -/
def sectionsRestrict {U V : Y.Opens} (i : V ⟶ U) : sectionsRing hS U ⟶ sectionsRing hS V :=
  CommRingCat.ofHom (show sectionsRing hS U →+* sectionsRing hS V from
    { toFun := fun a => toSectionsRing hS (M.presheaf.map i.op (ofSectionsRing hS a))
      map_one' := S.map_one i.op
      map_mul' := S.mul.naturality i.op
      map_zero' := map_zero (M.presheaf.map i.op).hom
      map_add' := map_add (M.presheaf.map i.op).hom })

lemma sectionsRestrict_apply {U V : Y.Opens} (i : V ⟶ U) (a : Γ(M, U)) :
    sectionsRestrict hS i (toSectionsRing hS a) = toSectionsRing hS (M.presheaf.map i.op a) := rfl

open Scheme.AffineZariskiSite in
/-- The rings of sections `M(U)` over the affine opens `U` of `Y`. -/
def sectionsFunctor : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := sectionsRing hS ((toOpensFunctor Y).obj U.unop)
  map i := sectionsRestrict hS ((toOpensFunctor Y).map i.unop)
  map_id U := by
    ext a
    change toSectionsRing hS (M.presheaf.map ((toOpensFunctor Y).map (𝟙 U.unop)).op
      (ofSectionsRing hS a)) = a
    simp
  map_comp i j := by
    ext a
    change toSectionsRing hS (M.presheaf.map ((toOpensFunctor Y).map (j.unop ≫ i.unop)).op
      (ofSectionsRing hS a)) = toSectionsRing hS (M.presheaf.map ((toOpensFunctor Y).map j.unop).op
        (M.presheaf.map ((toOpensFunctor Y).map i.unop).op (ofSectionsRing hS a)))
    simp

omit hS in
lemma mul_smul_left (U : Y.Opens) (r : Γ(Y, U)) (a b : Γ(M, U)) :
    S.mul.app (op U) (HSMul.hSMul (α := Γ(Y, U)) (β := Γ(M, U)) r a) b =
      HSMul.hSMul (α := Γ(Y, U)) (β := Γ(M, U)) r (S.mul.app (op U) a b) :=
  (S.mul.app (op U)).map_smul₂ r a b

omit hS in
lemma mul_smul_right (U : Y.Opens) (r : Γ(Y, U)) (a b : Γ(M, U)) :
    S.mul.app (op U) a (HSMul.hSMul (α := Γ(Y, U)) (β := Γ(M, U)) r b) =
      HSMul.hSMul (α := Γ(Y, U)) (β := Γ(M, U)) r (S.mul.app (op U) a b) :=
  (S.mul.app (op U) a).map_smul r b

/-- The structure map `r ↦ r • 1` from `Γ(U, 𝒪_Y)` to the sections over an open `U`. -/
def unitRingHom (U : Y.Opens) : Γ(Y, U) ⟶ sectionsRing hS U :=
  CommRingCat.ofHom (show Γ(Y, U) →+* sectionsRing hS U from
    { toFun := fun r => toSectionsRing hS (r • oneSection S U)
      map_one' := by
        change (1 : Γ(Y, U)) • oneSection S U = S.one (op U)
        exact one_smul _ _
      map_mul' := fun r s => by
        change (r * s) • oneSection S U =
          S.mul.app (op U) (r • oneSection S U) (s • oneSection S U)
        rw [mul_smul_left, mul_smul_right, mul_smul]
        exact congrArg (fun t => r • s • t) (S.one_mul (op U) (S.one (op U))).symm
      map_zero' := by
        change (0 : Γ(Y, U)) • oneSection S U = 0
        exact zero_smul _ _
      map_add' := fun r s => by
        change (r + s) • oneSection S U = r • oneSection S U + s • oneSection S U
        exact add_smul _ _ _ })

lemma unitRingHom_apply (U : Y.Opens) (r : Γ(Y, U)) :
    unitRingHom hS U r = toSectionsRing hS (r • oneSection S U) := rfl

lemma unitRingHom_mul (U : Y.Opens) (r : Γ(Y, U)) (a : Γ(M, U)) :
    unitRingHom hS U r * toSectionsRing hS a = toSectionsRing hS (r • a) := by
  change S.mul.app (op U) (r • oneSection S U) a = r • a
  rw [mul_smul_left]
  exact congrArg (r • ·) (S.one_mul (op U) a)

lemma unitRingHom_naturality {U V : Y.Opens} (i : V ⟶ U) (r : Γ(Y, U)) :
    sectionsRestrict hS i (unitRingHom hS U r) = unitRingHom hS V (Y.presheaf.map i.op r) := by
  change M.presheaf.map i.op (r • oneSection S U) =
    Y.presheaf.map i.op r • oneSection S V
  rw [Scheme.Modules.map_smul]
  congr 1
  exact S.map_one i.op

open Scheme.AffineZariskiSite in
/-- The `𝒪_Y`-algebra structure `Γ(U, 𝒪_Y) → M(U)` over the affine opens `U` of `Y`. -/
def sectionsStructureMap : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ sectionsFunctor hS where
  app U := unitRingHom hS ((toOpensFunctor Y).obj U.unop)
  naturality U V i := by
    ext r
    exact (unitRingHom_naturality hS _ r).symm

variable [M.IsQuasicoherent]

open Scheme.AffineZariskiSite in
/-- **Sections over `D(r)` are the localization at `r`** (Hartshorne's Lemma II.5.3 for the
quasi-coherent module `M`): the rings of sections of a commutative sheaf of algebras on a
quasi-coherent module satisfy `M(D(r)) = M(U)_r` for every affine open `U` and `r ∈ Γ(U, 𝒪_Y)`. -/
theorem coequifibered_structureMap : NatTrans.Coequifibered (sectionsStructureMap hS) := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U f => ?_
  let ρ : Y.basicOpen f ⟶ U.toOpens := homOfLE (Y.basicOpen_le f)
  let : Algebra (sectionsRing hS U.toOpens) (sectionsRing hS (Y.basicOpen f)) :=
    (sectionsRestrict hS ρ).hom.toAlgebra
  show IsLocalization.Away (unitRingHom hS U.toOpens f) (sectionsRing hS (Y.basicOpen f))
  have halg : ∀ a, algebraMap (sectionsRing hS U.toOpens) (sectionsRing hS (Y.basicOpen f)) a =
      sectionsRestrict hS ρ a := fun _ => rfl
  refine ⟨?_, fun z => ?_, fun {x y} h => ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow, halg]
    refine IsUnit.pow n ?_
    rw [show sectionsRestrict hS ρ (unitRingHom hS U.toOpens f) =
      unitRingHom hS _ (Y.presheaf.map ρ.op f) from unitRingHom_naturality hS ρ f]
    exact IsUnit.map (unitRingHom hS _).hom (Y.toRingedSpace.isUnit_res_basicOpen f)
  · obtain ⟨n, t', ht'⟩ :=
      exists_pow_smul_extension_of_isAffineOpen M U.2 f (ofSectionsRing hS z)
    refine ⟨⟨toSectionsRing hS t', ⟨unitRingHom hS U.toOpens f ^ n, n, rfl⟩⟩, ?_⟩
    change z * algebraMap _ _ (unitRingHom hS U.toOpens f ^ n) =
      algebraMap _ _ (toSectionsRing hS t')
    rw [halg, halg, ← map_pow, unitRingHom_naturality, sectionsRestrict_apply, mul_comm,
      ← toSectionsRing_ofSectionsRing hS z, unitRingHom_mul, map_pow]
    exact congrArg (toSectionsRing hS) ht'.symm
  · rw [halg, halg] at h
    have hxy : M.presheaf.map ρ.op (ofSectionsRing hS x - ofSectionsRing hS y) = 0 :=
      (map_sub (M.presheaf.map ρ.op).hom _ _).trans (sub_eq_zero.mpr h)
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen M U.2 f _ hxy
    refine ⟨⟨unitRingHom hS U.toOpens f ^ n, n, rfl⟩, ?_⟩
    change unitRingHom hS U.toOpens f ^ n * x = unitRingHom hS U.toOpens f ^ n * y
    rw [← map_pow, ← sub_eq_zero, ← mul_sub, ← toSectionsRing_ofSectionsRing hS x,
      ← toSectionsRing_ofSectionsRing hS y, toSectionsRing_sub, unitRingHom_mul]
    exact congrArg (toSectionsRing hS) hn

/-- **A commutative sheaf of algebras on a quasi-coherent module is a quasi-coherent algebra**:
the rings of sections over the affine opens of `Y`, with the structure maps `r ↦ r • 1`. -/
def toQuasiCoherentAlgebra : QuasiCoherentAlgebra Y :=
  ⟨Under.mk (sectionsStructureMap hS), coequifibered_structureMap hS⟩

lemma toQuasiCoherentAlgebra_sections_obj (U : Y.AffineZariskiSite) :
    (toQuasiCoherentAlgebra hS).sections.obj (op U) = sectionsRing hS U.toOpens := rfl

omit [M.IsQuasicoherent] in
lemma sectionsRestrict_comp {U V W : Y.Opens} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U) :
    sectionsRestrict hS i ≫ sectionsRestrict hS j = sectionsRestrict hS k := by
  ext a
  change M.presheaf.map j.op (M.presheaf.map i.op (ofSectionsRing hS a)) =
    M.presheaf.map k.op (ofSectionsRing hS a)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (j ≫ i) k]

/-- For affine opens `U ⊆ V`, the restriction homomorphism of the quasi-coherent algebra is the
restriction of sections. -/
lemma toQuasiCoherentAlgebra_restriction {U V : Y.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens) :
    (toQuasiCoherentAlgebra hS).restriction h = sectionsRestrict hS (homOfLE h) :=
  ((toQuasiCoherentAlgebra hS).eq_restriction h _ fun _ _ _ => sectionsRestrict_comp hS _ _ _).symm

end ModuleSheafAlgebra

end

end Hartshorne
