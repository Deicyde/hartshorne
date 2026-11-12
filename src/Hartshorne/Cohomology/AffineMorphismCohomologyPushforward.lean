/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AffineCoverComparison
import Hartshorne.Scheme.QcqsPushforwardQuasicoherent

/-!
# Cohomology under an affine morphism

Hartshorne, *Algebraic Geometry*, III, Exercise 4.1 (p. 222).

Let `f : X ⟶ Y` be an affine morphism of Noetherian separated schemes and let `F` be a
quasi-coherent `𝒪_X`-module. Then `H^i(X, F) ≅ H^i(Y, f_* F)` for every `i`
(`Hartshorne.sheafCohomologyIsoPushforwardOfIsAffineHom`), naturally in `F`
(`Hartshorne.sheafCohomologyIsoPushforwardOfIsAffineHom_hom_naturality`).

## Proof

We follow the route of the exercise. Let `U` be an open affine cover of `Y`. Since `f` is affine,
`f⁻¹U` is an open affine cover of `X`. By the definition of the direct image, the ordered Čech
complexes `C^•(U, f_* F)` and `C^•(f⁻¹U, F)` agree termwise: the sections of `f_* F` over
`U_{i₀} ∩ ⋯ ∩ U_{i_p}` are the sections of `F` over its inverse image
`f⁻¹U_{i₀} ∩ ⋯ ∩ f⁻¹U_{i_p}` (`Hartshorne.AffineMorphismCohomologyPushforward.cechComplexIso`,
stated for any continuous map and any abelian sheaf). The direct image `f_* F` is quasi-coherent
(Hartshorne II, Proposition 5.8(c)), `X` is separated because affine morphisms are separated, and
Theorem III.4.5 identifies both Čech cohomologies with sheaf cohomology.

As the cover of `Y` we take all of its affine opens; Theorem III.4.5 as formalized does not need
the cover to be finite.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Hartshorne

namespace AffineMorphismCohomologyPushforward

section Topological

variable {X Y : TopCat.{u}} (f : X ⟶ Y) {ι : Type u} [LinearOrder ι] (U : ι → Opens Y)

/-- The inverse image of an ordered Čech intersection is the ordered Čech intersection of the
inverse images. -/
theorem map_orderedCechIntersection {p : ℕ} (a : OrderedCechIndex ι p) :
    (Opens.map f).obj (orderedCechIntersection U a) =
      orderedCechIntersection (fun i => (Opens.map f).obj (U i)) a := by
  ext x
  simp [orderedCechIntersection, Opens.coe_iInf]

private theorem restrict_comm (H : X.Presheaf AddCommGrpCat.{u}) {A B B' C : (Opens X)ᵒᵖ}
    (i : A ⟶ B) (j : B ⟶ C) (i' : A ⟶ B') (j' : B' ⟶ C) (x : H.obj A) :
    H.map j (H.map i x) = H.map j' (H.map i' x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← H.map_comp, ← H.map_comp,
    show i ≫ j = i' ≫ j' from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

private theorem restrict_restrict_self (H : X.Presheaf AddCommGrpCat.{u}) {A B : (Opens X)ᵒᵖ}
    (i : A ⟶ B) (j : B ⟶ A) (x : H.obj A) : H.map j (H.map i x) = x := by
  rw [← ConcreteCategory.comp_apply, ← H.map_comp,
    show i ≫ j = 𝟙 A from Quiver.Hom.unop_inj (Subsingleton.elim _ _), H.map_id]
  rfl

/-- Degreewise, the ordered Čech cochains of a direct image `f_* H` on the cover `U` are the
ordered Čech cochains of `H` on the cover `f⁻¹U`. -/
def cochainsIso (H : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    orderedCechCochains U ((TopCat.Sheaf.pushforward _ f).obj H) p ≅
      orderedCechCochains (fun i => (Opens.map f).obj (U i)) H p where
  hom := AddCommGrpCat.ofHom
    { toFun := fun s a => H.presheaf.map
        (homOfLE (map_orderedCechIntersection f U a).ge).op (s a)
      map_zero' := by
        ext a
        exact map_zero _
      map_add' := by
        intro s t
        ext a
        exact map_add _ _ _ }
  inv := AddCommGrpCat.ofHom
    { toFun := fun s a => H.presheaf.map
        (homOfLE (map_orderedCechIntersection f U a).le).op (s a)
      map_zero' := by
        ext a
        exact map_zero _
      map_add' := by
        intro s t
        ext a
        exact map_add _ _ _ }
  hom_inv_id := by
    ext s
    funext a
    exact restrict_restrict_self H.presheaf _ _ (s a)
  inv_hom_id := by
    ext s
    funext a
    exact restrict_restrict_self H.presheaf _ _ (s a)

/-- **The two Čech complexes agree.** The ordered Čech complex of a direct image `f_* H` on an open
cover `U` of `Y` is isomorphic to the ordered Čech complex of `H` on the cover `f⁻¹U` of `X`; in
each degree the isomorphism is the identity on sections, up to the identification of
`f⁻¹(U_{i₀} ∩ ⋯ ∩ U_{i_p})` with `f⁻¹U_{i₀} ∩ ⋯ ∩ f⁻¹U_{i_p}`. -/
def cechComplexIso (H : X.Sheaf AddCommGrpCat.{u}) :
    orderedCechComplex U ((TopCat.Sheaf.pushforward _ f).obj H) ≅
      orderedCechComplex (fun i => (Opens.map f).obj (U i)) H :=
  HomologicalComplex.Hom.isoOfComponents (fun p => cochainsIso f U H p) (by
    rintro p _ rfl
    simp only [orderedCechComplex, CochainComplex.of_d, orderedCechDifferential,
      Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    ext s
    funext a
    exact restrict_comm H.presheaf _ _ _ _ (s (a.remove q)))

/-- The isomorphism `cechComplexIso` is natural in the sheaf. -/
def cechComplexNatIso :
    TopCat.Sheaf.pushforward _ f ⋙ orderedCechComplexFunctor U ≅
      orderedCechComplexFunctor (fun i => (Opens.map f).obj (U i)) :=
  NatIso.ofComponents (fun H => cechComplexIso f U H) (by
    intro H₁ H₂ g
    ext p : 2
    ext s
    funext a
    exact (ConcreteCategory.congr_hom (g.hom.naturality _) (s a)).symm)

end Topological

open AlgebraicGeometry

/-- The abelian sheaf underlying the direct image of a sheaf of modules is the direct image of
the underlying abelian sheaf. -/
def toSheafPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pushforward f ⋙ SheafOfModules.toSheaf Y.ringCatSheaf ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙ TopCat.Sheaf.pushforward _ f.base :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end AffineMorphismCohomologyPushforward

open AffineMorphismCohomologyPushforward AlgebraicGeometry

/-- The isomorphism `Ȟ^p(f⁻¹U, F) ≅ Ȟ^p(U, f_* F)` of ordered Čech cohomology groups, for a
morphism of schemes `f : X ⟶ Y`, an open cover `U` of `Y`, and an `𝒪_X`-module `F`. -/
def orderedCechCohomologyPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u}
    [LinearOrder ι] (U : ι → Y.Opens) (p : ℕ) (F : X.Modules) :
    (orderedCechCohomologyFunctor (fun i => f ⁻¹ᵁ U i) p).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ≅
      (orderedCechCohomologyFunctor U p).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj F)) :=
  (HomologicalComplex.homologyFunctor _ _ p).mapIso
      ((cechComplexNatIso f.base U).app ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)).symm ≪≫
    (orderedCechCohomologyFunctor U p).mapIso
      ((toSheafPushforwardIso f).app F).symm

/-- The inverse images of an open cover of `Y` form an open cover of `X`. -/
theorem isOpenCover_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} {U : ι → Y.Opens}
    (hU : IsOpenCover U) : IsOpenCover (fun i => f ⁻¹ᵁ U i) := by
  change (⨆ i, f ⁻¹ᵁ U i) = ⊤
  rw [← Scheme.Hom.preimage_iSup, hU.iSup_eq_top, Scheme.Hom.preimage_top]

/-- The isomorphism `orderedCechCohomologyPushforwardIso` is natural in the module. -/
theorem orderedCechCohomologyPushforwardIso_hom_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (p : ℕ) {F G : X.Modules} (φ : F ⟶ G) :
    (orderedCechCohomologyFunctor (fun i => f ⁻¹ᵁ U i) p).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) ≫
      (orderedCechCohomologyPushforwardIso f U p G).hom =
    (orderedCechCohomologyPushforwardIso f U p F).hom ≫
      (orderedCechCohomologyFunctor U p).map
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map ((Scheme.Modules.pushforward f).map φ)) := by
  have h₁ : (orderedCechComplexFunctor (fun i => f ⁻¹ᵁ U i)).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) ≫
      (cechComplexNatIso f.base U).inv.app ((SheafOfModules.toSheaf X.ringCatSheaf).obj G) =
    (cechComplexNatIso f.base U).inv.app ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ≫
      (orderedCechComplexFunctor U).map ((TopCat.Sheaf.pushforward _ f.base).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)) :=
    (cechComplexNatIso f.base U).inv.naturality _
  have h₂ : (TopCat.Sheaf.pushforward _ f.base).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) ≫ (toSheafPushforwardIso f).inv.app G =
      (toSheafPushforwardIso f).inv.app F ≫
        (SheafOfModules.toSheaf Y.ringCatSheaf).map ((Scheme.Modules.pushforward f).map φ) :=
    (toSheafPushforwardIso f).inv.naturality φ
  show (HomologicalComplex.homologyFunctor _ _ p).map _ ≫
      ((HomologicalComplex.homologyFunctor _ _ p).map _ ≫
        (HomologicalComplex.homologyFunctor _ _ p).map _) =
    ((HomologicalComplex.homologyFunctor _ _ p).map _ ≫
        (HomologicalComplex.homologyFunctor _ _ p).map _) ≫
      (HomologicalComplex.homologyFunctor _ _ p).map _
  simp only [← Functor.map_comp]
  congr 1

/-- The source of an affine morphism to a separated scheme is separated, since affine morphisms
are separated. -/
theorem scheme_isSeparated_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [Y.IsSeparated] : X.IsSeparated :=
  haveI : IsSeparated f := IsSeparated.of_isAffineHom f
  ⟨by rw [← terminal.comp_from f]; infer_instance⟩

/-- **Hartshorne III, Exercise 4.1**, for a given open affine cover `U` of `Y`: the isomorphism
`H^p(X, F) ≅ Ȟ^p(f⁻¹U, F) = Ȟ^p(U, f_* F) ≅ H^p(Y, f_* F)`. -/
def sheafCohomologyIsoPushforwardOfAffineCover {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [IsNoetherian X] [IsNoetherian Y] [Y.IsSeparated] {ι : Type u} [LinearOrder ι]
    (U : ι → Y.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) (F : X.Modules)
    [F.IsQuasicoherent] (p : ℕ) :
    (sheafCohomology X.toTopCat p).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ≅
      (sheafCohomology Y.toTopCat p).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj F)) :=
  haveI : X.IsSeparated := scheme_isSeparated_of_isAffineHom f
  haveI : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward f (Or.inl ‹_›) F
  (cechCohomologyIsoOfIsQuasicoherent (fun i => f ⁻¹ᵁ U i) (isOpenCover_preimage f hU)
      (fun i => IsAffineHom.isAffine_preimage _ (hUa i)) p F).symm ≪≫
    orderedCechCohomologyPushforwardIso f U p F ≪≫
      cechCohomologyIsoOfIsQuasicoherent U hU hUa p ((Scheme.Modules.pushforward f).obj F)

/-- A ladder of three commutative squares, the first one with invertible vertical maps. -/
private theorem naturality_aux {C : Type*} [Category C] {A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : C}
    (α₁ : A₁ ≅ B₁) (α₂ : A₂ ≅ B₂) (μ₁ : A₁ ⟶ C₁) (μ₂ : A₂ ⟶ C₂)
    (β₁ : C₁ ⟶ D₁) (β₂ : C₂ ⟶ D₂) {a : A₁ ⟶ A₂} {b : B₁ ⟶ B₂} {c : C₁ ⟶ C₂} {d : D₁ ⟶ D₂}
    (h₁ : a ≫ α₂.hom = α₁.hom ≫ b) (h₂ : a ≫ μ₂ = μ₁ ≫ c) (h₃ : c ≫ β₂ = β₁ ≫ d) :
    b ≫ α₂.inv ≫ μ₂ ≫ β₂ = α₁.inv ≫ μ₁ ≫ β₁ ≫ d := by
  rw [Iso.eq_inv_comp, ← reassoc_of% h₁, Iso.hom_inv_id_assoc, reassoc_of% h₂, h₃]

/-- The isomorphism `sheafCohomologyIsoPushforwardOfAffineCover` is natural in `F`. -/
theorem sheafCohomologyIsoPushforwardOfAffineCover_hom_naturality {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] [IsNoetherian X] [IsNoetherian Y] [Y.IsSeparated] {ι : Type u}
    [LinearOrder ι] (U : ι → Y.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) (p : ℕ) :
    (sheafCohomology X.toTopCat p).map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) ≫
        (sheafCohomologyIsoPushforwardOfAffineCover f U hU hUa G p).hom =
      (sheafCohomologyIsoPushforwardOfAffineCover f U hU hUa F p).hom ≫
        (sheafCohomology Y.toTopCat p).map
          ((SheafOfModules.toSheaf Y.ringCatSheaf).map ((Scheme.Modules.pushforward f).map φ)) := by
  have : X.IsSeparated := scheme_isSeparated_of_isAffineHom f
  have : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward f (Or.inl ‹_›) F
  have : ((Scheme.Modules.pushforward f).obj G).IsQuasicoherent :=
    isQuasicoherent_pushforward f (Or.inl ‹_›) G
  have hfU := isOpenCover_preimage f hU
  have hfUa : ∀ i, IsAffineOpen (f ⁻¹ᵁ U i) := fun i => IsAffineHom.isAffine_preimage _ (hUa i)
  exact naturality_aux
    (cechCohomologyIsoOfIsQuasicoherent (fun i => f ⁻¹ᵁ U i) hfU hfUa p F)
    (cechCohomologyIsoOfIsQuasicoherent (fun i => f ⁻¹ᵁ U i) hfU hfUa p G)
    (orderedCechCohomologyPushforwardIso f U p F).hom
    (orderedCechCohomologyPushforwardIso f U p G).hom
    (cechCohomologyIsoOfIsQuasicoherent U hU hUa p ((Scheme.Modules.pushforward f).obj F)).hom
    (cechCohomologyIsoOfIsQuasicoherent U hU hUa p ((Scheme.Modules.pushforward f).obj G)).hom
    ((cechToSheafCohomology _ hfU p).naturality _)
    (orderedCechCohomologyPushforwardIso_hom_naturality f U p φ)
    ((cechToSheafCohomology U hU p).naturality _)

/-- The linear order on the affine opens of `Y` used to form ordered Čech complexes on the cover
of `Y` by all of its affine opens. -/
@[instance_reducible]
def affineOpensLinearOrder (Y : Scheme.{u}) : LinearOrder Y.affineOpens :=
  IsWellOrder.linearOrder WellOrderingRel

/-- **Hartshorne III, Exercise 4.1.** Let `f : X ⟶ Y` be an affine morphism of Noetherian
schemes with `Y` separated (then `X` is separated too, affine morphisms being separated), and let
`F` be a quasi-coherent `𝒪_X`-module. Then for every `p` there is an isomorphism
`H^p(X, F) ≅ H^p(Y, f_* F)` of sheaf cohomology groups of the underlying abelian sheaves. It is
obtained by comparing both sides with Čech cohomology on the open affine cover of `Y` by all of
its affine opens and on its inverse image (Theorem III.4.5); it is natural in `F`
(`Hartshorne.sheafCohomologyIsoPushforwardOfIsAffineHom_hom_naturality`). -/
def sheafCohomologyIsoPushforwardOfIsAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [IsNoetherian X] [IsNoetherian Y] [Y.IsSeparated] (F : X.Modules) [F.IsQuasicoherent]
    (p : ℕ) :
    (sheafCohomology X.toTopCat p).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ≅
      (sheafCohomology Y.toTopCat p).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj F)) :=
  letI := affineOpensLinearOrder Y
  sheafCohomologyIsoPushforwardOfAffineCover f (fun V : Y.affineOpens => (V : Y.Opens))
    (iSup_affineOpens_eq_top Y) (fun V => V.2) F p

/-- **Hartshorne III, Exercise 4.1**, naturality: the isomorphisms
`sheafCohomologyIsoPushforwardOfIsAffineHom` are natural in the quasi-coherent module `F`. -/
theorem sheafCohomologyIsoPushforwardOfIsAffineHom_hom_naturality {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] [IsNoetherian X] [IsNoetherian Y] [Y.IsSeparated]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) (p : ℕ) :
    (sheafCohomology X.toTopCat p).map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) ≫
        (sheafCohomologyIsoPushforwardOfIsAffineHom f G p).hom =
      (sheafCohomologyIsoPushforwardOfIsAffineHom f F p).hom ≫
        (sheafCohomology Y.toTopCat p).map
          ((SheafOfModules.toSheaf Y.ringCatSheaf).map ((Scheme.Modules.pushforward f).map φ)) :=
  letI := affineOpensLinearOrder Y
  sheafCohomologyIsoPushforwardOfAffineCover_hom_naturality f _ (iSup_affineOpens_eq_top Y)
    (fun V => V.2) φ p

end Hartshorne
