/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeProjLineBundleTwist
import Hartshorne.Scheme.VeryAmpleTensorProduct
import Hartshorne.Scheme.ProjectiveBundleTwist

/-!
# Frames for the twisting sheaf of `Proj_X (S · L)`

Hartshorne, *Algebraic Geometry*, II.7, Lemma 7.9 (p. 161), the formula for `𝒪(1)`.

## Gluing an isomorphism from locally matching frames

`Hartshorne.nonempty_iso_of_isTrivializingSection_local`: if two modules `A`, `B` on a scheme
have trivializing sections `a i`, `b i` on the members `W i` of an open cover, and near every point
of each overlap `W i ∩ W j` the two families have the same transition function, then `A ≅ B`.
This is `Hartshorne.Ringed.nonempty_iso_of_frames`, where the transition functions are only
compared locally: the transition function of `a j` relative to `a i` on `W i ∩ W j` is the unique
coefficient, so it agrees with that of the `b`'s if it does so locally.
-/

universe u


noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

open scoped TensorProduct

namespace Hartshorne

namespace IsTrivializingSection

variable {X : Scheme.{u}} {L : X.Modules} {U : X.Opens} {e : Γ(L, U)}

theorem exists_eq_smul_section (he : IsTrivializingSection L U e) (x : Γ(L, U)) :
    ∃ c : Γ(X, U), x = c • e := by
  obtain ⟨c, hc⟩ := (he U le_rfl).2 x
  refine ⟨c, hc.symm.trans ?_⟩
  change c • L.presheaf.map (𝟙 _) e = c • e
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem smul_left_injective (he : IsTrivializingSection L U e) {c d : Γ(X, U)}
    (h : c • e = d • e) : c = d := by
  refine (he U le_rfl).1 ?_
  change c • L.presheaf.map (𝟙 _) e = d • L.presheaf.map (𝟙 _) e
  rw [CategoryTheory.Functor.map_id]
  exact h

end IsTrivializingSection

/-- **Modules with locally matching trivializing sections are isomorphic.** If `A` and `B` have
trivializing sections `a i`, `b i` on the members `W i` of an open cover, and near every point of
each overlap `W i ∩ W j` there is a function `c` with `a j = c • a i` and `b j = c • b i`, then
`A ≅ B`. -/
theorem nonempty_iso_of_isTrivializingSection_local {Y : Scheme.{u}} {ι : Type u}
    {A B : Y.Modules} (W : ι → Y.Opens) (hW : ⊤ ≤ iSup W) (a : ∀ i, Γ(A, W i))
    (b : ∀ i, Γ(B, W i)) (ha : ∀ i, IsTrivializingSection A (W i) (a i))
    (hb : ∀ i, IsTrivializingSection B (W i) (b i))
    (hloc : ∀ i j, ∀ y ∈ W i ⊓ W j, ∃ (O : Y.Opens) (hO : O ≤ W i ⊓ W j), y ∈ O ∧
      ∃ c : Γ(Y, O),
        A.presheaf.map (homOfLE (hO.trans inf_le_right)).op (a j) =
            c • A.presheaf.map (homOfLE (hO.trans inf_le_left)).op (a i) ∧
          B.presheaf.map (homOfLE (hO.trans inf_le_right)).op (b j) =
            c • B.presheaf.map (homOfLE (hO.trans inf_le_left)).op (b i)) :
    Nonempty (A ≅ B) := by
  have σ : PUnit.{u + 1} ≃ ULift.{u} (Fin 1) := Equiv.ofUnique _ _
  refine Ringed.nonempty_iso_of_frames (R := Y.sheaf) W hW a b
    (fun i => (isLocalFrame_of_isTrivializingSection (ha i)).reindex σ)
    (fun i => (isLocalFrame_of_isTrivializingSection (hb i)).reindex σ) fun i j => ?_
  obtain ⟨c, hc⟩ := ((ha i).restrict (inf_le_left : W i ⊓ W j ≤ W i)).exists_eq_smul_section
    (A.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (a j))
  obtain ⟨d, hd⟩ := ((hb i).restrict (inf_le_left : W i ⊓ W j ≤ W i)).exists_eq_smul_section
    (B.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (b j))
  refine ⟨c, hc, ?_⟩
  suffices hcd : c = d by rw [hcd]; exact hd
  choose O hO hyO e he using fun y : ↥(W i ⊓ W j) => hloc i j y.1 y.2
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf O (W i ⊓ W j) (fun y => homOfLE (hO y))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyO _⟩) c d fun y => ?_
  have key : ∀ (F : Y.Modules) (s : ∀ i, Γ(F, W i)) (hs : IsTrivializingSection F (W i) (s i))
      (c' : Γ(Y, W i ⊓ W j))
      (hc' : F.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (s j) =
        c' • F.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (s i))
      (he' : F.presheaf.map (homOfLE ((hO y).trans inf_le_right)).op (s j) =
        e y • F.presheaf.map (homOfLE ((hO y).trans inf_le_left)).op (s i)),
      Y.presheaf.map (homOfLE (hO y)).op c' = e y := by
    intro F s hs c' hc' he'
    refine (hs.restrict ((hO y).trans inf_le_left)).smul_left_injective ?_
    rw [← he', ← Scheme.Modules.map_map_homOfLE F inf_le_left (hO y),
      ← Scheme.Modules.map_map_homOfLE F inf_le_right (hO y), hc', Scheme.Modules.map_smul]
  exact (key A a (ha i) c hc (he y).1).trans (key B b (hb i) d hd (he y).2).symm

namespace QuasiCoherentGradedAlgebra

/-! ### Degree-one sections over the affine pieces

To keep the kernel away from the construction of the relative twisting sheaf, the following is
stated for any module `M` on `Proj_X A` with isomorphisms `α U : M|_{Proj A(U)} ≅ 𝒪_{Proj A(U)}(1)`
(for `M = 𝒪_{Proj_X A}(1)`, those of `relTwistingSheafRestrictIso`). -/

theorem modules_iso_hom_inv_app {Z : Scheme.{u}} {M N : Z.Modules} (α : M ≅ N) (W : Z.Opens)
    (x : Γ(N, W)) : α.hom.app W (α.inv.app W x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, α.inv_hom_id,
    Scheme.Modules.Hom.id_app]
  rfl

variable {X : Scheme.{u}} {A : QuasiCoherentGradedAlgebra X} (M : A.relProj.Modules)
  (α : ∀ U : X.AffineZariskiSite, M.restrict (A.projι U) ≅ A.twistingSheaf 1 U)

/-- An element `x ∈ A(U)₁` as a section of `M` over the affine piece `Proj A(U)`: the global
section `x` of `𝒪_{Proj A(U)}(1)`. -/
def pieceDegreeOneSection (U : X.AffineZariskiSite) {x : A.obj.obj (.op U)}
    (hx : x ∈ A.grading U 1) : Γ(M, A.projι U ''ᵁ ⊤) :=
  (M.restrictAppIso (A.projι U) ⊤).hom
    ((α U).inv.app ⊤ (ProjTwistingSheaf.degreeOneSection ⟨x, hx⟩))

variable {M}

theorem hom_app_pieceDegreeOneSection {U : X.AffineZariskiSite}
    {x : A.obj.obj (.op U)} (hx : x ∈ A.grading U 1) (W : (Proj (A.grading U)).Opens) :
    (α U).hom.app W ((M.restrictAppIso (A.projι U) W).inv (M.presheaf.map
        (homOfLE (Scheme.Hom.image_mono _ (le_top : W ≤ ⊤))).op (pieceDegreeOneSection M α U hx))) =
      (A.twistingSheaf 1 U).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (ProjTwistingSheaf.degreeOneSection ⟨x, hx⟩) := by
  rw [pieceDegreeOneSection, ← Scheme.Modules.map_restrictAppIso_hom_apply (f := A.projι U) (M := M)
      (hUV := (homOfLE (le_top : W ≤ ⊤)).op), Iso.hom_inv_id_apply, hom_app_map]
  exact congrArg _ (modules_iso_hom_inv_app _ _ _)

/-- The section `x` of `M` trivializes it over the image of `D₊(x) ⊆ Proj A(U)`. -/
theorem isTrivializingSection_pieceDegreeOneSection {U : X.AffineZariskiSite}
    {x : A.obj.obj (.op U)} (hx : x ∈ A.grading U 1) :
    IsTrivializingSection M (A.projι U ''ᵁ Proj.basicOpen (A.grading U) x)
      (M.presheaf.map (homOfLE (Scheme.Hom.image_mono _
        (le_top : Proj.basicOpen (A.grading U) x ≤ ⊤))).op (pieceDegreeOneSection M α U hx)) := by
  have h0 : IsTrivializingSection (A.twistingSheaf 1 U) (Proj.basicOpen (A.grading U) x)
      ((A.twistingSheaf 1 U).presheaf.map (homOfLE le_top).op
        (ProjTwistingSheaf.degreeOneSection ⟨x, hx⟩)) :=
    IsTrivializingSection.of_isLocalFrame (ι := PUnit.{u + 1})
      (ProjTwistingSheaf.isLocalFrame_degreeOneSection hx)
  refine (congrArg (IsTrivializingSection M
    (A.projι U ''ᵁ Proj.basicOpen (A.grading U) x)) ?_).mpr
      ((h0.map_iso (α U).symm).image_of_restrict (A.projι U))
  rw [Iso.symm_hom, hom_app_map (α U).inv (le_top : Proj.basicOpen (A.grading U) x ≤ ⊤),
    Scheme.Modules.map_restrictAppIso_hom_apply]
  rfl

/-- **Transition functions on one piece**: over the image of `D₊(x)`, the section `y` of `M` is
`y/x` times the section `x`, for `x, y ∈ A(U)₁`. -/
theorem pieceDegreeOneSection_eq_smul {U : X.AffineZariskiSite} {x y : A.obj.obj (.op U)}
    (hx : x ∈ A.grading U 1) (hy : y ∈ A.grading U 1) :
    M.presheaf.map (homOfLE (Scheme.Hom.image_mono _
        (le_top : Proj.basicOpen (A.grading U) x ≤ ⊤))).op (pieceDegreeOneSection M α U hy) =
      (((A.projι U).appIso (Proj.basicOpen (A.grading U) x)).inv
          (Proj.awayToSection (A.grading U) x
            (HomogeneousLocalization.Away.mk (A.grading U) hx 1 y (by rwa [smul_eq_mul, mul_one])))
          : Γ(A.relProj, A.projι U ''ᵁ Proj.basicOpen (A.grading U) x)) •
        M.presheaf.map (homOfLE (Scheme.Hom.image_mono _
          (le_top : Proj.basicOpen (A.grading U) x ≤ ⊤))).op (pieceDegreeOneSection M α U hx) := by
  apply ((ConcreteCategory.bijective_of_isIso ((α U).hom.app
    (Proj.basicOpen (A.grading U) x))).comp (ConcreteCategory.bijective_of_isIso
      (M.restrictAppIso (A.projι U) (Proj.basicOpen (A.grading U) x)).inv)).1
  simp only [Function.comp_apply]
  rw [hom_app_pieceDegreeOneSection α hy, Hartshorne.restrictAppIso_inv_smul,
    Scheme.Modules.Hom.app_smul, Iso.inv_hom_id_apply, hom_app_pieceDegreeOneSection α hx]
  exact ProjTwistingSheaf.restrict_degreeOneSection_eq_smul hx hy

variable (M) in
/-- Compatibility of the isomorphisms `α U` with the transition isomorphisms of the twisting
sheaves, in the form of `DirectedModuleGluing.DataTr.ψ_hom_app_top`. -/
def PieceIsosCompatible : Prop :=
  ∀ (U V : X.AffineZariskiSite) (f : V ⟶ U)
    (hle : A.projι U ''ᵁ (Proj.map (A.restrict f) (A.irrelevant_le f) ''ᵁ ⊤) ≤ A.projι V ''ᵁ ⊤)
    (x : Γ(M, A.projι V ''ᵁ ⊤)),
    (α V).hom.app ⊤ ((M.restrictAppIso (A.projι V) ⊤).inv x) =
      (A.twistTransition 1 f).hom.app ⊤
        (((A.twistingSheaf 1 U).restrictAppIso (Proj.map (A.restrict f) (A.irrelevant_le f))
          ⊤).inv ((α U).hom.app _ ((M.restrictAppIso (A.projι U) _).inv
            (M.presheaf.map (homOfLE hle).op x))))

/-- **Restricting degree-one sections**: along `f : V ⟶ U`, the section `x` over the piece over
`U` restricts to the section `x|_V` over the piece over `V`. -/
theorem pieceDegreeOneSection_restrict (hα : PieceIsosCompatible M α) {U V : X.AffineZariskiSite}
    (f : V ⟶ U) {x : A.obj.obj (.op U)} (hx : x ∈ A.grading U 1)
    (hle : A.projι V ''ᵁ ⊤ ≤ A.projι U ''ᵁ ⊤) :
    M.presheaf.map (homOfLE hle).op (pieceDegreeOneSection M α U hx) =
      pieceDegreeOneSection M α V (A.map_mem f hx) := by
  apply ((ConcreteCategory.bijective_of_isIso ((α V).hom.app ⊤)).comp
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso (A.projι V) ⊤).inv)).1
  simp only [Function.comp_apply]
  have hle' : A.projι U ''ᵁ (Proj.map (A.restrict f) (A.irrelevant_le f) ''ᵁ ⊤) ≤
      A.projι V ''ᵁ ⊤ := by
    rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩
    exact ⟨z, trivial, by rw [← restrict_projι A f]; rfl⟩
  rw [hα _ _ f hle', DirectedModuleGluing.pmap_map M (homOfLE hle).op (homOfLE hle').op
    (homOfLE (Scheme.Hom.image_mono _ le_top)).op, hom_app_pieceDegreeOneSection α hx,
    pieceDegreeOneSection, Iso.hom_inv_id_apply, modules_iso_hom_inv_app]
  exact ProjTwistMap.twistRestrictHom_app_degreeOneSection _ _ hx

theorem pieceIsosCompatible_relTwistingSheaf (A : QuasiCoherentGradedAlgebra X) :
    PieceIsosCompatible (A.relTwistingSheaf 1) (A.relTwistingSheafRestrictIso 1) :=
  fun _ _ f hle x => (A.twistData 1).ψ_hom_app_top f (restrict_projι A f) hle x

end QuasiCoherentGradedAlgebra

namespace QuasiCoherentGradedAlgebra

/-! ### Charts of `Proj_X (S · L)` -/

section Charts

variable {X : Scheme.{u}} (S : QuasiCoherentGradedAlgebra X) (L : X.Modules)

/-- A chart for the frames of `𝒪_{Proj_X (S · L)}(1)`: an affine open `U` of `X`, a frame `e` of
`L` over `U`, and an element `s ∈ S(U)₁`. -/
structure TwistChart where
  /-- The affine open of `X`. -/
  U : X.AffineZariskiSite
  /-- The frame of `L` over `U`. -/
  e : ULift.{u} (Fin 1) → Γ(L, U.1)
  he : Ringed.IsLocalFrame (R := X.sheaf) L U.1 e
  /-- The element of degree one. -/
  s : S.obj.obj (.op U)
  hs : s ∈ S.grading U 1

attribute [local instance] sectionsAlgebra

variable {S L} (hL : L.IsInvertible)

namespace TwistChart

/-- The graded isomorphism `S(U) → (S · L)(U)`, `s ↦ s ⊗ e^d`, of a chart. -/
abbrev gen (i : TwistChart S L) :
    S.grading i.U →+*ᵍ (S.lineBundleTwist L hL).grading i.U :=
  SegreProduct.ofGenerator Γ(X, i.U.1) (S.grading i.U) ((lineBundleSym L hL).grading i.U)
    (frameGenerator_mem (hL := hL) (e := i.e))

theorem gen_mem (i : TwistChart S L) :
    i.gen hL i.s ∈ (S.lineBundleTwist L hL).grading i.U 1 :=
  (i.gen hL).map_mem i.hs

/-- The open `D₊(s ⊗ e)` of the piece of `Proj_X (S · L)` over `U`. -/
def opens (i : TwistChart S L) : (S.lineBundleTwist L hL).relProj.Opens :=
  (S.lineBundleTwist L hL).projι i.U ''ᵁ Proj.basicOpen _ (i.gen hL i.s)

set_option backward.isDefEq.respectTransparency false in
theorem projι_lineBundleTwistHom_eq (i : TwistChart S L) :
    ∃ h, (S.lineBundleTwist L hL).projι i.U ≫ S.lineBundleTwistHom hL =
      Proj.map (i.gen hL) h ≫ S.projι i.U := by
  let := SegreProduct.gradedRing Γ(X, i.U.1) (S.grading i.U)
    ((lineBundleSym L hL).grading i.U) (S.algebraMap_sections_mem i.U)
    ((lineBundleSym L hL).algebraMap_sections_mem i.U)
  obtain ⟨h, e⟩ := SegreProduct.projIsoOfGenerator_hom (S.grading i.U)
    ((lineBundleSym L hL).grading i.U) (S.algebraMap_sections_mem i.U)
    ((lineBundleSym L hL).algebraMap_sections_mem i.U) frameGenerator_mem
    (frameGenerator_free i.he)
  refine ⟨h, ?_⟩
  rw [S.projι_lineBundleTwistHom ⟨i.U, i.e, i.he⟩, framedIso,
    S.lineBundleTwistProjIsoOfFrame_eq i.he]
  unfold lineBundleTwistProjIsoOfFrame
  rw [e]

theorem opens_le_preimage (i : TwistChart S L) :
    i.opens hL ≤ S.lineBundleTwistHom hL ⁻¹ᵁ (S.projι i.U ''ᵁ Proj.basicOpen _ i.s) := by
  obtain ⟨h, e⟩ := i.projι_lineBundleTwistHom_eq hL
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨Proj.map (i.gen hL) h z, hz, ?_⟩
  have := congrArg (fun g => g z) e
  simp only [Scheme.Hom.comp_apply] at this
  exact this.symm

theorem piece_le_preimage (i : TwistChart S L) :
    (S.lineBundleTwist L hL).projι i.U ''ᵁ ⊤ ≤
      S.lineBundleTwistHom hL ⁻¹ᵁ (S.projι i.U ''ᵁ ⊤) := by
  obtain ⟨h, e⟩ := i.projι_lineBundleTwistHom_eq hL
  rintro _ ⟨z, -, rfl⟩
  refine ⟨Proj.map (i.gen hL) h z, trivial, ?_⟩
  have := congrArg (fun g => g z) e
  simp only [Scheme.Hom.comp_apply] at this
  exact this.symm

theorem piece_le_base (i : TwistChart S L) :
    (S.lineBundleTwist L hL).projι i.U ''ᵁ ⊤ ≤
      (S.lineBundleTwist L hL).relProjToBase ⁻¹ᵁ i.U.1 := by
  rintro _ ⟨z, -, rfl⟩
  change ((S.lineBundleTwist L hL).projι i.U ≫ (S.lineBundleTwist L hL).relProjToBase) z ∈ i.U.1
  rw [projι_relProjToBase, Scheme.Hom.comp_apply]
  exact ((S.lineBundleTwist L hL).projToOpen i.U z).2

theorem opens_le_piece (i : TwistChart S L) :
    i.opens hL ≤ (S.lineBundleTwist L hL).projι i.U ''ᵁ ⊤ :=
  Scheme.Hom.image_mono _ le_top

end TwistChart

/-! ### The two families of frames -/

/-- The tensor product of two modules on a scheme, as a module on the scheme. -/
abbrev tensorModule {Y : Scheme.{u}} (F G : Y.Modules) : Y.Modules := moduleSheafTensor F G

theorem tmul_section_restrict {Y : Scheme.{u}} {F G : Y.Modules} {U V : Y.Opens} (h : V ≤ U)
    (a : Γ(F, U)) (b : Γ(G, U)) :
    (tensorModule F G).presheaf.map (homOfLE h).op
        ((moduleSheafTensorBilinear F G).app (op U) a b) =
      (moduleSheafTensorBilinear F G).app (op V) (F.presheaf.map (homOfLE h).op a)
        (G.presheaf.map (homOfLE h).op b) :=
  (moduleSheafTensorBilinear F G).naturality _ _ _

variable (MT : (S.lineBundleTwist L hL).relProj.Modules)
  (αT : ∀ U, MT.restrict ((S.lineBundleTwist L hL).projι U) ≅
    (S.lineBundleTwist L hL).twistingSheaf 1 U)
  (MS : S.relProj.Modules) (αS : ∀ U, MS.restrict (S.projι U) ≅ S.twistingSheaf 1 U)

/-- `φ^* M` for a module `M` on `Proj_X S`. -/
abbrev pullS : (S.lineBundleTwist L hL).relProj.Modules :=
  (Scheme.Modules.pullback (S.lineBundleTwistHom hL)).obj MS

variable (L) in
/-- `π^* L` on `Proj_X (S · L)`. -/
abbrev pullL : (S.lineBundleTwist L hL).relProj.Modules :=
  (Scheme.Modules.pullback (S.lineBundleTwist L hL).relProjToBase).obj L

namespace TwistChart

/-- The frame `s ⊗ e` of `𝒪_{Proj_X (S · L)}(1)` on the open of a chart. -/
def aSec (i : TwistChart S L) : Γ(MT, i.opens hL) :=
  MT.presheaf.map (homOfLE (i.opens_le_piece hL)).op
    (pieceDegreeOneSection MT αT i.U (i.gen_mem hL))

/-- The section `φ^* s ⊗ π^* e` of `φ^* 𝒪_{Proj_X S}(1) ⊗ π^* L` over the piece of a chart. -/
def bTop (i : TwistChart S L) :
    Γ(tensorModule (pullS hL MS) (pullL L hL), (S.lineBundleTwist L hL).projι i.U ''ᵁ ⊤) :=
  (moduleSheafTensorBilinear _ _).app (op _)
    ((pullS hL MS).presheaf.map (homOfLE (i.piece_le_preimage hL)).op
      (Ringed.etaSec (φ := (S.lineBundleTwistHom hL).toRingCatSheafHom)
        (pieceDegreeOneSection MS αS i.U i.hs)))
    ((pullL L hL).presheaf.map (homOfLE (i.piece_le_base hL)).op
      (Ringed.etaSec (φ := (S.lineBundleTwist L hL).relProjToBase.toRingCatSheafHom)
        (i.e default)))

/-- The frame `φ^* s ⊗ π^* e` of `φ^* 𝒪_{Proj_X S}(1) ⊗ π^* L` on the open of a chart. -/
def bSec (i : TwistChart S L) : Γ(tensorModule (pullS hL MS) (pullL L hL), i.opens hL) :=
  (tensorModule (pullS hL MS) (pullL L hL)).presheaf.map
    (homOfLE (i.opens_le_piece hL)).op (i.bTop hL MS αS)

theorem isTrivializingSection_aSec (i : TwistChart S L) :
    IsTrivializingSection MT (i.opens hL) (i.aSec hL MT αT) :=
  isTrivializingSection_pieceDegreeOneSection αT (i.gen_mem hL)

theorem isTrivializingSection_bSec (i : TwistChart S L) :
    IsTrivializingSection (tensorModule (pullS hL MS) (pullL L hL)) (i.opens hL)
      (i.bSec hL MS αS) := by
  have h1 := ((isLocalFrame_of_isTrivializingSection
    (isTrivializingSection_pieceDegreeOneSection αS i.hs)).pullback
      (φ := (S.lineBundleTwistHom hL).toRingCatSheafHom)).restrictLE (i.opens_le_preimage hL)
  have h2 := (i.he.pullback
    (φ := (S.lineBundleTwist L hL).relProjToBase.toRingCatSheafHom)).restrictLE
      ((i.opens_le_piece hL).trans (i.piece_le_base hL))
  refine (congrArg (IsTrivializingSection _ _) ?_).mp
    (IsTrivializingSection.of_isLocalFrame (h1.tensor h2))
  change _ = (tensorModule (pullS hL MS) (pullL L hL)).presheaf.map _ _
  rw [bTop, tmul_section_restrict]
  refine congrArg₂ (fun a b => (moduleSheafTensorBilinear _ _).app _ a b) ?_ ?_
  · erw [Ringed.etaSec_restrict]
    exact (Scheme.Modules.map_map_homOfLE _ _ _ _).trans
      (Scheme.Modules.map_map_homOfLE _ _ _ _).symm
  · exact (Scheme.Modules.map_map_homOfLE _ _ _ _).symm

/-- **The opens of the charts cover `Proj_X (S · L)`** when `S` is generated by `S₁`. -/
theorem iSup_opens (hS : S.GeneratedInDegreeOne) : ⊤ ≤ ⨆ i : TwistChart S L, i.opens hL := by
  intro y _
  obtain ⟨U, z, hz⟩ : ∃ U : (framedAffines L).FullSubcategory, ∃ z,
      (S.lineBundleTwist L hL).projι U.obj z = y :=
    ⟨_, (framedCover hL (S.lineBundleTwist L hL)).covers y⟩
  let i₀ : TwistChart S L := ⟨U.obj, U.property.choose, U.property.choose_spec, 0, zero_mem _⟩
  obtain ⟨h, -⟩ := i₀.projι_lineBundleTwistHom_eq hL
  have hmem : Proj.map (i₀.gen hL) h z ∈
      ⨆ f : S.grading U.obj 1, Proj.basicOpen (S.grading U.obj) (f : S.obj.obj (op U.obj)) := by
    rw [ProjTwistingSheaf.iSup_basicOpen_one_eq_top _
      (S.adjoin_eq_top_of_generatedInDegreeOne hS U.obj)]
    trivial
  obtain ⟨f, hf⟩ := Opens.mem_iSup.1 hmem
  exact Opens.mem_iSup.2 ⟨⟨U.obj, U.property.choose, U.property.choose_spec, f, f.2⟩,
    z, hf, hz⟩

end TwistChart

/-! ### Restricting a chart -/

namespace TwistChart

/-- The restriction of a chart along `f : V ⟶ U`. -/
def restrictChart (i : TwistChart S L) {V : X.AffineZariskiSite} (f : V ⟶ i.U) :
    TwistChart S L :=
  ⟨V, restrictFrame f i.e, isLocalFrame_restrictFrame f i.he, S.restrict f i.s,
    S.map_mem f i.hs⟩

theorem gen_restrictChart (i : TwistChart S L) {V : X.AffineZariskiSite} (f : V ⟶ i.U) :
    (i.restrictChart f).gen hL = SegreProduct.ofGenerator Γ(X, V.1) (S.grading V)
      ((lineBundleSym L hL).grading V) (frameGenerator_mem (hL := hL) (e := restrictFrame f i.e)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrict_gen (i : TwistChart S L) {V : X.AffineZariskiSite} (f : V ⟶ i.U) :
    (S.lineBundleTwist L hL).restrict f (i.gen hL i.s) =
      (i.restrictChart f).gen hL (i.restrictChart f).s := by
  apply Subtype.ext
  change ((S.diagonalRestrict (lineBundleSym L hL) f (i.gen hL i.s)) :
    S.obj.obj (op V) ⊗[Γ(X, V.1)] (lineBundleSym L hL).obj.obj (op V)) = _
  rw [diagonalRestrict, SegreProduct.coe_diagonalMap, gen_restrictChart]
  erw [SegreProduct.coe_ofGenerator_of_mem _ _ _ i.hs,
    SegreProduct.coe_ofGenerator_of_mem _ _ _ (S.map_mem f i.hs)]
  rw [SegreProduct.tensorMap_tmul, pow_one, pow_one, restrict_frameGenerator]
  rfl

theorem piece_le_piece {V U : X.AffineZariskiSite} (f : V ⟶ U) (A : QuasiCoherentGradedAlgebra X) :
    A.projι V ''ᵁ ⊤ ≤ A.projι U ''ᵁ ⊤ := by
  rintro _ ⟨z, -, rfl⟩
  exact ⟨_, trivial, by rw [← restrict_projι A f]; rfl⟩

theorem mem_opens_restrictChart (i : TwistChart S L) {V : X.AffineZariskiSite} (f : V ⟶ i.U)
    {y : (S.lineBundleTwist L hL).relProj} (hyi : y ∈ i.opens hL)
    (hyV : y ∈ (S.lineBundleTwist L hL).projι V ''ᵁ ⊤) : y ∈ (i.restrictChart f).opens hL := by
  obtain ⟨z, hz, rfl⟩ := hyi
  obtain ⟨w, -, hw⟩ := hyV
  have hw' : (S.lineBundleTwist L hL).projι i.U
      (Proj.map ((S.lineBundleTwist L hL).restrict f)
        ((S.lineBundleTwist L hL).irrelevant_le f) w) = (S.lineBundleTwist L hL).projι i.U z := by
    have := congrArg (fun g => g w) (restrict_projι (S.lineBundleTwist L hL) f)
    simp only [Scheme.Hom.comp_apply] at this
    exact this.trans hw
  have hwz := (S.lineBundleTwist L hL).projι i.U |>.isOpenEmbedding.injective hw'
  refine ⟨w, ?_, hw⟩
  rw [← restrict_gen]
  have : Proj.map ((S.lineBundleTwist L hL).restrict f)
      ((S.lineBundleTwist L hL).irrelevant_le f) w ∈ Proj.basicOpen _ (i.gen hL i.s) :=
    hwz ▸ hz
  exact this

theorem pieceDegreeOneSection_congr {A : QuasiCoherentGradedAlgebra X} (M : A.relProj.Modules)
    (α : ∀ U : X.AffineZariskiSite, M.restrict (A.projι U) ≅ A.twistingSheaf 1 U)
    {U : X.AffineZariskiSite} {x y : A.obj.obj (.op U)} (hx : x ∈ A.grading U 1)
    (hy : y ∈ A.grading U 1) (h : x = y) :
    pieceDegreeOneSection M α U hx = pieceDegreeOneSection M α U hy := by
  subst h; rfl

variable {MT αT MS αS}

theorem restrict_pieceDegreeOneSection_gen (hαT : PieceIsosCompatible MT αT) (i : TwistChart S L)
    {V : X.AffineZariskiSite} (f : V ⟶ i.U) :
    MT.presheaf.map (homOfLE (piece_le_piece f _)).op
        (pieceDegreeOneSection MT αT i.U (i.gen_mem hL)) =
      pieceDegreeOneSection MT αT V ((i.restrictChart f).gen_mem hL) :=
  (pieceDegreeOneSection_restrict αT hαT f _ _).trans
    (pieceDegreeOneSection_congr _ _ _ _ (i.restrict_gen hL f))

theorem restrict_bTop (hαS : PieceIsosCompatible MS αS) (i : TwistChart S L)
    {V : X.AffineZariskiSite} (f : V ⟶ i.U) :
    (tensorModule (pullS hL MS) (pullL L hL)).presheaf.map (homOfLE (piece_le_piece f _)).op
        (i.bTop hL MS αS) = (i.restrictChart f).bTop hL MS αS := by
  rw [bTop, bTop, tmul_section_restrict]
  refine congrArg₂ (fun a b => (moduleSheafTensorBilinear _ _).app _ a b) ?_ ?_
  · refine Eq.trans ?_ (congrArg (fun x => (pullS hL MS).presheaf.map
      (homOfLE ((i.restrictChart f).piece_le_preimage hL)).op
      (Ringed.etaSec (φ := (S.lineBundleTwistHom hL).toRingCatSheafHom) x))
        (pieceDegreeOneSection_restrict αS hαS f i.hs (piece_le_piece f S)))
    erw [Ringed.etaSec_restrict]
    exact (Scheme.Modules.map_map_homOfLE _ _ _ _).trans
      (Scheme.Modules.map_map_homOfLE _ _ _ _).symm
  · change _ = (pullL L hL).presheaf.map _ (Ringed.etaSec (L.presheaf.map _ (i.e default)))
    erw [Ringed.etaSec_restrict]
    exact (Scheme.Modules.map_map_homOfLE _ _ _ _).trans
      (Scheme.Modules.map_map_homOfLE _ _ _ _).symm

end TwistChart

end Charts

end QuasiCoherentGradedAlgebra

end Hartshorne
