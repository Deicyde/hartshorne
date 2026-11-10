/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.PicardPullback
import Hartshorne.Scheme.ProjTwistPullback
import Hartshorne.Scheme.GloballyGenerated
import Hartshorne.Scheme.RelativeSegre
import Hartshorne.Scheme.RelativeVeryAmple
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Hartshorne.Scheme.ProjectiveSpaceProper

/-!
# Tensor products of very ample sheaves

Hartshorne, *Algebraic Geometry*, II, Exercise 5.12(a) (p. 126): if `L` and `M` are very ample
relative to `Y` on the same `Y`-scheme `X`, then `L ⊗ M` is very ample relative to `Y`
(`Hartshorne.isVeryAmpleRelative_moduleSheafTensor`).

Given immersions `i : X ⟶ ℙʳ_Y` and `j : X ⟶ ℙˢ_Y` with `i^*𝒪(1) ≅ L` and `j^*𝒪(1) ≅ M`, the
composite of `(i, j) : X ⟶ ℙʳ_Y ×_Y ℙˢ_Y` with the relative Segre embedding `σ_Y` is an immersion
into `ℙ^{rs+r+s}_Y`, and it pulls `𝒪(1)` back to `L ⊗ M` because
`σ_Y^*𝒪(1) ≅ q₁^*𝒪(1) ⊗ q₂^*𝒪(1)` (`Hartshorne.nonempty_relativeSegre_pullback_iso`).

* `Hartshorne.Ringed.nonempty_iso_of_frames`: two sheaves of modules with one-element frames on the
  members of an open cover, with the same transition functions, are isomorphic. The local
  morphisms sending one frame to the other glue (`moduleSheafHom` is a sheaf).
* `Hartshorne.ProjTwistingSheaf.restrict_degreeOneSection_eq_smul`: on `D₊(f)`, the global section
  `g` of `𝒪(1)` is `g/f` times the global section `f`; `isLocalFrame_degreeOneSection`: the
  section `f` is a frame of `𝒪(1)` on `D₊(f)`.
* `Hartshorne.SegreTwist.nonempty_segre_pullback_iso`: over the integers,
  `σ^*𝒪(1) ≅ p₁^*𝒪(1) ⊗ p₂^*𝒪(1)` on `ℙʳ_ℤ ×_ℤ ℙˢ_ℤ`. On the chart `D₊(xᵢ) ×_ℤ D₊(yⱼ)`, the
  pulled-back sections `σ^* z_{ij}` and `p₁^* xᵢ ⊗ p₂^* yⱼ` are frames, and both families have
  the transition functions `(xₖ/xᵢ)(yₗ/yⱼ)` (`segreMorphismInt_appLE_chartRatio`).

The theorem assumes `X` quasi-compact over `Y`. Then the immersion `σ_Y ∘ (i, j)` is
quasi-compact, so it factors as an open immersion into its scheme-theoretic image followed by a
closed immersion, which is the form of immersion in `Hartshorne.IsVeryAmpleRelative`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits AlgebraicGeometry HomogeneousLocalization

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

/-- The local morphism sending a one-element frame to a prescribed section takes the frame
to that section. -/
theorem IsLocalFrame.homOfValues_eval_self {A G : 𝓜} {U : Opens X} {e : Γ(A, U)}
    (hA : IsLocalFrame A U (fun _ : PUnit.{u + 1} => e)) (g : Γ(G, U)) {V : Opens X}
    (h : V ≤ U) :
    moduleSheafHomEval (hA.homOfValues (le_refl U) (fun _ => g)) h
        (A.val.presheaf.map (homOfLE h).op e) = G.val.presheaf.map (homOfLE h).op g := by
  classical
  rw [hA.homOfValues_eval, Fintype.sum_unique]
  have := hA.coord_self h PUnit.unit
  rw [show (h.trans (le_refl U)) = h from rfl, this, Pi.single_eq_same, one_smul]

/-- **Invertible sheaves with matching frames are isomorphic.** If `A` and `B` have one-element
frames `a i`, `b i` on the members of an open cover, and on each overlap the two families have
the same transition function, then `A ≅ B`. -/
theorem nonempty_iso_of_frames {ι : Type u} {A B : 𝓜} (W : ι → Opens X) (hW : ⊤ ≤ iSup W)
    (a : ∀ i, Γ(A, W i)) (b : ∀ i, Γ(B, W i))
    (ha : ∀ i, IsLocalFrame A (W i) (fun _ : PUnit.{u + 1} => a i))
    (hb : ∀ i, IsLocalFrame B (W i) (fun _ : PUnit.{u + 1} => b i))
    (htrans : ∀ i j, ∃ c : R.obj.obj (op (W i ⊓ W j)),
      A.val.presheaf.map (homOfLE inf_le_right).op (a j) =
          c • A.val.presheaf.map (homOfLE inf_le_left).op (a i) ∧
        B.val.presheaf.map (homOfLE inf_le_right).op (b j) =
          c • B.val.presheaf.map (homOfLE inf_le_left).op (b i)) :
    Nonempty (A ≅ B) := by
  let φl : ∀ i, Γ(moduleSheafHom A B, W i) := fun i ↦ (ha i).homOfValues (le_refl _) (fun _ ↦ b i)
  have hcompat : ∀ i j, (moduleSheafHom A B).val.presheaf.map
      (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (φl i) =
      (moduleSheafHom A B).val.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op
        (φl j) := by
    intro i j
    obtain ⟨c, hca, hcb⟩ := htrans i j
    refine (ha j).hom_ext inf_le_right ?_
    funext k
    rw [localFrameEval_apply, localFrameEval_apply, moduleSheafHomEval_restrict,
      moduleSheafHomEval_restrict]
    refine Eq.trans ?_ ((ha j).homOfValues_eval_self (b j) (le_refl _ |>.trans inf_le_right)).symm
    rw [show ((le_refl (W i ⊓ W j)).trans (inf_le_left : W i ⊓ W j ≤ W i)) = inf_le_left from rfl,
      show ((le_refl (W i ⊓ W j)).trans (inf_le_right : W i ⊓ W j ≤ W j)) = inf_le_right from rfl,
      hca, map_smul, (ha i).homOfValues_eval_self (b i) inf_le_left, ← hcb]
  obtain ⟨ψ, hψ, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(moduleSheafHom A B).val.presheaf, (moduleSheafHom A B).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} X) W ⊤ (fun i ↦ homOfLE le_top) hW φl
    (by intro i j; exact hcompat i j)
  let φ : A ⟶ B := moduleSheafHomGlobalSectionsAddEquiv A B ψ
  have hφ : ∀ i, sectionsMap φ (W i) (a i) = b i := by
    intro i
    have h1 : sectionsMap φ (W i) (a i) = moduleSheafHomEval ψ le_top (a i) := rfl
    rw [h1, ← moduleSheafHomEval_restrict ψ le_top (le_refl (W i))]
    erw [hψ i]
    have h2 := (ha i).homOfValues_eval_self (b i) (le_refl (W i))
    rw [show (homOfLE (le_refl (W i))).op = 𝟙 (op (W i)) from rfl,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h2
    exact h2
  have : IsIso φ := modules_isIso_of_locally_bijective φ fun x ↦ by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hW (show x ∈ (⊤ : Opens X) from trivial))
    exact ⟨W i, hi, fun V hV ↦ IsLocalFrame.app_bijective_of_map φ (ha i) (hb i)
      (fun _ ↦ hφ i) hV⟩
  exact ⟨asIso φ⟩

end Ringed

end Hartshorne


namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

/-- Restriction is transitive. -/
theorem res_res (A : 𝓜) {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(A, U)) :
    A.val.presheaf.map (homOfLE h₂).op (A.val.presheaf.map (homOfLE h₁).op x) =
      A.val.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction is semilinear over the restriction of scalars. -/
theorem res_smul (A : 𝓜) {U V : Opens X} (h : V ≤ U) (c : R.obj.obj (op U)) (x : Γ(A, U)) :
    A.val.presheaf.map (homOfLE h).op (c • x) =
      R.obj.map (homOfLE h).op c • A.val.presheaf.map (homOfLE h).op x :=
  A.val.map_smul (homOfLE h).op c x

/-- Restriction commutes with the tensor product of sections. -/
theorem res_tmul {A B : 𝓜} {U V : Opens X} (h : V ≤ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    (moduleSheafTensor A B).val.presheaf.map (homOfLE h).op
        ((moduleSheafTensorBilinear A B).app (op U) a b) =
      (moduleSheafTensorBilinear A B).app (op V) (A.val.presheaf.map (homOfLE h).op a)
        (B.val.presheaf.map (homOfLE h).op b) :=
  (moduleSheafTensorBilinear A B).naturality _ _ _

/-- The tensor product of sections is bilinear over the structure sheaf. -/
theorem tmul_smul_smul {A B : 𝓜} {U : Opens X} (a : Γ(A, U)) (b : Γ(B, U))
    (v w : R.obj.obj (op U)) :
    (moduleSheafTensorBilinear A B).app (op U) (v • a) (w • b) =
      (v * w) • (moduleSheafTensorBilinear A B).app (op U) a b := by
  exact ((LinearMap.map_smul₂ ((moduleSheafTensorBilinear A B).app (op U)) v a (w • b)).trans
    (congrArg (v • ·) (LinearMap.map_smul (((moduleSheafTensorBilinear A B).app (op U)) a) w b))).trans
    (smul_smul v w _)

/-- Global-section form of `nonempty_iso_of_frames`. -/
theorem nonempty_iso_of_global_frames {ι : Type u} {A B : 𝓜} (W : ι → Opens X)
    (hW : ⊤ ≤ iSup W) (α : ι → Γ(A, ⊤)) (β : ι → Γ(B, ⊤))
    (ha : ∀ i, IsLocalFrame A (W i)
      (fun _ : PUnit.{u + 1} => A.val.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op (α i)))
    (hb : ∀ i, IsLocalFrame B (W i)
      (fun _ : PUnit.{u + 1} => B.val.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op (β i)))
    (htrans : ∀ i j, ∃ c : R.obj.obj (op (W i)),
      A.val.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op (α j) =
          c • A.val.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op (α i) ∧
        B.val.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op (β j) =
          c • B.val.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op (β i)) :
    Nonempty (A ≅ B) := by
  refine nonempty_iso_of_frames W hW _ _ ha hb fun i j ↦ ?_
  obtain ⟨c, hca, hcb⟩ := htrans i j
  refine ⟨R.obj.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op c, ?_, ?_⟩
  · rw [res_res, res_res, ← res_res A le_top (inf_le_left : W i ⊓ W j ≤ W i), hca, res_smul, res_res]
  · rw [res_res, res_res, ← res_res B le_top (inf_le_left : W i ⊓ W j ≤ W i), hcb, res_smul, res_res]

end Ringed

end Hartshorne

namespace Hartshorne

namespace ProjTwistingSheaf

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

open ProjGradedModuleSheaf

/-- On `D₊(f)`, `f ∈ S_1`, the global section `f` of `𝒪(1)` restricts to the local generator
`f^1`. -/
theorem restrict_degreeOneSection {f : A} (hf : f ∈ 𝒜 1) :
    (projTwistingSheaf 𝒜 1).val.presheaf.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⊤)).op
        (degreeOneSection ⟨f, hf⟩) = twistGenSection hf 1 := by
  apply Subtype.ext
  funext x
  change degreeOneFraction x.1 hf = twistGen 1 hf x.2
  apply HomogeneousLocalizedModule.ext
  simp only [degreeOneFraction, HomogeneousLocalizedModule.val_mk]
  erw [twistGen_val]
  exact LocalizedModule.mk_eq.2 ⟨1, by simp⟩

open Ringed in
/-- The global section `f` of `𝒪(1)` restricted to `D₊(f)` is a frame there. -/
theorem isLocalFrame_degreeOneSection {f : A} (hf : f ∈ 𝒜 1) :
    IsLocalFrame (R := (Proj 𝒜).sheaf) (projTwistingSheaf 𝒜 1)
      (ProjectiveSpectrum.basicOpen 𝒜 f) (fun _ : PUnit.{u + 1} =>
        (projTwistingSheaf 𝒜 1).val.presheaf.map
          (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⊤)).op
          (degreeOneSection ⟨f, hf⟩)) := by
  rw [restrict_degreeOneSection hf]
  exact ProjTwistPullback.isLocalFrame_twistGenSection hf 1

/-- **Transition functions of `𝒪(1)`.** On `D₊(f)`, the global section `g` of `𝒪(1)` is `g/f`
times the global section `f`, for `f, g ∈ S_1`. -/
theorem restrict_degreeOneSection_eq_smul {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (hg' : g ∈ 𝒜 (1 • 1)) :
    (projTwistingSheaf 𝒜 1).presheaf.map
        (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤)).op
        (degreeOneSection ⟨g, hg⟩) =
      Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf 1 g hg') •
        (projTwistingSheaf 𝒜 1).presheaf.map
          (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤)).op
          (degreeOneSection ⟨f, hf⟩) := by
  apply Subtype.ext
  funext x
  change degreeOneFraction x.1 hg =
    ((Proj.awayToSection 𝒜 f (Away.mk 𝒜 hf 1 g hg')).1 x) • degreeOneFraction x.1 hf
  apply HomogeneousLocalizedModule.ext
  simp only [HomogeneousLocalizedModule.val_smul, degreeOneFraction,
    HomogeneousLocalizedModule.val_mk]
  have h := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f (Away.mk 𝒜 hf 1 g hg') x
  erw [h]
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  rw [← Localization.mk_eq_mk', LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.mk_smul, Submonoid.mk_mul_mk, smul_eq_mul, pow_one, mul_one]
  ring

end ProjTwistingSheaf

end Hartshorne

namespace Hartshorne

open MvPolynomial Ringed

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SegreTwist

variable (r s : ℕ)

/-- `𝒪(1)` on `ℙⁿ_ℤ = Proj ℤ[x₀, …, xₙ]`. -/
noncomputable abbrev twistOne (n : ℕ) : (Proj (segreGrading.{u} n)).Modules :=
  projTwistingSheaf (segreGrading.{u} n) 1

/-- The coordinate `xᵢ` as a global section of `𝒪(1)` on `ℙⁿ_ℤ`. -/
noncomputable abbrev coordSection (n : ℕ) (i : Fin (n + 1)) :
    (twistOne.{u} n).val.presheaf.obj (op ⊤) :=
  ProjTwistingSheaf.degreeOneSection ⟨X i, X_mem_homogeneousSubmodule_one _ i⟩

/-- On `D₊(xᵢ)`, the coordinate `xₖ` of `𝒪(1)` is `xₖ/xᵢ` times `xᵢ`. -/
theorem coordSection_restrict_eq_smul (n : ℕ) (i k : Fin (n + 1)) :
    (twistOne.{u} n).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (segreGrading.{u} n) (X i) ≤ ⊤)).op
        (coordSection n k) =
      Proj.awayToSection _ (X i) (chartRatio (ULift.{u} ℤ) i k) •
        (twistOne.{u} n).presheaf.map
          (homOfLE (le_top : Proj.basicOpen (segreGrading.{u} n) (X i) ≤ ⊤)).op
          (coordSection n i) :=
  ProjTwistingSheaf.restrict_degreeOneSection_eq_smul _ _ _

/-- The coordinate `xᵢ` is a frame of `𝒪(1)` on `D₊(xᵢ)`. -/
theorem isLocalFrame_coordSection (n : ℕ) (i : Fin (n + 1)) :
    IsLocalFrame (R := (Proj (segreGrading.{u} n)).sheaf) (twistOne.{u} n)
      (Proj.basicOpen (segreGrading.{u} n) (X i)) (fun _ : PUnit.{u + 1} =>
        (twistOne.{u} n).val.presheaf.map
          (homOfLE (le_top : Proj.basicOpen (segreGrading.{u} n) (X i) ≤ ⊤)).op
          (coordSection n i)) :=
  ProjTwistingSheaf.isLocalFrame_degreeOneSection _


/-- The whole space lies in the preimage of the whole space. -/
theorem topLePreimageTop {X Y : Scheme.{u}} (f : X ⟶ Y) : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ :=
  fun _ _ ↦ trivial

/-- `σ^*𝒪(1)` for the Segre morphism `σ`. -/
noncomputable abbrev segreA : (segreSource.{u} r s).Modules :=
  (Scheme.Modules.pullback (segreMorphismInt.{u} r s)).obj
    (twistOne.{u} (r * s + r + s))

/-- `p₁^*𝒪(1)`. -/
noncomputable abbrev segreB₁ : (segreSource.{u} r s).Modules :=
  (Scheme.Modules.pullback (segreFst.{u} r s)).obj (twistOne.{u} r)

/-- `p₂^*𝒪(1)`. -/
noncomputable abbrev segreB₂ : (segreSource.{u} r s).Modules :=
  (Scheme.Modules.pullback (segreSnd.{u} r s)).obj (twistOne.{u} s)

/-- `p₁^*𝒪(1) ⊗ p₂^*𝒪(1)`. -/
noncomputable abbrev segreB : (segreSource.{u} r s).Modules :=
  moduleSheafTensor (segreB₁.{u} r s) (segreB₂.{u} r s)

/-- The coordinate `z_c` of `ℙ^{rs+r+s}_ℤ`, pulled back along the Segre morphism. -/
noncomputable def segreAlpha (c : Fin (r + 1) × Fin (s + 1)) :
    (segreA.{u} r s).val.presheaf.obj (op ⊤) :=
  (segreA.{u} r s).val.presheaf.map (homOfLE (topLePreimageTop (segreMorphismInt.{u} r s))).op
    (etaSec (φ := (segreMorphismInt.{u} r s).toRingCatSheafHom) (coordSection _ (segreIndex r s c)))

/-- `p₁^* x_i`. -/
noncomputable def segreFstCoord (i : Fin (r + 1)) : (segreB₁.{u} r s).val.presheaf.obj (op ⊤) :=
  (segreB₁.{u} r s).val.presheaf.map (homOfLE (topLePreimageTop (segreFst.{u} r s))).op
    (etaSec (φ := (segreFst.{u} r s).toRingCatSheafHom) (coordSection r i))

/-- `p₂^* y_j`. -/
noncomputable def segreSndCoord (j : Fin (s + 1)) : (segreB₂.{u} r s).val.presheaf.obj (op ⊤) :=
  (segreB₂.{u} r s).val.presheaf.map (homOfLE (topLePreimageTop (segreSnd.{u} r s))).op
    (etaSec (φ := (segreSnd.{u} r s).toRingCatSheafHom) (coordSection s j))

/-- The section `p₁^* x_i ⊗ p₂^* y_j` of `p₁^*𝒪(1) ⊗ p₂^*𝒪(1)`. -/
noncomputable def segreBeta (c : Fin (r + 1) × Fin (s + 1)) :
    (moduleSheafTensor (segreB₁.{u} r s) (segreB₂.{u} r s)).val.presheaf.obj (op ⊤) :=
  (moduleSheafTensorBilinear _ _).app (op ⊤) (segreFstCoord r s c.1) (segreSndCoord r s c.2)

/-- `σ^* z_{ij}` is a frame of `σ^*𝒪(1)` on the chart `(i, j)`. -/
theorem isLocalFrame_segreAlpha (i : Fin (r + 1)) (j : Fin (s + 1)) :
    IsLocalFrame (R := (segreSource.{u} r s).sheaf) (segreA.{u} r s) (segreChartOpen r s i j)
      (fun _ : PUnit.{u + 1} => (segreA.{u} r s).val.presheaf.map
        (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op (segreAlpha r s (i, j))) := by
  have hle : segreChartOpen r s i j ≤ segreMorphismInt.{u} r s ⁻¹ᵁ
      Proj.basicOpen _ (X (segreIndex r s (i, j))) :=
    (segreMorphismInt_preimage_basicOpen r s i j).ge
  have h1 := ((isLocalFrame_coordSection _ (segreIndex r s (i, j))).pullback
    (φ := (segreMorphismInt.{u} r s).toRingCatSheafHom)).restrictLE hle
  refine (congrArg (IsLocalFrame _ _) (funext fun _ => ?_)).mp h1
  erw [etaSec_restrict, res_res]
  exact (res_res _ _ _ _).symm

/-- The pullback of the restricted coordinate `xₖ` is the restriction of `p₁^* xₖ`. -/
theorem segreFstCoord_restrict (i : Fin (r + 1)) (j : Fin (s + 1)) (k : Fin (r + 1)) :
    (segreB₁.{u} r s).val.presheaf.map
        (homOfLE (show segreChartOpen r s i j ≤ segreFst.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X i)
          from inf_le_left)).op
        (etaSec (φ := (segreFst.{u} r s).toRingCatSheafHom)
          ((twistOne.{u} r).val.presheaf.map
            (homOfLE (le_top : Proj.basicOpen (segreGrading.{u} r) (X i) ≤ ⊤)).op
            (coordSection r k))) =
      (segreB₁.{u} r s).val.presheaf.map (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op
        (segreFstCoord r s k) := by
  erw [etaSec_restrict, res_res]
  exact (res_res _ _ _ _).symm

/-- The pullback of the restricted coordinate `yₗ` is the restriction of `p₂^* yₗ`. -/
theorem segreSndCoord_restrict (i : Fin (r + 1)) (j : Fin (s + 1)) (l : Fin (s + 1)) :
    (segreB₂.{u} r s).val.presheaf.map
        (homOfLE (show segreChartOpen r s i j ≤ segreSnd.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X j)
          from inf_le_right)).op
        (etaSec (φ := (segreSnd.{u} r s).toRingCatSheafHom)
          ((twistOne.{u} s).val.presheaf.map
            (homOfLE (le_top : Proj.basicOpen (segreGrading.{u} s) (X j) ≤ ⊤)).op
            (coordSection s l))) =
      (segreB₂.{u} r s).val.presheaf.map (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op
        (segreSndCoord r s l) := by
  erw [etaSec_restrict, res_res]
  exact (res_res _ _ _ _).symm

/-- `p₁^* xᵢ ⊗ p₂^* yⱼ` is a frame of `p₁^*𝒪(1) ⊗ p₂^*𝒪(1)` on the chart `(i, j)`. -/
theorem isLocalFrame_segreBeta (i : Fin (r + 1)) (j : Fin (s + 1)) :
    IsLocalFrame (R := (segreSource.{u} r s).sheaf)
      (moduleSheafTensor (segreB₁.{u} r s) (segreB₂.{u} r s)) (segreChartOpen r s i j)
      (fun _ : PUnit.{u + 1} => (moduleSheafTensor (segreB₁.{u} r s) (segreB₂.{u} r s)).val.presheaf.map
        (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op (segreBeta r s (i, j))) := by
  have h1 := ((isLocalFrame_coordSection r i).pullback
    (φ := (segreFst.{u} r s).toRingCatSheafHom)).restrictLE
    (show segreChartOpen r s i j ≤ segreFst.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X i) from inf_le_left)
  have h2 := ((isLocalFrame_coordSection s j).pullback
    (φ := (segreSnd.{u} r s).toRingCatSheafHom)).restrictLE
    (show segreChartOpen r s i j ≤ segreSnd.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X j) from inf_le_right)
  have h3 := h1.tensor h2
  refine (congrArg (IsLocalFrame _ _) (funext fun _ => ?_)).mp h3
  exact (congrArg₂ (fun a b => (moduleSheafTensorBilinear (segreB₁.{u} r s) (segreB₂.{u} r s)).app
    (op (segreChartOpen r s i j)) a b) (segreFstCoord_restrict r s i j i)
    (segreSndCoord_restrict r s i j j)).trans (res_tmul _ _ _).symm

/-- The pullback of the restricted coordinate `z_c` is the restriction of `σ^* z_c`. -/
theorem segreAlpha_restrict (i : Fin (r + 1)) (j : Fin (s + 1)) (c : Fin (r + 1) × Fin (s + 1)) :
    (segreA.{u} r s).val.presheaf.map
        (homOfLE (segreMorphismInt_preimage_basicOpen r s i j).ge).op
        (etaSec (φ := (segreMorphismInt.{u} r s).toRingCatSheafHom)
          ((twistOne.{u} (r * s + r + s)).val.presheaf.map
            (homOfLE (le_top : Proj.basicOpen (segreGrading.{u} (r * s + r + s))
              (X (segreIndex r s (i, j))) ≤ ⊤)).op
            (coordSection _ (segreIndex r s c)))) =
      (segreA.{u} r s).val.presheaf.map (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op
        (segreAlpha r s c) := by
  erw [etaSec_restrict, res_res]
  exact (res_res _ _ _ _).symm

/-- On the chart `(i, j)`, `σ^* z_{kl} = (xₖ/xᵢ)(yₗ/yⱼ) · σ^* z_{ij}`. -/
theorem segreAlpha_trans (i : Fin (r + 1)) (j : Fin (s + 1)) (k : Fin (r + 1))
    (l : Fin (s + 1)) :
    (segreA.{u} r s).presheaf.map (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op
        (segreAlpha r s (k, l)) =
      (segreFstSection r s i j (chartRatio _ i k) * segreSndSection r s i j (chartRatio _ j l)) •
        (segreA.{u} r s).presheaf.map (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op
          (segreAlpha r s (i, j)) := by
  have e := congrArg (etaSec (φ := (segreMorphismInt.{u} r s).toRingCatSheafHom))
    (coordSection_restrict_eq_smul (r * s + r + s) (segreIndex r s (i, j)) (segreIndex r s (k, l)))
  erw [etaSec_smul] at e
  have e2 := congrArg ((segreA.{u} r s).val.presheaf.map
    (homOfLE (segreMorphismInt_preimage_basicOpen r s i j).ge).op) e
  erw [res_smul, segreAlpha_restrict, segreAlpha_restrict] at e2
  rw [← segreMorphismInt_appLE_chartRatio]
  exact e2

/-- On the chart `(i, j)`, `p₁^* xₖ = (xₖ/xᵢ) · p₁^* xᵢ`. -/
theorem segreFstCoord_trans (i : Fin (r + 1)) (j : Fin (s + 1)) (k : Fin (r + 1)) :
    (segreB₁.{u} r s).presheaf.map (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op
        (segreFstCoord r s k) =
      segreFstSection r s i j (chartRatio _ i k) •
        (segreB₁.{u} r s).presheaf.map (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op
          (segreFstCoord r s i) := by
  have e := congrArg (etaSec (φ := (segreFst.{u} r s).toRingCatSheafHom))
    (coordSection_restrict_eq_smul r i k)
  erw [etaSec_smul] at e
  have e2 := congrArg ((segreB₁.{u} r s).val.presheaf.map
    (homOfLE (show segreChartOpen r s i j ≤ segreFst.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X i)
      from inf_le_left)).op) e
  erw [res_smul, segreFstCoord_restrict, segreFstCoord_restrict] at e2
  exact e2

/-- On the chart `(i, j)`, `p₂^* yₗ = (yₗ/yⱼ) · p₂^* yⱼ`. -/
theorem segreSndCoord_trans (i : Fin (r + 1)) (j : Fin (s + 1)) (l : Fin (s + 1)) :
    (segreB₂.{u} r s).presheaf.map (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op
        (segreSndCoord r s l) =
      segreSndSection r s i j (chartRatio _ j l) •
        (segreB₂.{u} r s).presheaf.map (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op
          (segreSndCoord r s j) := by
  have e := congrArg (etaSec (φ := (segreSnd.{u} r s).toRingCatSheafHom))
    (coordSection_restrict_eq_smul s j l)
  erw [etaSec_smul] at e
  have e2 := congrArg ((segreB₂.{u} r s).val.presheaf.map
    (homOfLE (show segreChartOpen r s i j ≤ segreSnd.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X j)
      from inf_le_right)).op) e
  erw [res_smul, segreSndCoord_restrict, segreSndCoord_restrict] at e2
  exact e2

/-- On the chart `(i, j)`, `p₁^* xₖ ⊗ p₂^* yₗ = (xₖ/xᵢ)(yₗ/yⱼ) · p₁^* xᵢ ⊗ p₂^* yⱼ`. -/
theorem segreBeta_trans (i : Fin (r + 1)) (j : Fin (s + 1)) (k : Fin (r + 1))
    (l : Fin (s + 1)) :
    (segreB.{u} r s).presheaf.map
        (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op (segreBeta r s (k, l)) =
      (segreFstSection r s i j (chartRatio _ i k) * segreSndSection r s i j (chartRatio _ j l)) •
        (segreB.{u} r s).presheaf.map
          (homOfLE (le_top : segreChartOpen r s i j ≤ ⊤)).op (segreBeta r s (i, j)) := by
  have hF := segreFstCoord_trans r s i j k
  have hS := segreSndCoord_trans r s i j l
  exact (res_tmul _ _ _).trans ((congrArg₂ (fun a b =>
    (moduleSheafTensorBilinear (segreB₁.{u} r s) (segreB₂.{u} r s)).app
      (op (segreChartOpen r s i j)) a b) hF hS).trans
    ((tmul_smul_smul _ _ _ _).trans (congrArg _ (res_tmul _ _ _).symm)))

/-- **The Segre morphism pulls `𝒪(1)` back to `𝒪(1) ⊠ 𝒪(1)`** over the integers:
`σ^*𝒪(1) ≅ p₁^*𝒪(1) ⊗ p₂^*𝒪(1)` on `ℙʳ_ℤ ×_ℤ ℙˢ_ℤ`. -/
theorem nonempty_segre_pullback_iso :
    Nonempty (segreA.{u} r s ≅ moduleSheafTensor (segreB₁.{u} r s) (segreB₂.{u} r s)) := by
  refine nonempty_iso_of_global_frames (R := (segreSource.{u} r s).sheaf)
    (ι := ULift.{u} (Fin (r + 1) × Fin (s + 1)))
    (fun c => segreChartOpen r s c.down.1 c.down.2) ?_
    (fun c => segreAlpha r s c.down) (fun c => segreBeta r s c.down)
    (fun c => isLocalFrame_segreAlpha r s c.down.1 c.down.2)
    (fun c => isLocalFrame_segreBeta r s c.down.1 c.down.2)
    (fun c d => ⟨_, segreAlpha_trans r s c.down.1 c.down.2 d.down.1 d.down.2,
      segreBeta_trans r s c.down.1 c.down.2 d.down.1 d.down.2⟩)
  intro x _
  have hx : x ∈ ⨆ c : Fin (r + 1) × Fin (s + 1), segreChartOpen.{u} r s c.1 c.2 := by
    rw [show (⨆ c : Fin (r + 1) × Fin (s + 1), segreChartOpen.{u} r s c.1 c.2) = ⊤ from
      segreChartOpen_iSup r s]
    trivial
  obtain ⟨c, hc⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨ULift.up c, hc⟩

end SegreTwist

end Hartshorne

namespace Hartshorne

section Relative

open Ringed

variable (r s : ℕ)

/-- `𝒪(1)` on `ℙⁿ_ℤ` is invertible, in the ringed-space sense. -/
theorem ringed_isInvertible_projectiveSpaceIntTwistingSheaf (n : ℕ) :
    Ringed.IsInvertible (R := (projectiveSpaceScheme (ULift.{u} ℤ) n).sheaf)
      (projectiveSpaceIntTwistingSheaf.{u} n 1) :=
  (Scheme.Modules.isInvertible_iff_ringed _).mp (isInvertible_projectiveSpaceIntTwistingSheaf n 1)

/-- `𝒪(1)` on `ℙⁿ_Y` is invertible, in the ringed-space sense. -/
theorem ringed_isInvertible_projectiveSpaceTwistingSheaf (n : ℕ) (Y : Scheme.{u}) :
    Ringed.IsInvertible (R := (projectiveSpaceOverScheme n Y).sheaf)
      (projectiveSpaceTwistingSheaf.{u} n Y 1) :=
  isInvertible_pullback _ (ringed_isInvertible_projectiveSpaceIntTwistingSheaf n)

/-- **The relative Segre embedding pulls `𝒪(1)` back to `𝒪(1) ⊠ 𝒪(1)`**:
`σ_Y^*𝒪(1) ≅ q₁^*𝒪(1) ⊗ q₂^*𝒪(1)` on `ℙʳ_Y ×_Y ℙˢ_Y`. -/
theorem nonempty_relativeSegre_pullback_iso (Y : Scheme.{u}) :
    Nonempty ((Scheme.Modules.pullback (relativeSegre r s Y)).obj
        (projectiveSpaceTwistingSheaf (r * s + r + s) Y 1) ≅
      moduleSheafTensor
        ((Scheme.Modules.pullback (pullback.fst (projectiveSpaceOverSchemeProjection r Y)
          (projectiveSpaceOverSchemeProjection s Y))).obj (projectiveSpaceTwistingSheaf r Y 1))
        ((Scheme.Modules.pullback (pullback.snd (projectiveSpaceOverSchemeProjection r Y)
          (projectiveSpaceOverSchemeProjection s Y))).obj (projectiveSpaceTwistingSheaf s Y 1))) := by
  obtain ⟨e⟩ := SegreTwist.nonempty_segre_pullback_iso.{u} r s
  let t := relativeSegreSourceToInt r s Y
  have h1 : t ≫ segreFst r s = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have h2 : t ≫ segreSnd r s = pullback.snd _ _ ≫ pullback.fst _ _ := pullback.lift_snd _ _ _
  have i1 : Ringed.IsInvertible (R := (segreSource.{u} r s).sheaf) (SegreTwist.segreB₁.{u} r s) :=
    isInvertible_pullback _ (ringed_isInvertible_projectiveSpaceIntTwistingSheaf r)
  have i2 : Ringed.IsInvertible (R := (segreSource.{u} r s).sheaf) (SegreTwist.segreB₂.{u} r s) :=
    isInvertible_pullback _ (ringed_isInvertible_projectiveSpaceIntTwistingSheaf s)
  refine ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (relativeSegre_fst r s Y)).app _ ≪≫
    ((Scheme.Modules.pullbackComp t (segreMorphismInt r s)).app _).symm ≪≫
    (Scheme.Modules.pullback t).mapIso e ≪≫ pullbackTensorIso t i1 i2 ≪≫
    moduleSheafTensorIsoOfIso
      ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr h1).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm)
      ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr h2).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm)⟩

end Relative

end Hartshorne

namespace Hartshorne

open Ringed

/-- **Hartshorne II, Exercise 5.12(a).** If `L` and `M` are very ample relative to `Y` on the same
`Y`-scheme `X`, then `L ⊗ M` is very ample relative to `Y`. The immersion is the Segre embedding of
the product of the two immersions; `X` is assumed quasi-compact over `Y`, so that this immersion is
an open immersion into a closed subscheme. -/
theorem isVeryAmpleRelative_moduleSheafTensor {X Y : Scheme.{u}} {p : X ⟶ Y} [QuasiCompact p]
    {L M : X.Modules} (hL : IsVeryAmpleRelative p L) (hM : IsVeryAmpleRelative p M) :
    IsVeryAmpleRelative p (moduleSheafTensor L M) := by
  obtain ⟨hLinv, r, Z, o, c, ho, hc, hp, ⟨eL⟩⟩ := hL
  obtain ⟨hMinv, s, Z', o', c', ho', hc', hp', ⟨eM⟩⟩ := hM
  have hij : (o ≫ c) ≫ projectiveSpaceOverSchemeProjection r Y =
      (o' ≫ c') ≫ projectiveSpaceOverSchemeProjection s Y := hp.trans hp'.symm
  let φ : X ⟶ relativeSegreSource r s Y := pullback.lift (o ≫ c) (o' ≫ c') hij
  let ι : X ⟶ projectiveSpaceOverScheme (r * s + r + s) Y := φ ≫ relativeSegre r s Y
  have hιp : ι ≫ projectiveSpaceOverSchemeProjection (r * s + r + s) Y = p := by
    simp only [ι, φ, Category.assoc, relativeSegre_projection, relativeSegreSourceProjection,
      pullback.lift_fst_assoc, hp]
  have : IsImmersion (φ ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]
    infer_instance
  have : IsImmersion φ := IsImmersion.of_comp φ (pullback.fst _ _)
  have : QuasiCompact (ι ≫ projectiveSpaceOverSchemeProjection (r * s + r + s) Y) := by
    rw [hιp]
    infer_instance
  have := projectiveSpaceOverSchemeProjection_isProper (r * s + r + s) Y
  have : QuasiCompact ι := QuasiCompact.of_comp ι (projectiveSpaceOverSchemeProjection _ Y)
  obtain ⟨e⟩ := nonempty_relativeSegre_pullback_iso r s Y
  have i1 := ringed_isInvertible_projectiveSpaceTwistingSheaf r Y
  have i2 := ringed_isInvertible_projectiveSpaceTwistingSheaf s Y
  have hinv : Scheme.Modules.IsInvertible (X := X) (moduleSheafTensor L M) :=
    (Scheme.Modules.isInvertible_iff_ringed _).mpr (isInvertible_moduleSheafTensor
      ((Scheme.Modules.isInvertible_iff_ringed _).mp hLinv)
      ((Scheme.Modules.isInvertible_iff_ringed _).mp hMinv))
  refine ⟨hinv, r * s + r + s, ι.image, ι.toImage, ι.imageι, inferInstance, inferInstance,
    by rw [Scheme.Hom.toImage_imageι, hιp], ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackCongr (Scheme.Hom.toImage_imageι ι)).app _ ≪≫
    ((Scheme.Modules.pullbackComp φ (relativeSegre r s Y)).app _).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso e ≪≫
    pullbackTensorIso φ (isInvertible_pullback _ i1) (isInvertible_pullback _ i2) ≪≫
    moduleSheafTensorIsoOfIso
      ((Scheme.Modules.pullbackComp _ _).app _ ≪≫
        (Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app _ ≪≫ eL)
      ((Scheme.Modules.pullbackComp _ _).app _ ≪≫
        (Scheme.Modules.pullbackCongr (pullback.lift_snd _ _ _)).app _ ≪≫ eM)

end Hartshorne
