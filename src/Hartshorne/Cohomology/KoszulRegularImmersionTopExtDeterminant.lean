/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.KoszulRegularImmersionTopExtTarget
import Hartshorne.Cohomology.KoszulRegularImmersionConormal
import Hartshorne.Scheme.ExteriorPerfectPairing

/-!
# Determinant frames of the conormal sheaf of a Koszul-regular immersion

Let `i : X ⟶ Y` be a closed immersion with ideal sheaf `I`. For a Koszul chart `c` on `V` with
generators `f₁, …, f_r` (`r = s + 1`), the conormal classes `[fⱼ]`
(`Hartshorne.KoszulImmersion.KoszulChart.conormalSection`, the images of the generators under the
unit `I ⟶ i_* i^* I`) are sections of `i^* I` over `i⁻¹ V`, and their exterior product
`ω_c = [f₁] ∧ ⋯ ∧ [f_r]` (`KoszulChart.conormalFrame`) is a section of `⋀^r(i^* I)`. These
sections restrict to those of the restricted charts (`conormalFrame_restrict`) and satisfy the
determinant transition law `ω_{f Q} = det Q · ω_f` (`conormalFrame_of_eq_vecMul`, from
`Hartshorne.Koszul.ιMulti_family_topIndex_vecMul`).

If the `[fⱼ]` form a frame of `i^* I` over `i⁻¹ V`, then `ω_c` is a frame of `⋀^r(i^* I)`
(`isLocalFrame_conormalFrame`), and the gluing of the local top-Ext isomorphisms gives
`ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_* ℋom(⋀^r(i^* I), i^* M)` for a Koszul-regular immersion and a
quasi-coherent `M`
(`Hartshorne.KoszulTarget.nonempty_sheafExt_iso_of_isLocalFrame_conormalSection`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace Koszul

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P] {r : ℕ}

/-- `(∑ₖ Q_{k1} eₖ) ∧ ⋯ ∧ (∑ₖ Q_{kr} eₖ) = det Q · e₁ ∧ ⋯ ∧ e_r`. -/
theorem ιMulti_family_topIndex_vecMul (e : Fin r → P) (Q : Matrix (Fin r) (Fin r) A) :
    exteriorPower.ιMulti_family A r (fun j => ∑ k, Q k j • e k) (topIndex r) =
      Q.det • exteriorPower.ιMulti_family A r e (topIndex r) := by
  let φ : (Fin r → A) →ₗ[A] P := Fintype.linearCombination A e
  have h1 : e = φ ∘ Pi.basisFun A (Fin r) := funext fun j => by
    simp [φ, Fintype.linearCombination_apply_single]
  have h2 : (fun j => ∑ k, Q k j • e k) = φ ∘ (Matrix.toLin' Q ∘ Pi.basisFun A (Fin r)) :=
    funext fun j => by
      simp only [Function.comp_apply, Pi.basisFun_apply, Matrix.toLin'_apply,
        Matrix.mulVec_single_one, φ, Fintype.linearCombination_apply]
      rfl
  rw [h2, ← exteriorPower.map_apply_ιMulti_family, ← exteriorPower.map_apply_ιMulti_family]
  change exteriorPower.map r φ (exteriorPower.map r (Matrix.toLin' Q) (topForm r)) = _
  rw [exteriorPower_map_topForm, map_smul, topForm, exteriorPower.map_apply_ιMulti_family, ← h1]

end Koszul

namespace ExteriorPerfectPairing

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (F : SheafOfModules.{u} (ringCatSheafOf R)) {ι : Type*} [LinearOrder ι]

open SheafTensorOperations

/-- Exterior products of sections restrict to the exterior products of the restrictions. -/
lemma exteriorPowerFrame_restrict (k : ℕ) {U V : Opens X} (h : V ≤ U)
    (e : ι → F.val.obj (op U)) (K : Set.powersetCard ι k) :
    (moduleSheafExteriorPower k F).val.presheaf.map (homOfLE h).op (exteriorPowerFrame F k e K) =
      exteriorPowerFrame F k (fun j => F.val.presheaf.map (homOfLE h).op (e j)) K := by
  exact (PresheafOfModules.naturality_apply (moduleSheafExteriorPowerUnit k F) (homOfLE h).op
    (exteriorPower.ιMulti_family _ k e K)).symm.trans
      (congrArg _ (exteriorPowerPresheaf_restrictₛₗ_ιMulti_family F k _ e K))

/-- The determinant law for the top exterior product of sections. -/
lemma exteriorPowerFrame_topIndex_vecMul {r : ℕ} {U : Opens X} (e : Fin r → F.val.obj (op U))
    (Q : Matrix (Fin r) (Fin r) ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))) :
    exteriorPowerFrame F r (fun j => ∑ k, Q k j • e k) (Koszul.topIndex r) =
      Q.det • exteriorPowerFrame F r e (Koszul.topIndex r) := by
  simp only [exteriorPowerFrame]
  rw [Koszul.ιMulti_family_topIndex_vecMul]
  exact map_smul _ _ _

end ExteriorPerfectPairing

namespace KoszulImmersion

open AlgebraicGeometry Koszul KoszulConormal Ringed

variable {Y X : Scheme.{u}} {i : X ⟶ Y} {r : ℕ} [IsClosedImmersion i]

/-- The generators of a chart vanish on `X`. -/
lemma KoszulChart.app_f_eq_zero {V : Y.Opens} (c : KoszulChart i r V) (j : Fin r) :
    i.app V (c.f j) = 0 := by
  have hmem : c.f j ∈ i.ker.ideal ⟨V, c.hV⟩ := c.hI ▸ Ideal.subset_span ⟨j, rfl⟩
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hmem
  exact hmem

omit [IsClosedImmersion i] in
/-- The inclusion of the ideal sheaf is injective on sections. -/
lemma closedImmersionIdealSheafι_app_injective (W : Y.Opens) :
    Function.Injective ((closedImmersionIdealSheafι i).app W) := by
  have : Mono ((SheafOfModules.evaluation Y.ringCatSheaf (op W)).map
      (closedImmersionIdealSheafι i)) := by
    have : (SheafOfModules.evaluation Y.ringCatSheaf (op W)).Additive := ⟨rfl⟩
    unfold closedImmersionIdealSheafι
    rw [← Limits.kernelComparison_comp_ι]
    infer_instance
  intro a b hab
  exact (ModuleCat.mono_iff_injective _).mp this hab

/-- The section of the ideal sheaf given by a generator of a chart. -/
noncomputable def KoszulChart.idealSection {V : Y.Opens} (c : KoszulChart i r V) (j : Fin r) :
    Γ(closedImmersionIdealSheaf i, V) :=
  (exists_closedImmersionIdealSheafι_app_eq i (c.f j) (c.app_f_eq_zero j)).choose

/-- The section of the ideal sheaf of a generator maps to the generator. -/
lemma KoszulChart.ι_idealSection {V : Y.Opens} (c : KoszulChart i r V) (j : Fin r) :
    (closedImmersionIdealSheafι i).app V (c.idealSection j) = c.f j :=
  (exists_closedImmersionIdealSheafι_app_eq i (c.f j) (c.app_f_eq_zero j)).choose_spec

/-- The conormal class `[fⱼ]` of a generator: its image under the unit `I ⟶ i_* i^* I`, a section
of `i^* I` over `i⁻¹ V`. -/
noncomputable def KoszulChart.conormalSection {V : Y.Opens} (c : KoszulChart i r V)
    (j : Fin r) : Γ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i), i ⁻¹ᵁ V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (closedImmersionIdealSheaf i)).app V
    (c.idealSection j)

/-- The ideal-sheaf sections of a chart restrict to those of the restricted chart. -/
lemma KoszulChart.idealSection_restrict {V : Y.Opens} (c : KoszulChart i r V) (W : Y.Opens)
    (b : Γ(Y, V)) (hb : Y.basicOpen b = W) (j : Fin r) :
    (closedImmersionIdealSheaf i).presheaf.map (homOfLE (le_of_basicOpen_eq b hb)).op
      (c.idealSection j) = (c.restrict W b hb).idealSection j := by
  apply closedImmersionIdealSheafι_app_injective
  rw [KoszulChart.ι_idealSection]
  refine (PresheafOfModules.naturality_apply (closedImmersionIdealSheafι i).val
    (homOfLE (le_of_basicOpen_eq b hb)).op (c.idealSection j)).trans ?_
  erw [c.ι_idealSection j]
  rfl

/-- The conormal classes of a chart restrict to those of its restriction to a basic open. -/
lemma KoszulChart.conormalSection_restrict {V : Y.Opens} (c : KoszulChart i r V) (W : Y.Opens)
    (b : Γ(Y, V)) (hb : Y.basicOpen b = W) (j : Fin r) :
    ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)).presheaf.map
      (homOfLE (i.preimage_mono (le_of_basicOpen_eq b hb))).op (c.conormalSection j) =
      (c.restrict W b hb).conormalSection j := by
  rw [KoszulChart.conormalSection, KoszulChart.conormalSection,
    ← c.idealSection_restrict W b hb j]
  exact (PresheafOfModules.naturality_apply ((Scheme.Modules.pullbackPushforwardAdjunction
    i).unit.app (closedImmersionIdealSheaf i)).val (homOfLE (le_of_basicOpen_eq b hb)).op
      (c.idealSection j)).symm

/-- The ideal-sheaf sections transform by `Q` under a change of generators `f ↦ f Q`. -/
lemma KoszulChart.idealSection_of_eq_vecMul {V : Y.Opens} (c : KoszulChart i r V)
    (g : Fin r → Γ(Y, V)) (hIg : i.ker.ideal ⟨V, c.hV⟩ = Ideal.span (Set.range g))
    (hfg : IsKoszulRegular g (ModuleCat.of Γ(Y, V) Γ(Y, V)))
    (Q : Matrix (Fin r) (Fin r) Γ(Y, V)) (hg : g = Matrix.vecMul c.f Q) (j : Fin r) :
    (⟨c.hV, g, hIg, hfg⟩ : KoszulChart i r V).idealSection j =
      ∑ k, Q k j • c.idealSection k := by
  apply closedImmersionIdealSheafι_app_injective
  rw [KoszulChart.ι_idealSection, map_sum]
  simp_rw [Scheme.Modules.Hom.app_smul, KoszulChart.ι_idealSection]
  change g j = ∑ k, Q k j * c.f k
  rw [hg]
  simp only [Matrix.vecMul, dotProduct, mul_comm]

/-- The conormal classes transform by `Q` under a change of generators `f ↦ f Q`. -/
lemma KoszulChart.conormalSection_of_eq_vecMul {V : Y.Opens} (c : KoszulChart i r V)
    (g : Fin r → Γ(Y, V)) (hIg : i.ker.ideal ⟨V, c.hV⟩ = Ideal.span (Set.range g))
    (hfg : IsKoszulRegular g (ModuleCat.of Γ(Y, V) Γ(Y, V)))
    (Q : Matrix (Fin r) (Fin r) Γ(Y, V)) (hg : g = Matrix.vecMul c.f Q) (j : Fin r) :
    (⟨c.hV, g, hIg, hfg⟩ : KoszulChart i r V).conormalSection j =
      ∑ k, i.app V (Q k j) • c.conormalSection k := by
  rw [KoszulChart.conormalSection, c.idealSection_of_eq_vecMul g hIg hfg Q hg j, map_sum]
  simp_rw [Scheme.Modules.Hom.app_smul]
  rfl

variable {s : ℕ}

/-- The determinant frame `[f₁] ∧ ⋯ ∧ [f_r]` of `⋀^r(i^* I)` over `i⁻¹ V` given by a chart. -/
noncomputable def KoszulChart.conormalFrame {V : Y.Opens} (c : KoszulChart i (s + 1) V) :
    Γ(moduleSheafExteriorPower (R := X.sheaf) (s + 1)
      ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)), i ⁻¹ᵁ V) :=
  ExteriorPerfectPairing.exteriorPowerFrame (R := X.sheaf)
    ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)) (s + 1)
    (fun j => c.conormalSection j) (topIndex (s + 1))

/-- The determinant frames restrict to the determinant frames of the restricted charts. -/
lemma KoszulChart.conormalFrame_restrict {V : Y.Opens} (c : KoszulChart i (s + 1) V)
    (W : Y.Opens) (b : Γ(Y, V)) (hb : Y.basicOpen b = W) :
    (moduleSheafExteriorPower (R := X.sheaf) (s + 1)
      ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))).val.presheaf.map
        (homOfLE (i.preimage_mono (le_of_basicOpen_eq b hb))).op c.conormalFrame =
      (c.restrict W b hb).conormalFrame := by
  rw [KoszulChart.conormalFrame, ExteriorPerfectPairing.exteriorPowerFrame_restrict]
  congr 1
  funext j
  exact c.conormalSection_restrict W b hb j

/-- **The determinant transition law for the frames**: `ω_{f Q} = det Q · ω_f`. -/
lemma KoszulChart.conormalFrame_of_eq_vecMul {V : Y.Opens} (c : KoszulChart i (s + 1) V)
    (g : Fin (s + 1) → Γ(Y, V)) (hIg : i.ker.ideal ⟨V, c.hV⟩ = Ideal.span (Set.range g))
    (hfg : IsKoszulRegular g (ModuleCat.of Γ(Y, V) Γ(Y, V)))
    (Q : Matrix (Fin (s + 1)) (Fin (s + 1)) Γ(Y, V)) (hg : g = Matrix.vecMul c.f Q) :
    (⟨c.hV, g, hIg, hfg⟩ : KoszulChart i (s + 1) V).conormalFrame =
      i.app V Q.det • (show Γ(moduleSheafExteriorPower (R := X.sheaf) (s + 1)
        ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)), i ⁻¹ᵁ V) from
          c.conormalFrame) := by
  have h := ExteriorPerfectPairing.exteriorPowerFrame_topIndex_vecMul (R := X.sheaf)
    ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))
    (fun j => c.conormalSection j) (Q.map (i.app V).hom)
  rw [show (Q.map (i.app V).hom).det = (i.app V).hom Q.det from
    (RingHom.map_det (i.app V).hom Q).symm] at h
  rw [KoszulChart.conormalFrame, KoszulChart.conormalFrame]
  refine Eq.trans ?_ h
  congr 1
  funext j
  exact c.conormalSection_of_eq_vecMul g hIg hfg Q hg j

/-- The determinant frame of a chart is a frame of `⋀^r(i^* I)` over `i⁻¹ V` if the conormal
classes of the generators are a frame of `i^* I`. -/
lemma KoszulChart.isLocalFrame_conormalFrame {V : Y.Opens} (c : KoszulChart i (s + 1) V)
    (hc : IsLocalFrame (R := X.sheaf) ((Scheme.Modules.pullback i).obj
      (closedImmersionIdealSheaf i)) (i ⁻¹ᵁ V) (fun j => c.conormalSection j)) :
    IsLocalFrame (R := X.sheaf) (moduleSheafExteriorPower (R := X.sheaf) (s + 1)
      ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i))) (i ⁻¹ᵁ V)
      (fun _ : PUnit.{u + 1} => c.conormalFrame) := by
  let σ : PUnit.{u + 1} ≃ Set.powersetCard (Fin (s + 1)) (s + 1) :=
    ⟨fun _ => topIndex (s + 1), fun _ => PUnit.unit, fun _ => rfl,
      fun _ => Subsingleton.elim _ _⟩
  exact (ExteriorPerfectPairing.isLocalFrame_exteriorPowerFrame (R := X.sheaf) _ hc
    (s + 1)).reindex σ

end KoszulImmersion

namespace KoszulTarget

open AlgebraicGeometry Koszul KoszulImmersion KoszulConormal Ringed

variable {Y X : Scheme.{u}} {i : X ⟶ Y} {s : ℕ}

/-- **The top sheaf Ext of a Koszul-regular immersion, assuming the conormal frames.** For a
Koszul-regular closed immersion `i : X ⟶ Y` of codimension `s + 1` with ideal sheaf `I` and a
quasi-coherent `𝒪_Y`-module `M`, if the conormal classes of the generators of every Koszul chart
form a frame of `i^* I` over the preimage of the chart, then
`ℰxt^{s+1}_Y(i_* 𝒪_X, M) ≅ i_* ℋom(⋀^{s+1}(i^* I), i^* M)`. -/
theorem nonempty_sheafExt_iso_of_isLocalFrame_conormalSection
    (h : IsKoszulRegularImmersion i (s + 1)) (M : Y.Modules) [M.IsQuasicoherent]
    (hc : haveI := h.isClosedImmersion
      ∀ (V : Y.Opens) (c : KoszulChart i (s + 1) V),
        IsLocalFrame (R := X.sheaf) ((Scheme.Modules.pullback i).obj
          (closedImmersionIdealSheaf i)) (i ⁻¹ᵁ V) (fun j => c.conormalSection j)) :
    Nonempty ((Ringed.sheafExt (R := Y.sheaf) ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf)) (s + 1)).obj M ≅
        (Scheme.Modules.pushforward i).obj (moduleSheafHom (R := X.sheaf)
          (moduleSheafExteriorPower (R := X.sheaf) (s + 1)
            ((Scheme.Modules.pullback i).obj (closedImmersionIdealSheaf i)))
          ((Scheme.Modules.pullback i).obj M))) := by
  have := h.isClosedImmersion
  refine nonempty_sheafExt_iso_of_frames M _ (fun V c => c.conormalFrame)
    (fun V c => c.isLocalFrame_conormalFrame (hc V c))
    (fun V c W b hb => c.conormalFrame_restrict W b hb)
    (fun V c g hIg hfg Q hg => c.conormalFrame_of_eq_vecMul g hIg hfg Q hg) fun y => ?_
  obtain ⟨U, hyU, f, hI, hf⟩ := h.exists_isKoszulRegular y
  exact ⟨U, ⟨U.2, f, hI, hf⟩, hyU⟩

end KoszulTarget

end Hartshorne
