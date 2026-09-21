import Hartshorne.Rational.BlowingUpVariety
import Hartshorne.Rational.BirationalCriterion
import Hartshorne.Rational.HypersurfaceComplement
import Hartshorne.Morphism.OpenSubvariety

/-!
# The blow-up projection and its inverse away from the origin

Hartshorne, *Algebraic Geometry*, I.4, pp. 28–29.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {σ : Type u} [Finite σ] [DecidableEq σ] [Nonempty σ]

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
private theorem blowupSet_subset_ambient :
    blowupSet (k := k) (σ := σ) ⊆ blowupAmbient (k := k) (σ := σ) :=
  Set.inter_subset_left

private noncomputable abbrev fullChartNonempty :
    ((Set.univ : Set (ProjectiveSpace k (Option σ))) ∩ standardChart none).Nonempty :=
  ⟨chartInv none 0,
    Set.mem_inter (Set.mem_univ _) (chartInv_mem_standardChart none 0)⟩

private noncomputable abbrev hAffineChart :
    IsQuasiProjVariety (BlowupAffineChart (k := k) (σ := σ)) :=
  isQuasiProjVariety_standardChart k none

private noncomputable abbrev hProjectiveSpace :
    IsQuasiProjVariety (Set.univ : Set (ProjectiveSpace k σ)) :=
  (isProjVariety_univ (k := k) (σ := σ)).isQuasiProjVariety

private noncomputable abbrev hBlowupAmbient :
    IsQuasiProjVariety (blowupAmbient (k := k) (σ := σ)) :=
  isQuasiProjVariety_segreProduct
    (hAffineChart (k := k) (σ := σ))
    (hProjectiveSpace (k := k) (σ := σ))

private noncomputable abbrev hFullChart :
    IsQuasiProjVariety
      ((Set.univ : Set (ProjectiveSpace k (Option σ))) ∩ standardChart none) :=
  isQuasiProjVariety_inter_standardChart k none
    (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
    (fullChartNonempty (k := k) (σ := σ))

/-- The inclusion from the chosen model of the affine chart into the chart
model used by `chartHom`. -/
noncomputable def affineChartToFullChart :
    VarietyHom
      (Variety.ofQuasiProjective (hAffineChart (k := k) (σ := σ)))
      (Variety.ofQuasiProjective (hFullChart (k := k) (σ := σ))) :=
  inclHom (hFullChart (k := k) (σ := σ))
    (hAffineChart (k := k) (σ := σ))
    (fun _P hP => ⟨Set.mem_univ _, hP⟩)

/-- Projection of the blow-up to the affine chart.  The output is the native
chart target, canonically isomorphic to affine `σ`-space. -/
noncomputable def blowupProjection
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    VarietyHom
      (Variety.ofQuasiProjective hBlow)
      (chartTarget k none
        (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
        (fullChartNonempty (k := k) (σ := σ))) :=
  (chartHom k none
      (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
      (fullChartNonempty (k := k) (σ := σ))).comp
    ((affineChartToFullChart (k := k) (σ := σ)).comp
      ((segreProductFstHom
          (hAffineChart (k := k) (σ := σ))
          (hBlowupAmbient (k := k) (σ := σ))).comp
        (inclHom (hBlowupAmbient (k := k) (σ := σ)) hBlow
          (blowupSet_subset_ambient (k := k) (σ := σ)))))

/-- Forget the impossible `none` coordinate. -/
def eraseNone (y : {j : Option σ // j ≠ none} → k) : σ → k :=
  fun a => y ⟨some a, by simp⟩

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
@[simp]
theorem eraseNone_blowupOptionCoordinates (x : σ → k) :
    eraseNone (blowupOptionCoordinates x) = x := by
  funext a
  simp [eraseNone]

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
@[simp]
theorem blowupOptionCoordinates_eraseNone (y : {j : Option σ // j ≠ none} → k) :
    blowupOptionCoordinates (eraseNone y) = y := by
  funext j
  rcases j with ⟨_ | a, h⟩
  · exact False.elim (h rfl)
  · simp [eraseNone]

private noncomputable abbrev hAffineSpace :
    IsQuasiAffineVariety (Set.univ : Set (σ → k)) :=
  (affineSpace_isAffineVariety (k := k) (σ := σ)).isQuasiAffineVariety

private noncomputable abbrev hChartTarget :
    IsQuasiAffineVariety
      (chartMap none ''
        ((Set.univ : Set (ProjectiveSpace k (Option σ))) ∩ standardChart none)) :=
  isQuasiAffineVariety_chartMap_image none
    (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
    (fullChartNonempty (k := k) (σ := σ))

omit [IsAlgClosed k] in
private theorem affineCoordinate_isGlobalRegular
    {ι : Type u} [Finite ι] {Y : Set (ι → k)}
    (hY : IsQuasiAffineVariety Y) (a : ι) :
    (Variety.ofQuasiAffine hY).IsGlobalRegular (fun y => y.1 a) := by
  intro _
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, X a, 1, by simp, by simp⟩

/-- The underlying reindexing from the chart target to literal affine space. -/
def chartTargetToAffineFun :
    (chartTarget k none
      (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
      (fullChartNonempty (k := k) (σ := σ))).carrier →
      (Set.univ : Set (σ → k)) :=
  fun y => ⟨eraseNone y.1, Set.mem_univ _⟩

theorem exists_chartTargetToAffineHom :
    ∃ F : VarietyHom
      (chartTarget k none
        (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
        (fullChartNonempty (k := k) (σ := σ)))
      (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))),
      F.toFun = chartTargetToAffineFun (k := k) (σ := σ) := by
  apply (exists_varietyHom_iff_coords_regular
    (hAffineSpace (k := k) (σ := σ))
    (chartTargetToAffineFun (k := k) (σ := σ))).2
  intro a
  simpa [chartTargetToAffineFun, eraseNone] using
    (affineCoordinate_isGlobalRegular
      (hChartTarget (k := k) (σ := σ)) ⟨some a, by simp⟩)

/-- The chart target reindexed to literal affine `σ`-space. -/
noncomputable def chartTargetToAffine :
    VarietyHom
      (chartTarget k none
        (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
        (fullChartNonempty (k := k) (σ := σ)))
      (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))) :=
  Classical.choose (exists_chartTargetToAffineHom (k := k) (σ := σ))

theorem chartTargetToAffine_apply
    (y : (chartTarget k none
      (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
      (fullChartNonempty (k := k) (σ := σ))).carrier) :
    (chartTargetToAffine (k := k) (σ := σ) y).1 = eraseNone y.1 := by
  exact congrArg Subtype.val
    (congrFun (Classical.choose_spec
      (exists_chartTargetToAffineHom (k := k) (σ := σ))) y)

/-- Reindex literal affine coordinates into the native chart target. -/
noncomputable def affineToChartTargetFun :
    (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).carrier →
      (chartTarget k none
        (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
        (fullChartNonempty (k := k) (σ := σ))).carrier :=
  fun x => ⟨blowupOptionCoordinates x.1, by
    refine ⟨chartInv none (blowupOptionCoordinates x.1), ?_, ?_⟩
    · exact ⟨Set.mem_univ _, chartInv_mem_standardChart none _⟩
    · exact chartMap_chartInv none (blowupOptionCoordinates x.1)⟩

theorem exists_affineToChartTargetHom :
    ∃ F : VarietyHom
      (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ)))
      (chartTarget k none
        (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
        (fullChartNonempty (k := k) (σ := σ))),
      F.toFun = affineToChartTargetFun (k := k) (σ := σ) := by
  apply (exists_varietyHom_iff_coords_regular
    (hChartTarget (k := k) (σ := σ))
    (affineToChartTargetFun (k := k) (σ := σ))).2
  rintro ⟨_ | a, h⟩
  · exact False.elim (h rfl)
  · simpa [affineToChartTargetFun, blowupOptionCoordinates] using
      (affineCoordinate_isGlobalRegular
        (hAffineSpace (k := k) (σ := σ)) a)

noncomputable def affineToChartTarget :
    VarietyHom
      (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ)))
      (chartTarget k none
        (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
        (fullChartNonempty (k := k) (σ := σ))) :=
  Classical.choose (exists_affineToChartTargetHom (k := k) (σ := σ))

theorem affineToChartTarget_apply
    (x : (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).carrier) :
    (affineToChartTarget (k := k) (σ := σ) x).1 = blowupOptionCoordinates x.1 := by
  exact congrArg Subtype.val
    (congrFun (Classical.choose_spec
      (exists_affineToChartTargetHom (k := k) (σ := σ))) x)

/-- Literal affine space and the native target of the `none` chart are
isomorphic as varieties. -/
theorem isIso_chartTargetToAffine :
    (chartTargetToAffine (k := k) (σ := σ)).IsIso := by
  refine ⟨affineToChartTarget (k := k) (σ := σ), ?_, ?_⟩
  · apply VarietyHom.ext
    funext y
    apply Subtype.ext
    change (affineToChartTarget (k := k) (σ := σ)
      (chartTargetToAffine (k := k) (σ := σ) y)).1 = y.1
    have hto := chartTargetToAffine_apply (k := k) (σ := σ) y
    have hfrom := affineToChartTarget_apply (k := k) (σ := σ)
      (chartTargetToAffine (k := k) (σ := σ) y)
    calc
      _ = blowupOptionCoordinates
          (chartTargetToAffine (k := k) (σ := σ) y).1 := hfrom
      _ = blowupOptionCoordinates (eraseNone y.1) := congrArg blowupOptionCoordinates hto
      _ = y.1 := blowupOptionCoordinates_eraseNone y.1
  · apply VarietyHom.ext
    funext x
    apply Subtype.ext
    change (chartTargetToAffine (k := k) (σ := σ)
      (affineToChartTarget (k := k) (σ := σ) x)).1 = x.1
    have hfrom := affineToChartTarget_apply (k := k) (σ := σ) x
    have hto := chartTargetToAffine_apply (k := k) (σ := σ)
      (affineToChartTarget (k := k) (σ := σ) x)
    calc
      _ = eraseNone
          (affineToChartTarget (k := k) (σ := σ) x).1 := hto
      _ = eraseNone (blowupOptionCoordinates x.1) := congrArg eraseNone hfrom
      _ = x.1 := eraseNone_blowupOptionCoordinates x.1

/-- Projection to literal affine space. -/
noncomputable def blowupProjectionAffine
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    VarietyHom (Variety.ofQuasiProjective hBlow)
      (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))) :=
  (chartTargetToAffine (k := k) (σ := σ)).comp (blowupProjection hBlow)

/-- Affine space minus the origin. -/
def affinePuncturedOpen :
    Opens (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).carrier where
  carrier := {x | x.1 ≠ 0}
  is_open' := by
    let A := Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))
    have hopen (i : σ) : IsOpen {x : A.carrier | x.1 i ≠ 0} := by
      have hc := A.isClosed_zeroSet_of_isGlobalRegular
        (affineCoordinate_isGlobalRegular
          (hAffineSpace (k := k) (σ := σ)) i)
      simpa only [Set.compl_ofPred, not_not] using hc.isOpen_compl
    have heq : {x : A.carrier | x.1 ≠ 0} = ⋃ i : σ, {x | x.1 i ≠ 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      exact Function.ne_iff
    rw [heq]
    exact isOpen_iUnion hopen

private noncomputable def punctureVector : σ → k :=
  Pi.single (Classical.choice (inferInstance : Nonempty σ)) 1

omit [IsAlgClosed k] [Finite σ] in
private theorem punctureVector_ne_zero :
    punctureVector (k := k) (σ := σ) ≠ 0 := by
  intro h
  have ha := congrFun h (Classical.choice (inferInstance : Nonempty σ))
  simp [punctureVector] at ha

theorem affinePuncturedOpen_nonempty :
    ((affinePuncturedOpen (k := k) (σ := σ) : Opens
      (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).carrier) :
      Set (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).carrier).Nonempty :=
  ⟨⟨punctureVector (k := k) (σ := σ), Set.mem_univ _⟩,
    punctureVector_ne_zero (k := k) (σ := σ)⟩

private theorem puncturedAffineCoordinate_isGlobalRegular (a : σ) :
    ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
      (affinePuncturedOpen (k := k) (σ := σ))
      (affinePuncturedOpen_nonempty (k := k) (σ := σ))).IsGlobalRegular
      (fun x => x.1.1 a) := by
  let A := Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))
  let U := affinePuncturedOpen (k := k) (σ := σ)
  let hU := affinePuncturedOpen_nonempty (k := k) (σ := σ)
  have hcoord := affineCoordinate_isGlobalRegular
    (hAffineSpace (k := k) (σ := σ)) a
  exact (A.inclHom U hU).regular_comp ⊤
    (fun y : (⊤ : Opens A.carrier) => y.1.1 a) hcoord

/-- Projectivize a nonzero affine vector. -/
noncomputable def projectivizePuncturedFun :
    ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
      (affinePuncturedOpen (k := k) (σ := σ))
      (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier →
      (Set.univ : Set (ProjectiveSpace k σ)) :=
  fun x => ⟨Projectivization.mk k x.1.1 x.2, Set.mem_univ _⟩

/-- The map `x ↦ [x]` from punctured affine space to projective space is a
morphism. -/
theorem exists_projectivizePuncturedHom :
    ∃ F : VarietyHom
      ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
        (affinePuncturedOpen (k := k) (σ := σ))
        (affinePuncturedOpen_nonempty (k := k) (σ := σ)))
      (Variety.ofQuasiProjective (hProjectiveSpace (k := k) (σ := σ))),
      F.toFun = projectivizePuncturedFun (k := k) (σ := σ) := by
  apply (exists_varietyHom_iff_locally_chart_regular
    (hProjectiveSpace (k := k) (σ := σ))
    (projectivizePuncturedFun (k := k) (σ := σ))).2
  intro x
  obtain ⟨i, hi⟩ := Function.ne_iff.mp x.2
  let A := (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
    (affinePuncturedOpen (k := k) (σ := σ))
    (affinePuncturedOpen_nonempty (k := k) (σ := σ))
  have hci : A.IsGlobalRegular (fun z => z.1.1 i) :=
    puncturedAffineCoordinate_isGlobalRegular (k := k) (σ := σ) i
  let U : Opens A.carrier :=
    ⟨{z | z.1.1 i ≠ 0}, by
      have hc := A.isClosed_zeroSet_of_isGlobalRegular hci
      simpa only [Set.compl_ofPred, not_not] using hc.isOpen_compl⟩
  refine ⟨i, U, hi, ?_, ?_⟩
  · intro z
    change ¬ HomogeneousVanish (X i)
      (Projectivization.mk k z.1.1.1 z.1.2)
    rw [homogeneousVanish_X_iff z.1.2]
    exact z.2
  · intro l
    have hnum : (fun z : U => z.1.1.1 l.1) ∈ A.regular U :=
      (puncturedAffineCoordinate_isGlobalRegular (k := k) (σ := σ) l.1).restrict U
    have hden : (fun z : U => z.1.1.1 i) ∈ A.regular U := hci.restrict U
    rw [show (fun z : U =>
        chartMap i (projectivizePuncturedFun (k := k) (σ := σ) z.1).1 l) =
      fun z : U => z.1.1.1 l.1 / z.1.1.1 i by
        funext z
        exact chartMap_mk i z.1.2 l]
    exact A.regular_div hnum hden (fun z => z.2)

noncomputable def projectivizePuncturedHom :
    VarietyHom
      ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
        (affinePuncturedOpen (k := k) (σ := σ))
        (affinePuncturedOpen_nonempty (k := k) (σ := σ)))
      (Variety.ofQuasiProjective (hProjectiveSpace (k := k) (σ := σ))) :=
  Classical.choose (exists_projectivizePuncturedHom (k := k) (σ := σ))

theorem projectivizePuncturedHom_apply
    (x : ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
      (affinePuncturedOpen (k := k) (σ := σ))
      (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier) :
    (projectivizePuncturedHom (k := k) (σ := σ) x).1 =
      Projectivization.mk k x.1.1 x.2 := by
  exact congrArg Subtype.val (congrFun (Classical.choose_spec
    (exists_projectivizePuncturedHom (k := k) (σ := σ))) x)

/-- The standard-chart realization of literal affine space. -/
noncomputable def affineToStandardChart :
    VarietyHom
      (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ)))
      (Variety.ofQuasiProjective (hAffineChart (k := k) (σ := σ))) :=
  (inclHom (hAffineChart (k := k) (σ := σ))
      (hFullChart (k := k) (σ := σ)) Set.inter_subset_right).comp
    ((chartInvHom k none
      (isProjVariety_univ (k := k) (σ := Option σ)).isQuasiProjVariety
      (fullChartNonempty (k := k) (σ := σ))).comp
      (affineToChartTarget (k := k) (σ := σ)))

theorem affineToStandardChart_apply
    (x : (Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).carrier) :
    (affineToStandardChart (k := k) (σ := σ) x).1 =
      chartInv none (blowupOptionCoordinates x.1) := by
  change chartInv none (affineToChartTarget (k := k) (σ := σ) x).1 = _
  rw [affineToChartTarget_apply]

/-- First component of the inverse on punctured affine space. -/
noncomputable def puncturedToStandardChart :
    VarietyHom
      ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
        (affinePuncturedOpen (k := k) (σ := σ))
        (affinePuncturedOpen_nonempty (k := k) (σ := σ)))
      (Variety.ofQuasiProjective (hAffineChart (k := k) (σ := σ))) :=
  (affineToStandardChart (k := k) (σ := σ)).comp
    ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).inclHom
      (affinePuncturedOpen (k := k) (σ := σ))
      (affinePuncturedOpen_nonempty (k := k) (σ := σ)))

theorem puncturedToStandardChart_apply
    (x : ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
      (affinePuncturedOpen (k := k) (σ := σ))
      (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier) :
    (puncturedToStandardChart (k := k) (σ := σ) x).1 =
      chartInv none (blowupOptionCoordinates x.1.1) := by
  exact affineToStandardChart_apply (k := k) (σ := σ) x.1

section CodRestrict

variable {ι : Type u} [Finite ι] [DecidableEq ι]
variable {A : Variety k}
variable {Y Z : Set (ProjectiveSpace k ι)}

omit [IsAlgClosed k] [Finite ι] in
/-- A morphism to a quasi-projective ambient variety whose range lies in a
quasi-projective subset can be corestricted to that subset. -/
theorem exists_varietyHom_codRestrictProj
    (hY : IsQuasiProjVariety Y) (hZ : IsQuasiProjVariety Z)
    (f : VarietyHom A (Variety.ofQuasiProjective hY))
    (hf : ∀ x, (f x).1 ∈ Z) :
    ∃ g : VarietyHom A (Variety.ofQuasiProjective hZ),
      g.toFun = fun x => ⟨(f x).1, hf x⟩ := by
  apply (exists_varietyHom_iff_locally_chart_regular hZ
    (fun x => ⟨(f x).1, hf x⟩)).2
  intro x
  obtain ⟨i, U, hxU, hchart, hreg⟩ :=
    (exists_varietyHom_iff_locally_chart_regular hY f.toFun).1 ⟨f, rfl⟩ x
  exact ⟨i, U, hxU, hchart, hreg⟩

noncomputable def VarietyHom.codRestrictProj
    (hY : IsQuasiProjVariety Y) (hZ : IsQuasiProjVariety Z)
    (f : VarietyHom A (Variety.ofQuasiProjective hY))
    (hf : ∀ x, (f x).1 ∈ Z) :
    VarietyHom A (Variety.ofQuasiProjective hZ) :=
  Classical.choose (exists_varietyHom_codRestrictProj hY hZ f hf)

omit [IsAlgClosed k] [Finite ι] in
theorem VarietyHom.codRestrictProj_toFun
    (hY : IsQuasiProjVariety Y) (hZ : IsQuasiProjVariety Z)
    (f : VarietyHom A (Variety.ofQuasiProjective hY))
    (hf : ∀ x, (f x).1 ∈ Z) :
    (f.codRestrictProj hY hZ hf).toFun = fun x => ⟨(f x).1, hf x⟩ :=
  Classical.choose_spec (exists_varietyHom_codRestrictProj hY hZ f hf)

end CodRestrict

/-- The obvious lift `x ↦ (x,[x])` away from the origin, as a point of the
Segre ambient. -/
noncomputable def blowupInverseAmbientPoint (x : σ → k) (hx : x ≠ 0) :
    blowupAmbient (k := k) (σ := σ) :=
  segreProductMk
    (⟨chartInv none (blowupOptionCoordinates x), chartInv_mem_standardChart none _⟩ :
      BlowupAffineChart (k := k) (σ := σ))
    (⟨Projectivization.mk k x hx, Set.mem_univ _⟩ :
      (Set.univ : Set (ProjectiveSpace k σ)))

omit [IsAlgClosed k] [Finite σ] [Nonempty σ] in
theorem blowupInverseAmbientPoint_mem_zeroSet (x : σ → k) (hx : x ≠ 0) :
    (blowupInverseAmbientPoint (k := k) x hx).1 ∈
      projZeroSet (blowupEquations (k := k) (σ := σ)) := by
  intro f hf
  obtain ⟨a, b, rfl⟩ := hf
  change HomogeneousVanish (blowupEquation (k := k) a b)
    (segreMap (chartInv none (blowupOptionCoordinates x)) (Projectivization.mk k x hx))
  rw [show chartInv none (blowupOptionCoordinates x) =
      Projectivization.mk k (chartInvVec none (blowupOptionCoordinates x))
        (chartInvVec_ne_zero none (blowupOptionCoordinates x)) from rfl]
  rw [segreMap_mk_mk (chartInvVec_ne_zero none (blowupOptionCoordinates x)) hx]
  rw [homogeneousVanish_iff_of_isHomogeneous
    (blowupEquation_isHomogeneous (k := k) a b)
    (segreVector_ne_zero (chartInvVec_ne_zero none (blowupOptionCoordinates x)) hx)]
  simp [blowupEquation, segreVector, chartInvVec, blowupOptionCoordinates]
  ring

/-- The point `x ↦ (x,[x])` actually lands in the blow-up. -/
noncomputable def blowupInversePoint (x : σ → k) (hx : x ≠ 0) :
    blowupSet (k := k) (σ := σ) :=
  ⟨(blowupInverseAmbientPoint (k := k) x hx).1,
    (blowupInverseAmbientPoint (k := k) x hx).2,
    blowupInverseAmbientPoint_mem_zeroSet (k := k) x hx⟩

/-- The morphism `x ↦ (x,[x])` into the Segre-product ambient. -/
noncomputable def blowupInverseAmbientHom :
    VarietyHom
      ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
        (affinePuncturedOpen (k := k) (σ := σ))
        (affinePuncturedOpen_nonempty (k := k) (σ := σ)))
      (Variety.ofQuasiProjective (hBlowupAmbient (k := k) (σ := σ))) :=
  segreProductLiftHom
    (hAffineChart (k := k) (σ := σ))
    (hProjectiveSpace (k := k) (σ := σ))
    (hBlowupAmbient (k := k) (σ := σ))
    (puncturedToStandardChart (k := k) (σ := σ))
    (projectivizePuncturedHom (k := k) (σ := σ))

theorem blowupInverseAmbientHom_apply
    (x : ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
      (affinePuncturedOpen (k := k) (σ := σ))
      (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier) :
    blowupInverseAmbientHom (k := k) (σ := σ) x =
      blowupInverseAmbientPoint (k := k) x.1.1 x.2 := by
  unfold blowupInverseAmbientHom
  rw [segreProductLiftHom_toFun]
  apply Subtype.ext
  change segreMap
      (puncturedToStandardChart (k := k) (σ := σ) x).1
      (projectivizePuncturedHom (k := k) (σ := σ) x).1 =
    segreMap (chartInv none (blowupOptionCoordinates x.1.1))
      (Projectivization.mk k x.1.1 x.2)
  rw [puncturedToStandardChart_apply, projectivizePuncturedHom_apply]

theorem blowupInverseAmbientHom_mem
    (x : ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
      (affinePuncturedOpen (k := k) (σ := σ))
      (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier) :
    (blowupInverseAmbientHom (k := k) (σ := σ) x).1 ∈
      blowupSet (k := k) (σ := σ) := by
  rw [blowupInverseAmbientHom_apply]
  exact ⟨(blowupInverseAmbientPoint (k := k) x.1.1 x.2).2,
    blowupInverseAmbientPoint_mem_zeroSet (k := k) x.1.1 x.2⟩

/-- The inverse morphism away from the origin, corestricted to the blow-up. -/
noncomputable def blowupInverseHom
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    VarietyHom
      ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
        (affinePuncturedOpen (k := k) (σ := σ))
        (affinePuncturedOpen_nonempty (k := k) (σ := σ)))
      (Variety.ofQuasiProjective hBlow) :=
  (blowupInverseAmbientHom (k := k) (σ := σ)).codRestrictProj
    (hBlowupAmbient (k := k) (σ := σ)) hBlow
    (blowupInverseAmbientHom_mem (k := k) (σ := σ))

theorem blowupInverseHom_apply
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ)))
    (x : ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
      (affinePuncturedOpen (k := k) (σ := σ))
      (affinePuncturedOpen_nonempty (k := k) (σ := σ))).carrier) :
    blowupInverseHom hBlow x =
      blowupInversePoint (k := k) x.1.1 x.2 := by
  apply Subtype.ext
  rw [show (blowupInverseHom hBlow).toFun = fun x =>
      ⟨(blowupInverseAmbientHom (k := k) (σ := σ) x).1,
        blowupInverseAmbientHom_mem (k := k) (σ := σ) x⟩ from
    VarietyHom.codRestrictProj_toFun
      (hBlowupAmbient (k := k) (σ := σ)) hBlow
      (blowupInverseAmbientHom (k := k) (σ := σ))
      (blowupInverseAmbientHom_mem (k := k) (σ := σ))]
  change (blowupInverseAmbientHom (k := k) (σ := σ) x).1 =
    (blowupInverseAmbientPoint (k := k) x.1.1 x.2).1
  exact congrArg Subtype.val (blowupInverseAmbientHom_apply (k := k) (σ := σ) x)

/-- The ambient product point underlying a flat blow-up point. -/
def blowupAsAmbient (R : blowupSet (k := k) (σ := σ)) :
    blowupAmbient (k := k) (σ := σ) :=
  ⟨R.1, R.2.1⟩

noncomputable def blowupFirst (R : blowupSet (k := k) (σ := σ)) :
    BlowupAffineChart (k := k) (σ := σ) :=
  segreProductFst (blowupAsAmbient R)

noncomputable def blowupSecond (R : blowupSet (k := k) (σ := σ)) :
    ProjectiveSpace k σ :=
  (segreProductSnd (blowupAsAmbient R)).1

theorem blowupProjectionAffine_apply
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ)))
    (R : (Variety.ofQuasiProjective hBlow).carrier) :
    (blowupProjectionAffine hBlow R).1 =
      eraseNone (chartMap none (blowupFirst R).1) := by
  rw [show (blowupProjectionAffine hBlow).toFun =
      (chartTargetToAffine (k := k) (σ := σ)).toFun ∘
        (blowupProjection hBlow).toFun from rfl]
  change (chartTargetToAffine (k := k) (σ := σ)
    (blowupProjection hBlow R)).1 = _
  rw [chartTargetToAffine_apply]
  congr 1
  unfold blowupProjection VarietyHom.comp affineChartToFullChart chartHom chartFun inclHom
  dsimp only [Function.comp_apply, blowupFirst, blowupAsAmbient]
  change chartMap none
    (((segreProductFstHom
      (hAffineChart (k := k) (σ := σ))
      (hBlowupAmbient (k := k) (σ := σ))).toFun
      (⟨R.1, R.2.1⟩ : blowupAmbient (k := k) (σ := σ))).1) =
    chartMap none (segreProductFst
      (⟨R.1, R.2.1⟩ : blowupAmbient (k := k) (σ := σ))).1
  rw [segreProductFstHom_toFun]

/-- The fibre of the affine blow-up projection over the zero vector is exactly
the exceptional fibre identified in `BlowingUpGeometry`. -/
theorem blowupProjectionAffine_eq_zero_iff
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ)))
    (R : blowupSet (k := k) (σ := σ)) :
    (blowupProjectionAffine hBlow R).1 = 0 ↔
      blowupFirst R = blowupOrigin (k := k) (σ := σ) := by
  let R' : (Variety.ofQuasiProjective hBlow).carrier := ⟨R.1, R.2⟩
  change (blowupProjectionAffine hBlow R').1 = 0 ↔ _
  rw [blowupProjectionAffine_apply]
  change eraseNone (chartMap none (blowupFirst R).1) = 0 ↔ _
  constructor
  · intro h
    apply (blowupSpatialVector_eq_zero_iff (blowupFirst R)).1
    funext i
    have hi := congrFun h i
    change (blowupFirst R).1.rep (some i) /
      (blowupFirst R).1.rep none = 0 at hi
    exact (div_eq_zero_iff.mp hi).resolve_right
      (rep_ne_zero_of_mem_standardChart (blowupFirst R).2)
  · intro h
    have hsp := (blowupSpatialVector_eq_zero_iff (blowupFirst R)).2 h
    funext i
    change (blowupFirst R).1.rep (some i) /
      (blowupFirst R).1.rep none = 0
    rw [show (blowupFirst R).1.rep (some i) = 0 from congrFun hsp i,
      zero_div]

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
theorem blowup_incidence_flat
    (R : blowupSet (k := k) (σ := σ)) (a b : σ) :
    (blowupFirst R).1.rep (some a) * (blowupSecond R).rep b =
      (blowupFirst R).1.rep (some b) * (blowupSecond R).rep a := by
  have hv := R.2.2 (blowupEquation (k := k) a b) ⟨a, b, rfl⟩
  change HomogeneousVanish (blowupEquation (k := k) a b)
    (blowupAsAmbient R).1 at hv
  rw [← segreMap_fst_snd (blowupAsAmbient R)] at hv
  change HomogeneousVanish (blowupEquation (k := k) a b)
    (Projectivization.mk k
      (segreVector (blowupFirst R).1.rep (blowupSecond R).rep)
      (segreVector_ne_zero (blowupFirst R).1.rep_nonzero
        (blowupSecond R).rep_nonzero)) at hv
  rw [homogeneousVanish_iff_of_isHomogeneous
    (blowupEquation_isHomogeneous (k := k) a b)
    (segreVector_ne_zero (blowupFirst R).1.rep_nonzero
      (blowupSecond R).rep_nonzero)] at hv
  simpa [blowupEquation, segreVector, sub_eq_zero] using hv

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
theorem blowup_chart_incidence_flat
    (R : blowupSet (k := k) (σ := σ)) (a b : σ) :
    eraseNone (chartMap none (blowupFirst R).1) a * (blowupSecond R).rep b =
      eraseNone (chartMap none (blowupFirst R).1) b * (blowupSecond R).rep a := by
  have hnone : (blowupFirst R).1.rep none ≠ 0 :=
    rep_ne_zero_of_mem_standardChart (blowupFirst R).2
  change ((blowupFirst R).1.rep (some a) / (blowupFirst R).1.rep none) *
      (blowupSecond R).rep b =
    ((blowupFirst R).1.rep (some b) / (blowupFirst R).1.rep none) *
      (blowupSecond R).rep a
  field_simp
  exact blowup_incidence_flat R a b

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
theorem projectivization_eq_of_raw_minors
    {x : σ → k} (hx : x ≠ 0) (Q : ProjectiveSpace k σ)
    (h : ∀ a b, x a * Q.rep b = x b * Q.rep a) :
    Projectivization.mk k x hx = Q := by
  let P := Projectivization.mk k x hx
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep k x hx
  have hminor : ∀ a b, P.rep a * Q.rep b = P.rep b * Q.rep a := by
    intro a b
    have ha := congrFun hc a
    have hb := congrFun hc b
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at ha hb
    rw [← ha, ← hb, mul_assoc, mul_assoc]
    exact congrArg ((c : k) * ·) (h a b)
  obtain ⟨a, ha⟩ := Function.ne_iff.mp P.rep_nonzero
  exact eq_of_minors_eq_zero ha hminor

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
theorem affineBlowup_ext {R S : blowupSet (k := k) (σ := σ)}
    (h₁ : blowupFirst R = blowupFirst S)
    (h₂ : blowupSecond R = blowupSecond S) : R = S := by
  apply Subtype.ext
  change (blowupAsAmbient R).1 = (blowupAsAmbient S).1
  rw [← segreMap_fst_snd (blowupAsAmbient R),
    ← segreMap_fst_snd (blowupAsAmbient S)]
  simpa [blowupFirst, blowupSecond] using
    congrArg₂ (fun P Q => segreMap P.1 Q) h₁ h₂

omit [IsAlgClosed k] [Finite σ] [Nonempty σ] in
@[simp]
theorem blowupFirst_inversePoint (x : σ → k) (hx : x ≠ 0) :
    blowupFirst (blowupInversePoint (k := k) x hx) =
      (⟨chartInv none (blowupOptionCoordinates x), chartInv_mem_standardChart none _⟩ :
        BlowupAffineChart (k := k) (σ := σ)) := by
  let P : BlowupAffineChart (k := k) (σ := σ) :=
    ⟨chartInv none (blowupOptionCoordinates x), chartInv_mem_standardChart none _⟩
  let Q : (Set.univ : Set (ProjectiveSpace k σ)) :=
    ⟨Projectivization.mk k x hx, Set.mem_univ _⟩
  have hA : blowupAsAmbient (blowupInversePoint (k := k) x hx) =
      segreProductMk P Q := by
    apply Subtype.ext
    rfl
  rw [blowupFirst, hA, segreProductFst_mk]

omit [IsAlgClosed k] [Finite σ] [Nonempty σ] in
@[simp]
theorem blowupSecond_inversePoint (x : σ → k) (hx : x ≠ 0) :
    blowupSecond (blowupInversePoint (k := k) x hx) =
      Projectivization.mk k x hx := by
  let P : BlowupAffineChart (k := k) (σ := σ) :=
    ⟨chartInv none (blowupOptionCoordinates x), chartInv_mem_standardChart none _⟩
  let Q : (Set.univ : Set (ProjectiveSpace k σ)) :=
    ⟨Projectivization.mk k x hx, Set.mem_univ _⟩
  have hA : blowupAsAmbient (blowupInversePoint (k := k) x hx) =
      segreProductMk P Q := by
    apply Subtype.ext
    rfl
  change (segreProductSnd (blowupAsAmbient
    (blowupInversePoint (k := k) x hx))).1 = _
  rw [hA, segreProductSnd_mk]

/-- The explicit inverse recovers every point of the blow-up lying over a
nonzero affine point. -/
theorem blowupInversePoint_projection
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ)))
    (R : (Variety.ofQuasiProjective hBlow).carrier)
    (hR : (blowupProjectionAffine hBlow R).1 ≠ 0) :
    blowupInversePoint (k := k) (blowupProjectionAffine hBlow R).1 hR = R := by
  apply affineBlowup_ext
  · rw [blowupFirst_inversePoint, blowupProjectionAffine_apply]
    apply Subtype.ext
    rw [blowupOptionCoordinates_eraseNone]
    exact chartInv_chartMap (blowupFirst R).2
  · rw [blowupSecond_inversePoint]
    apply projectivization_eq_of_raw_minors hR
    intro a b
    rw [blowupProjectionAffine_apply]
    exact blowup_chart_incidence_flat R a b

theorem blowupProjectionAffine_inversePoint
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ)))
    (x : σ → k) (hx : x ≠ 0) :
    (blowupProjectionAffine hBlow (blowupInversePoint (k := k) x hx)).1 = x := by
  let R : (Variety.ofQuasiProjective hBlow).carrier :=
    ⟨(blowupInversePoint (k := k) x hx).1,
      (blowupInversePoint (k := k) x hx).2⟩
  change (blowupProjectionAffine hBlow R).1 = x
  rw [blowupProjectionAffine_apply]
  change eraseNone
    (chartMap none (blowupFirst (blowupInversePoint (k := k) x hx)).1) = x
  rw [blowupFirst_inversePoint]
  simp

/-- The complement of the exceptional fibre, defined as the preimage of
punctured affine space under the blow-up projection. -/
noncomputable def blowupPuncturedOpen
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    Opens (Variety.ofQuasiProjective hBlow).carrier :=
  Opens.comap
    ⟨(blowupProjectionAffine hBlow).toFun,
      (blowupProjectionAffine hBlow).continuous_toFun⟩
    (affinePuncturedOpen (k := k) (σ := σ))

theorem blowupPuncturedOpen_nonempty
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    ((blowupPuncturedOpen hBlow : Opens
      (Variety.ofQuasiProjective hBlow).carrier) :
      Set (Variety.ofQuasiProjective hBlow).carrier).Nonempty := by
  let x := punctureVector (k := k) (σ := σ)
  let hx := punctureVector_ne_zero (k := k) (σ := σ)
  refine ⟨blowupInversePoint (k := k) x hx, ?_⟩
  change (blowupProjectionAffine hBlow
    (blowupInversePoint (k := k) x hx)).1 ≠ 0
  rw [blowupProjectionAffine_inversePoint]
  exact hx

/-- The blow-up projection restricted away from the exceptional fibre. -/
noncomputable def blowupProjectionPuncturedHom
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    VarietyHom
      ((Variety.ofQuasiProjective hBlow).restrict
        (blowupPuncturedOpen hBlow) (blowupPuncturedOpen_nonempty hBlow))
      ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
        (affinePuncturedOpen (k := k) (σ := σ))
        (affinePuncturedOpen_nonempty (k := k) (σ := σ))) :=
  VarietyHom.liftToRestrict
    ((blowupProjectionAffine hBlow).comp
      ((Variety.ofQuasiProjective hBlow).inclHom
        (blowupPuncturedOpen hBlow) (blowupPuncturedOpen_nonempty hBlow)))
    (affinePuncturedOpen (k := k) (σ := σ))
    (affinePuncturedOpen_nonempty (k := k) (σ := σ))
    (fun R => R.2)

/-- The inverse `x ↦ (x,[x])`, now landing in the nonexceptional open. -/
noncomputable def blowupInversePuncturedHom
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    VarietyHom
      ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
        (affinePuncturedOpen (k := k) (σ := σ))
        (affinePuncturedOpen_nonempty (k := k) (σ := σ)))
      ((Variety.ofQuasiProjective hBlow).restrict
        (blowupPuncturedOpen hBlow) (blowupPuncturedOpen_nonempty hBlow)) :=
  VarietyHom.liftToRestrict (blowupInverseHom hBlow)
    (blowupPuncturedOpen hBlow) (blowupPuncturedOpen_nonempty hBlow)
    (fun x => by
      change (blowupProjectionAffine hBlow (blowupInverseHom hBlow x)).1 ≠ 0
      rw [blowupInverseHom_apply]
      have hp := blowupProjectionAffine_inversePoint hBlow x.1.1 x.2
      exact hp.symm ▸ x.2)

theorem blowupProjectionPunctured_comp_inverse
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    (blowupProjectionPuncturedHom hBlow).comp
      (blowupInversePuncturedHom hBlow) =
        VarietyHom.id
          ((Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ))).restrict
            (affinePuncturedOpen (k := k) (σ := σ))
            (affinePuncturedOpen_nonempty (k := k) (σ := σ))) := by
  apply VarietyHom.ext
  funext x
  apply Subtype.ext
  apply Subtype.ext
  change (blowupProjectionAffine hBlow (blowupInverseHom hBlow x)).1 = x.1.1
  rw [blowupInverseHom_apply]
  exact blowupProjectionAffine_inversePoint hBlow x.1.1 x.2

theorem blowupInverse_comp_projectionPunctured
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    (blowupInversePuncturedHom hBlow).comp
      (blowupProjectionPuncturedHom hBlow) =
        VarietyHom.id
          ((Variety.ofQuasiProjective hBlow).restrict
            (blowupPuncturedOpen hBlow) (blowupPuncturedOpen_nonempty hBlow)) := by
  apply VarietyHom.ext
  funext R
  apply Subtype.ext
  change blowupInverseHom hBlow
      (blowupProjectionPuncturedHom hBlow R) = R.1
  rw [blowupInverseHom_apply]
  exact blowupInversePoint_projection hBlow R.1 R.2

/-- Property (1): away from the origin, the blow-up projection is an
isomorphism. -/
theorem isIso_blowupProjectionPunctured
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    (blowupProjectionPuncturedHom hBlow).IsIso :=
  ⟨blowupInversePuncturedHom hBlow,
    blowupInverse_comp_projectionPunctured hBlow,
    blowupProjectionPunctured_comp_inverse hBlow⟩

/-- The blow-up of affine space at the origin is birational to affine space. -/
theorem birational_affineBlowup
    (hBlow : IsQuasiProjVariety (blowupSet (k := k) (σ := σ))) :
    Birational
      ⟨Variety.ofQuasiProjective hBlow,
        isSeparated_ofQuasiProjective hBlow⟩
      ⟨Variety.ofQuasiAffine (hAffineSpace (k := k) (σ := σ)),
        RationalMapFunctionField.isSeparated_ofQuasiAffine
          (hAffineSpace (k := k) (σ := σ))⟩ := by
  apply (birational_iff_hasIsomorphicOpenSubsets _ _).2
  exact ⟨blowupPuncturedOpen hBlow, blowupPuncturedOpen_nonempty hBlow,
    affinePuncturedOpen (k := k) (σ := σ),
    affinePuncturedOpen_nonempty (k := k) (σ := σ),
    blowupProjectionPuncturedHom hBlow,
    isIso_blowupProjectionPunctured hBlow⟩

end Hartshorne
