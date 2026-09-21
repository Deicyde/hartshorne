import Hartshorne.Rational.ProductVariety
import Hartshorne.Rational.Minors

/-!
Geometry of the blow-up of affine space at the origin.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k] {σ : Type u}

/-- Affine `σ`-space, represented by the `none` chart of
`ProjectiveSpace k (Option σ)`. -/
abbrev BlowupAffineChart :=
  (standardChart (none : Option σ) : Set (ProjectiveSpace k (Option σ)))

/-- The homogeneous linear incidence equation in the Segre ambient space.
On a Segre point it reads `xᵢ yⱼ - xⱼ yᵢ`. -/
noncomputable def blowupEquation (i j : σ) :
    MvPolynomial ((Option σ) × σ) k :=
  X (some i, j) - X (some j, i)

theorem blowupEquation_isHomogeneous (i j : σ) :
    (blowupEquation (k := k) i j).IsHomogeneous 1 := by
  exact (isHomogeneous_X k (some i, j)).sub
    (isHomogeneous_X k (some j, i))

/-- All incidence equations. -/
def blowupEquations : Set (MvPolynomial ((Option σ) × σ) k) :=
  {f | ∃ i j : σ, blowupEquation (k := k) i j = f}

theorem blowupEquations_isHomogeneousSet :
    IsHomogeneousSet (blowupEquations (k := k) (σ := σ)) := by
  rintro f ⟨i, j, rfl⟩
  exact ⟨1, blowupEquation_isHomogeneous i j⟩

/-- The projectively closed incidence locus in the Segre ambient space. -/
def blowupIncidence : Set (ProjectiveSpace k ((Option σ) × σ)) :=
  projZeroSet (blowupEquations (k := k) (σ := σ))

theorem isProjAlgebraicSet_blowupIncidence :
    IsProjAlgebraicSet (blowupIncidence (k := k) (σ := σ)) :=
  ⟨blowupEquations (k := k) (σ := σ),
    blowupEquations_isHomogeneousSet, rfl⟩

theorem isClosed_blowupIncidence :
    IsClosed (blowupIncidence (k := k) (σ := σ)) :=
  isClosed_iff_isProjAlgebraicSet.2 isProjAlgebraicSet_blowupIncidence

theorem segreMap_mem_blowupIncidence_iff
    (P : ProjectiveSpace k (Option σ)) (Q : ProjectiveSpace k σ) :
    segreMap P Q ∈ blowupIncidence (k := k) (σ := σ) ↔
      ∀ i j : σ,
        P.rep (some i) * Q.rep j = P.rep (some j) * Q.rep i := by
  constructor
  · intro h i j
    have hv := h (blowupEquation (k := k) i j) ⟨i, j, rfl⟩
    change HomogeneousVanish (blowupEquation (k := k) i j)
      (Projectivization.mk k (segreVector P.rep Q.rep)
        (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)) at hv
    rw [homogeneousVanish_iff_of_isHomogeneous
      (blowupEquation_isHomogeneous i j)
      (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)] at hv
    simpa [blowupEquation, segreVector, sub_eq_zero] using hv
  · intro h f hf
    obtain ⟨i, j, rfl⟩ := hf
    change HomogeneousVanish (blowupEquation (k := k) i j)
      (Projectivization.mk k (segreVector P.rep Q.rep)
        (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero))
    rw [homogeneousVanish_iff_of_isHomogeneous
      (blowupEquation_isHomogeneous i j)
      (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)]
    simpa [blowupEquation, segreVector, sub_eq_zero] using h i j

/-- The ambient `A^σ × P^σ`, with the topology induced by the Segre
embedding (not the ordinary product topology). -/
def blowupAmbient : Set (ProjectiveSpace k ((Option σ) × σ)) :=
  segreProduct
    (standardChart (none : Option σ) : Set (ProjectiveSpace k (Option σ)))
    (Set.univ : Set (ProjectiveSpace k σ))

/-- Flat ambient-projective presentation, suitable for
`Variety.ofQuasiProjective`. -/
def blowupSet : Set (ProjectiveSpace k ((Option σ) × σ)) :=
  blowupAmbient (k := k) (σ := σ) ∩
    blowupIncidence (k := k) (σ := σ)

abbrev BlowupAmbientPoint := ↥(blowupAmbient (k := k) (σ := σ))

/-- The blow-up is the incidence locus, cut out inside the Segre product. -/
def blowupLocus : Set (BlowupAmbientPoint (k := k) (σ := σ)) :=
  {R | R.1 ∈ blowupIncidence (k := k) (σ := σ)}

abbrev BlowupPoint := ↥(blowupLocus (k := k) (σ := σ))

/-- The nested "closed in the product" and flat ambient-projective
presentations have the same points. -/
def blowupPointEquivFlat :
    BlowupPoint (k := k) (σ := σ) ≃
      ↥(blowupSet (k := k) (σ := σ)) where
  toFun R := ⟨R.1.1, R.1.2, R.2⟩
  invFun R := ⟨⟨R.1, R.2.1⟩, R.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The two presentations also carry the same induced topology. -/
def blowupPointHomeomorphFlat :
    BlowupPoint (k := k) (σ := σ) ≃ₜ
      ↥(blowupSet (k := k) (σ := σ)) where
  toEquiv := blowupPointEquivFlat
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The defining equations make the blow-up closed in `A^σ × P^σ`. -/
theorem isClosed_blowupLocus :
    IsClosed (blowupLocus (k := k) (σ := σ)) := by
  change IsClosed (Subtype.val ⁻¹' blowupIncidence (k := k) (σ := σ))
  exact isClosed_blowupIncidence.preimage continuous_subtype_val

/-- First (affine) projection. -/
noncomputable def blowupAffine (R : BlowupPoint (k := k) (σ := σ)) :
    BlowupAffineChart (k := k) (σ := σ) :=
  segreProductFst R.1

/-- Second (direction) projection. -/
noncomputable def blowupDirection (R : BlowupPoint (k := k) (σ := σ)) :
    ProjectiveSpace k σ :=
  (segreProductSnd R.1).1

theorem blowup_incidence (R : BlowupPoint (k := k) (σ := σ)) (i j : σ) :
    (blowupAffine R).1.rep (some i) * (blowupDirection R).rep j =
      (blowupAffine R).1.rep (some j) * (blowupDirection R).rep i := by
  apply (segreMap_mem_blowupIncidence_iff
    (blowupAffine R).1 (blowupDirection R)).1
  change segreMap (segreProductFst R.1).1 (segreProductSnd R.1).1 ∈
    blowupIncidence (k := k) (σ := σ)
  rw [segreMap_fst_snd R.1]
  exact R.2

/-- Construct a blow-up point from an affine point, a direction, and the
incidence equations. -/
noncomputable def blowupMk
    (P : BlowupAffineChart (k := k) (σ := σ))
    (Q : ProjectiveSpace k σ)
    (h : ∀ i j : σ,
      P.1.rep (some i) * Q.rep j = P.1.rep (some j) * Q.rep i) :
    BlowupPoint (k := k) (σ := σ) :=
  ⟨segreProductMk P ⟨Q, Set.mem_univ Q⟩,
    (segreMap_mem_blowupIncidence_iff P.1 Q).2 h⟩

@[simp]
theorem blowupAffine_mk
    (P : BlowupAffineChart (k := k) (σ := σ))
    (Q : ProjectiveSpace k σ)
    (h : ∀ i j : σ,
      P.1.rep (some i) * Q.rep j = P.1.rep (some j) * Q.rep i) :
    blowupAffine (blowupMk P Q h) = P := by
  simp [blowupAffine, blowupMk]

@[simp]
theorem blowupDirection_mk
    (P : BlowupAffineChart (k := k) (σ := σ))
    (Q : ProjectiveSpace k σ)
    (h : ∀ i j : σ,
      P.1.rep (some i) * Q.rep j = P.1.rep (some j) * Q.rep i) :
    blowupDirection (blowupMk P Q h) = Q := by
  simp [blowupDirection, blowupMk]

theorem blowupPoint_ext {R S : BlowupPoint (k := k) (σ := σ)}
    (h₁ : blowupAffine R = blowupAffine S)
    (h₂ : blowupDirection R = blowupDirection S) : R = S := by
  apply Subtype.ext
  apply Subtype.ext
  rw [← segreMap_fst_snd R.1, ← segreMap_fst_snd S.1]
  simpa [blowupAffine, blowupDirection] using
    congrArg₂ (fun P Q => segreMap P.1 Q) h₁ h₂

section OriginAndFibres

variable [DecidableEq σ]

/-- The origin in the standard affine chart. -/
noncomputable def blowupOrigin : BlowupAffineChart (k := k) (σ := σ) :=
  ⟨chartInv (none : Option σ) 0,
    chartInv_mem_standardChart (none : Option σ) 0⟩

/-- The vector of nonconstant homogeneous coordinates of an affine-chart
point. It is nonzero exactly away from the origin. -/
noncomputable def blowupSpatialVector
    (P : BlowupAffineChart (k := k) (σ := σ)) : σ → k :=
  fun i => P.1.rep (some i)

theorem blowupSpatialVector_origin :
    blowupSpatialVector (blowupOrigin (k := k) (σ := σ)) = 0 := by
  funext i
  have hratio := congrFun
    (chartMap_chartInv (k := k) (none : Option σ)
      (0 : {j : Option σ // j ≠ none} → k))
    ⟨some i, by simp⟩
  change (chartInv (none : Option σ)
      (0 : {j : Option σ // j ≠ none} → k)).rep (some i) /
      (chartInv (none : Option σ)
        (0 : {j : Option σ // j ≠ none} → k)).rep none = 0 at hratio
  have hden : (chartInv (none : Option σ)
      (0 : {j : Option σ // j ≠ none} → k)).rep none ≠ 0 :=
    rep_ne_zero_of_mem_standardChart
      (chartInv_mem_standardChart (none : Option σ)
        (0 : {j : Option σ // j ≠ none} → k))
  exact (div_eq_zero_iff.mp hratio).resolve_right hden

theorem blowupSpatialVector_eq_zero_iff
    (P : BlowupAffineChart (k := k) (σ := σ)) :
    blowupSpatialVector P = 0 ↔ P = blowupOrigin := by
  constructor
  · intro hP
    have hchart : chartMap (none : Option σ) P.1 = 0 := by
      funext j
      rcases j with ⟨j, hj⟩
      cases j with
      | none => exact (hj rfl).elim
      | some i =>
          have hi := congrFun hP i
          change P.1.rep (some i) = 0 at hi
          change P.1.rep (some i) / P.1.rep none = 0
          rw [hi, zero_div]
    apply Subtype.ext
    rw [← chartInv_chartMap P.2, hchart]
    rfl
  · rintro rfl
    exact blowupSpatialVector_origin

theorem blowupSpatialVector_ne_zero_iff
    (P : BlowupAffineChart (k := k) (σ := σ)) :
    blowupSpatialVector P ≠ 0 ↔ P ≠ blowupOrigin := by
  rw [not_iff_not]
  exact blowupSpatialVector_eq_zero_iff P

theorem blowupOrigin_incidence (Q : ProjectiveSpace k σ) :
    ∀ i j : σ,
      (blowupOrigin (k := k) (σ := σ)).1.rep (some i) * Q.rep j =
        (blowupOrigin (k := k) (σ := σ)).1.rep (some j) * Q.rep i := by
  intro i j
  have hi := congrFun (blowupSpatialVector_origin (k := k) (σ := σ)) i
  have hj := congrFun (blowupSpatialVector_origin (k := k) (σ := σ)) j
  change (blowupOrigin (k := k) (σ := σ)).1.rep (some i) = 0 at hi
  change (blowupOrigin (k := k) (σ := σ)).1.rep (some j) = 0 at hj
  rw [hi, hj]
  simp

/-- Every projective direction gives a point of the exceptional fibre. -/
noncomputable def exceptionalPoint (Q : ProjectiveSpace k σ) :
    BlowupPoint (k := k) (σ := σ) :=
  blowupMk blowupOrigin Q (blowupOrigin_incidence Q)

@[simp]
theorem blowupAffine_exceptionalPoint (Q : ProjectiveSpace k σ) :
    blowupAffine (exceptionalPoint (k := k) Q) = blowupOrigin := by
  simp [exceptionalPoint]

@[simp]
theorem blowupDirection_exceptionalPoint (Q : ProjectiveSpace k σ) :
    blowupDirection (exceptionalPoint (k := k) Q) = Q := by
  simp [exceptionalPoint]

/-- The exceptional fibre as a subtype. -/
def ExceptionalFibre : Set (BlowupPoint (k := k) (σ := σ)) :=
  {R | blowupAffine R = blowupOrigin}

/-- Property (2): the fibre over the origin is exactly `P^σ`. -/
noncomputable def exceptionalFibreEquiv :
    ↥(ExceptionalFibre (k := k) (σ := σ)) ≃ ProjectiveSpace k σ where
  toFun R := blowupDirection R.1
  invFun Q := ⟨exceptionalPoint Q, blowupAffine_exceptionalPoint Q⟩
  left_inv R := by
    apply Subtype.ext
    apply blowupPoint_ext
    · simpa using R.2.symm
    · simp
  right_inv Q := by simp

/-- The projective direction determined by a non-origin affine point. -/
noncomputable def affineDirection
    (P : BlowupAffineChart (k := k) (σ := σ))
    (hP : blowupSpatialVector P ≠ 0) : ProjectiveSpace k σ :=
  Projectivization.mk k (blowupSpatialVector P) hP

omit [DecidableEq σ] in
theorem affineDirection_incidence
    (P : BlowupAffineChart (k := k) (σ := σ))
    (hP : blowupSpatialVector P ≠ 0) :
    ∀ i j : σ,
      P.1.rep (some i) * (affineDirection P hP).rep j =
        P.1.rep (some j) * (affineDirection P hP).rep i := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k
    (blowupSpatialVector P) hP
  intro i j
  have hi := congrFun ha i
  have hj := congrFun ha j
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hi hj
  change blowupSpatialVector P i *
      (Projectivization.mk k (blowupSpatialVector P) hP).rep j =
    blowupSpatialVector P j *
      (Projectivization.mk k (blowupSpatialVector P) hP).rep i
  rw [← hj, ← hi]
  ring

/-- The canonical point over a non-origin affine point. -/
noncomputable def nonexceptionalPoint
    (P : BlowupAffineChart (k := k) (σ := σ))
    (hP : blowupSpatialVector P ≠ 0) :
    BlowupPoint (k := k) (σ := σ) :=
  blowupMk P (affineDirection P hP) (affineDirection_incidence P hP)

omit [DecidableEq σ] in
@[simp]
theorem blowupAffine_nonexceptionalPoint
    (P : BlowupAffineChart (k := k) (σ := σ))
    (hP : blowupSpatialVector P ≠ 0) :
    blowupAffine (nonexceptionalPoint P hP) = P := by
  simp [nonexceptionalPoint]

omit [DecidableEq σ] in
theorem blowupDirection_eq_affineDirection
    (R : BlowupPoint (k := k) (σ := σ))
    (hP : blowupSpatialVector (blowupAffine R) ≠ 0) :
    blowupDirection R = affineDirection (blowupAffine R) hP := by
  let D := affineDirection (blowupAffine R) hP
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k
    (blowupSpatialVector (blowupAffine R)) hP
  have hminor : ∀ l m : σ,
      D.rep l * (blowupDirection R).rep m =
        D.rep m * (blowupDirection R).rep l := by
    intro l m
    have hl := congrFun ha l
    have hm := congrFun ha m
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hl hm
    change (Projectivization.mk k
        (blowupSpatialVector (blowupAffine R)) hP).rep l *
        (blowupDirection R).rep m =
      (Projectivization.mk k
        (blowupSpatialVector (blowupAffine R)) hP).rep m *
        (blowupDirection R).rep l
    rw [← hl, ← hm]
    rw [mul_assoc, mul_assoc]
    exact congrArg ((a : k) * ·) (blowup_incidence R l m)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp D.rep_nonzero
  exact (eq_of_minors_eq_zero hi hminor).symm

omit [DecidableEq σ] in
/-- Property (1), set-theoretic fibre statement: away from the origin the
first projection has exactly one point in every fibre. -/
theorem existsUnique_fibre_of_spatialVector_ne_zero
    (P : BlowupAffineChart (k := k) (σ := σ))
    (hP : blowupSpatialVector P ≠ 0) :
    ∃! R : BlowupPoint (k := k) (σ := σ), blowupAffine R = P := by
  refine ⟨nonexceptionalPoint P hP,
    blowupAffine_nonexceptionalPoint P hP, ?_⟩
  intro R hR
  subst P
  apply blowupPoint_ext
  · simp
  · simpa [nonexceptionalPoint] using
      (blowupDirection_eq_affineDirection R hP)

/-- Property (1) in Hartshorne's stated form: every point other than the
origin has a singleton fibre. -/
theorem existsUnique_fibre_of_ne_origin
    (P : BlowupAffineChart (k := k) (σ := σ))
    (hP : P ≠ blowupOrigin) :
    ∃! R : BlowupPoint (k := k) (σ := σ), blowupAffine R = P :=
  existsUnique_fibre_of_spatialVector_ne_zero P
    ((blowupSpatialVector_ne_zero_iff P).2 hP)

/-! ### Lines through the origin and density of the ordinary locus -/

/-- Reindex ordinary affine coordinates as the coordinates of the `none`
chart. The impossible `none` case is assigned `0`; the subtype proof ensures
that it is never observed. -/
def blowupOptionCoordinates (x : σ → k) :
    {j : Option σ // j ≠ none} → k :=
  fun j => j.1.elim 0 x

omit [DecidableEq σ] in
@[simp]
theorem blowupOptionCoordinates_some (x : σ → k) (i : σ) :
    blowupOptionCoordinates x ⟨some i, by simp⟩ = x i := rfl

/-- The affine point with coordinates `x`, placed in the standard chart. -/
noncomputable def blowupAffinePoint (x : σ → k) :
    BlowupAffineChart (k := k) (σ := σ) :=
  ⟨chartInv (none : Option σ) (blowupOptionCoordinates x),
    chartInv_mem_standardChart (none : Option σ)
      (blowupOptionCoordinates x)⟩

theorem blowupAffinePoint_injective :
    Function.Injective (blowupAffinePoint (k := k) (σ := σ)) := by
  intro x y hxy
  have hproj : (blowupAffinePoint (k := k) x).1 =
      (blowupAffinePoint (k := k) y).1 := congrArg Subtype.val hxy
  have hcoords := congrArg (chartMap (none : Option σ)) hproj
  simp only [blowupAffinePoint, chartMap_chartInv] at hcoords
  funext i
  exact congrFun hcoords ⟨some i, by simp⟩

@[simp]
theorem blowupAffinePoint_zero :
    blowupAffinePoint (k := k) (0 : σ → k) =
      blowupOrigin (k := k) (σ := σ) := by
  apply Subtype.ext
  apply congrArg (chartInv (k := k) (none : Option σ))
  funext j
  rcases j with ⟨j, hj⟩
  cases j with
  | none => exact (hj rfl).elim
  | some i => rfl

theorem blowupSpatialVector_affinePoint_ne_zero {x : σ → k}
    (hx : x ≠ 0) :
    blowupSpatialVector (blowupAffinePoint (k := k) x) ≠ 0 := by
  intro hspatial
  apply hx
  funext i
  have hcoord := congrFun
    (chartMap_chartInv (k := k) (none : Option σ)
      (blowupOptionCoordinates x)) ⟨some i, by simp⟩
  change (blowupAffinePoint (k := k) x).1.rep (some i) /
      (blowupAffinePoint (k := k) x).1.rep none = x i at hcoord
  have hi := congrFun hspatial i
  change (blowupAffinePoint (k := k) x).1.rep (some i) = 0 at hi
  rw [hi, zero_div] at hcoord
  exact hcoord.symm

theorem blowupAffinePoint_rep_some (x : σ → k) (i : σ) :
    (blowupAffinePoint (k := k) x).1.rep (some i) =
      x i * (blowupAffinePoint (k := k) x).1.rep none := by
  have hcoord := congrFun
    (chartMap_chartInv (k := k) (none : Option σ)
      (blowupOptionCoordinates x)) ⟨some i, by simp⟩
  change (blowupAffinePoint (k := k) x).1.rep (some i) /
      (blowupAffinePoint (k := k) x).1.rep none = x i at hcoord
  exact (div_eq_iff (rep_ne_zero_of_mem_standardChart
    (blowupAffinePoint (k := k) x).2)).mp hcoord

theorem blowupLine_incidence (a : σ → k) (ha : a ≠ 0) (t : k) :
    ∀ i j : σ,
      (blowupAffinePoint (k := k) (fun l => t * a l)).1.rep (some i) *
          (Projectivization.mk k a ha).rep j =
        (blowupAffinePoint (k := k) (fun l => t * a l)).1.rep (some j) *
          (Projectivization.mk k a ha).rep i := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep k a ha
  intro i j
  rw [blowupAffinePoint_rep_some, blowupAffinePoint_rep_some]
  have hi := congrFun hc i
  have hj := congrFun hc j
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at hi hj
  rw [← hi, ← hj]
  ring

/-- The lift of the affine line `x = t a`; its projective direction is fixed
at `[a]`, including at `t = 0`. -/
noncomputable def blowupLineLift (a : σ → k) (ha : a ≠ 0) (t : k) :
    BlowupPoint (k := k) (σ := σ) :=
  blowupMk (blowupAffinePoint (fun i => t * a i))
    (Projectivization.mk k a ha) (blowupLine_incidence a ha t)

@[simp]
theorem blowupAffine_lineLift (a : σ → k) (ha : a ≠ 0) (t : k) :
    blowupAffine (blowupLineLift (k := k) a ha t) =
      blowupAffinePoint (fun i => t * a i) := by
  simp [blowupLineLift]

@[simp]
theorem blowupDirection_lineLift (a : σ → k) (ha : a ≠ 0) (t : k) :
    blowupDirection (blowupLineLift (k := k) a ha t) =
      Projectivization.mk k a ha := by
  simp [blowupLineLift]

theorem blowupLineLift_zero (a : σ → k) (ha : a ≠ 0) :
    blowupLineLift (k := k) a ha 0 =
      exceptionalPoint (Projectivization.mk k a ha) := by
  apply blowupPoint_ext
  · rw [blowupAffine_lineLift, blowupAffine_exceptionalPoint]
    have hz : (fun i : σ => (0 : k) * a i) = 0 := by
      funext i
      simp
    rw [hz, blowupAffinePoint_zero]
  · simp

/-- Property (3): an exceptional point is the endpoint at `t = 0` of the
lift of the affine line having its projective direction. -/
theorem eq_blowupLineLift_zero_of_mem_exceptional
    (R : BlowupPoint (k := k) (σ := σ))
    (hR : R ∈ ExceptionalFibre (k := k) (σ := σ)) :
    R = blowupLineLift (blowupDirection R).rep
      (blowupDirection R).rep_nonzero 0 := by
  rw [blowupLineLift_zero, (blowupDirection R).mk_rep]
  apply blowupPoint_ext
  · simpa [ExceptionalFibre] using hR
  · simp

theorem blowupLineLift_nonexceptional (a : σ → k) (ha : a ≠ 0)
    {t : k} (ht : t ≠ 0) :
    blowupAffine (blowupLineLift (k := k) a ha t) ≠
      blowupOrigin (k := k) (σ := σ) := by
  rw [blowupAffine_lineLift, ← blowupAffinePoint_zero]
  apply fun h => ha ?_
  have hzero := blowupAffinePoint_injective h
  funext i
  have hi := congrFun hzero i
  exact (mul_eq_zero.mp hi).resolve_left ht

/-- The ordinary locus, i.e. the complement of the exceptional fibre. -/
def blowupOrdinaryLocus : Set (BlowupPoint (k := k) (σ := σ)) :=
  {R | blowupAffine R ≠ blowupOrigin}

section LineTopology

variable [IsAlgClosed k]

/-- An affine line, bundled as a variety so that polynomial coordinate maps
can be fed to the morphism/continuity criteria. -/
noncomputable def blowupLineVariety : Variety k :=
  Variety.ofQuasiAffine
    (show IsQuasiAffineVariety (Set.univ : Set (Unit → k)) from
      (show IsAffineVariety (Set.univ : Set (Unit → k)) from
        ⟨isIrreducible_univ, isClosed_univ⟩).isQuasiAffineVariety)

/-- Coordinates of the line `t ↦ t a`, reindexed into the `none` chart. -/
noncomputable def blowupLineCoordinates (a : σ → k)
    (t : (blowupLineVariety (k := k)).carrier) :
    {j : Option σ // j ≠ none} → k :=
  blowupOptionCoordinates (fun i => t.1 () * a i)

omit [DecidableEq σ] in
theorem blowupLineCoordinates_regular (a : σ → k)
    (j : {j : Option σ // j ≠ none}) :
    (blowupLineVariety (k := k)).IsGlobalRegular
      (fun t => blowupLineCoordinates a t j) := by
  rcases j with ⟨j, hj⟩
  cases j with
  | none => exact (hj rfl).elim
  | some i =>
      change IsRegularVia
        (openIota (⊤ : Opens (Set.univ : Set (Unit → k))))
        (fun t : (⊤ : Opens (Set.univ : Set (Unit → k))) =>
          t.1.1 () * a i)
      intro t
      refine ⟨Set.univ, isOpen_univ, Set.mem_univ _,
        X () * C (a i), 1, by simp, ?_⟩
      intro x hx
      simp [openIota]

omit [DecidableEq σ] in
theorem continuous_blowupLineCoordinates (a : σ → k) :
    Continuous (blowupLineCoordinates (k := k) a) := by
  exact Variety.continuous_of_coords_regular _
    (blowupLineCoordinates_regular a)

/-- The affine point `t a`, now as a continuous map from the affine line. -/
noncomputable def blowupLineBasePoint (a : σ → k)
    (t : (blowupLineVariety (k := k)).carrier) :
    BlowupAffineChart (k := k) (σ := σ) :=
  blowupAffinePoint (fun i => t.1 () * a i)

theorem continuous_blowupLineBasePoint (a : σ → k) :
    Continuous (blowupLineBasePoint (k := k) a) := by
  exact ((continuous_chartInv (k := k) (none : Option σ)).comp
    (continuous_blowupLineCoordinates a)).subtype_mk _

/-- The lifted line as a continuous curve in the blow-up. -/
noncomputable def blowupLineCurve (a : σ → k) (ha : a ≠ 0)
    (t : (blowupLineVariety (k := k)).carrier) :
    BlowupPoint (k := k) (σ := σ) :=
  blowupLineLift a ha (t.1 ())

theorem continuous_blowupLineCurve (a : σ → k) (ha : a ≠ 0) :
    Continuous (blowupLineCurve (k := k) a ha) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun t : (blowupLineVariety (k := k)).carrier =>
    segreMap (blowupLineBasePoint (k := k) a t).1
      (Projectivization.mk k a ha))
  exact (continuous_segreMap_left (Projectivization.mk k a ha)).comp
    (continuous_blowupLineBasePoint a).subtype_val

/-- Nonzero parameters on the affine line. -/
def blowupLinePunctured : Set (blowupLineVariety (k := k)).carrier :=
  {t | t.1 () ≠ 0}

theorem blowupLineParameter_regular :
    (blowupLineVariety (k := k)).IsGlobalRegular (fun t => t.1 ()) := by
  change IsRegularVia
    (openIota (⊤ : Opens (Set.univ : Set (Unit → k))))
    (fun t : (⊤ : Opens (Set.univ : Set (Unit → k))) => t.1.1 ())
  intro t
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, X (), 1, by simp, ?_⟩
  intro x hx
  simp [openIota]

theorem isOpen_blowupLinePunctured :
    IsOpen (blowupLinePunctured (k := k)) := by
  have hz : IsClosed
      {t : (blowupLineVariety (k := k)).carrier | t.1 () = 0} :=
    Variety.isClosed_zeroSet_of_isGlobalRegular blowupLineParameter_regular
  have heq : blowupLinePunctured (k := k) =
      {t : (blowupLineVariety (k := k)).carrier | t.1 () = 0}ᶜ := by
    ext t
    simp [blowupLinePunctured]
  rw [heq]
  exact hz.isOpen_compl

theorem blowupLinePunctured_nonempty :
    (blowupLinePunctured (k := k)).Nonempty := by
  refine ⟨⟨fun _ => 1, Set.mem_univ _⟩, ?_⟩
  change (1 : k) ≠ 0
  exact one_ne_zero

theorem dense_blowupLinePunctured :
    Dense (blowupLinePunctured (k := k)) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  have hpre : IsPreirreducible
      (Set.univ : Set (blowupLineVariety (k := k)).carrier) :=
    PreirreducibleSpace.isPreirreducible_univ
  obtain ⟨u, hu⟩ := hUne
  obtain ⟨v, hv⟩ := blowupLinePunctured_nonempty (k := k)
  obtain ⟨z, -, hz⟩ := hpre U (blowupLinePunctured (k := k)) hU
    isOpen_blowupLinePunctured
    ⟨u, Set.mem_univ u, hu⟩ ⟨v, Set.mem_univ v, hv⟩
  exact ⟨z, hz⟩

noncomputable def blowupLineZero : (blowupLineVariety (k := k)).carrier :=
  ⟨0, Set.mem_univ _⟩

theorem blowupLineCurve_zero (a : σ → k) (ha : a ≠ 0) :
    blowupLineCurve (k := k) a ha blowupLineZero =
      exceptionalPoint (Projectivization.mk k a ha) := by
  simpa [blowupLineCurve, blowupLineZero] using
    blowupLineLift_zero (k := k) a ha

theorem blowupLineCurve_zero_mem_closure_image (a : σ → k) (ha : a ≠ 0) :
    blowupLineCurve (k := k) a ha blowupLineZero ∈
      closure (blowupLineCurve (k := k) a ha ''
        blowupLinePunctured (k := k)) := by
  apply image_closure_subset_closure_image
    (continuous_blowupLineCurve (k := k) a ha)
  refine ⟨blowupLineZero, ?_, rfl⟩
  rw [dense_blowupLinePunctured (k := k) |>.closure_eq]
  exact Set.mem_univ _

theorem blowupLineCurve_punctured_subset_ordinary
    (a : σ → k) (ha : a ≠ 0) :
    blowupLineCurve (k := k) a ha '' blowupLinePunctured (k := k) ⊆
      blowupOrdinaryLocus (k := k) (σ := σ) := by
  rintro R ⟨t, ht, rfl⟩
  exact blowupLineLift_nonexceptional a ha ht

/-- Every point of the exceptional fibre is approached by the lift of the
line having that projective direction. -/
theorem exceptionalPoint_mem_closure_ordinary (Q : ProjectiveSpace k σ) :
    exceptionalPoint (k := k) Q ∈
      closure (blowupOrdinaryLocus (k := k) (σ := σ)) := by
  have hcurve := blowupLineCurve_zero_mem_closure_image
    (k := k) Q.rep Q.rep_nonzero
  have hzero : blowupLineCurve (k := k) Q.rep Q.rep_nonzero blowupLineZero =
      exceptionalPoint (k := k) Q := by
    rw [blowupLineCurve_zero, Q.mk_rep]
  rw [hzero] at hcurve
  exact closure_mono
    (blowupLineCurve_punctured_subset_ordinary Q.rep Q.rep_nonzero) hcurve

/-- The complement of the exceptional fibre is dense. This is the density
half of Hartshorne's property (4). -/
theorem dense_blowupOrdinaryLocus :
    Dense (blowupOrdinaryLocus (k := k) (σ := σ)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro R
  by_cases hR : blowupAffine R = blowupOrigin
  · have heq : exceptionalPoint (k := k) (blowupDirection R) = R := by
      apply blowupPoint_ext
      · simpa using hR.symm
      · simp
    rw [← heq]
    exact exceptionalPoint_mem_closure_ordinary (blowupDirection R)
  · exact subset_closure hR

end LineTopology

end OriginAndFibres

end Hartshorne
