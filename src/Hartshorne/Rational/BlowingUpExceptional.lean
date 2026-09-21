/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.BlowingUpVariety

/-!
# The exceptional fibre of the blow-up

The fibre over the origin in the blow-up of affine space is the Segre product
of the origin with projective space.  Projection to the second factor is an
isomorphism of varieties.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k] {σ : Type u}

/-- Linear homogeneous equations cutting out a single projective point. -/
noncomputable def projectiveSingletonEquation {ι : Type u}
    (P : ProjectiveSpace k ι) (i j : ι) : MvPolynomial ι k :=
  C (P.rep i) * X j - C (P.rep j) * X i

/-- The family of all proportionality equations for a projective point. -/
noncomputable def projectiveSingletonEquations {ι : Type u}
    (P : ProjectiveSpace k ι) : Set (MvPolynomial ι k) :=
  {f | ∃ i j : ι, projectiveSingletonEquation P i j = f}

theorem projectiveSingletonEquations_isHomogeneousSet {ι : Type u}
    (P : ProjectiveSpace k ι) :
    IsHomogeneousSet (projectiveSingletonEquations P) := by
  rintro f ⟨i, j, rfl⟩
  exact ⟨1, (isHomogeneous_C_mul_X (P.rep i) j).sub
    (isHomogeneous_C_mul_X (P.rep j) i)⟩

theorem projZeroSet_projectiveSingletonEquations {ι : Type u}
    (P : ProjectiveSpace k ι) :
    projZeroSet (projectiveSingletonEquations P) =
      ({P} : Set (ProjectiveSpace k ι)) := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨i, hi⟩ := Function.ne_iff.mp P.rep_nonzero
    have hminor : ∀ l m : ι,
        P.rep l * Q.rep m = P.rep m * Q.rep l := by
      intro l m
      have h := hQ (projectiveSingletonEquation P l m) ⟨l, m, rfl⟩
      simpa [HomogeneousVanish, projectiveSingletonEquation, sub_eq_zero] using h
    exact (eq_of_minors_eq_zero hi hminor) ▸ Set.mem_singleton P
  · intro hQ f hf
    rw [Set.mem_singleton_iff] at hQ
    subst Q
    obtain ⟨i, j, rfl⟩ := hf
    simp [HomogeneousVanish, projectiveSingletonEquation]
    ring

/-- A point is a projective variety. -/
theorem isProjVariety_singleton_projectivePoint {ι : Type u}
    (P : ProjectiveSpace k ι) :
    IsProjVariety ({P} : Set (ProjectiveSpace k ι)) := by
  refine ⟨isIrreducible_singleton, ?_⟩
  rw [← projZeroSet_projectiveSingletonEquations P]
  exact isClosed_projZeroSet_of_isHomogeneousSet
    (projectiveSingletonEquations_isHomogeneousSet P)

section ExceptionalFibre

variable [DecidableEq σ]

/-- The exceptional fibre in the flat projective presentation of the blow-up. -/
noncomputable abbrev blowupExceptionalSet :
    Set (ProjectiveSpace k (Option σ × σ)) :=
  segreProduct
    ({(blowupOrigin (k := k) (σ := σ)).1} :
      Set (ProjectiveSpace k (Option σ)))
    (Set.univ : Set (ProjectiveSpace k σ))

/-- The zero fibre in the nested presentation, flattened into the common
projective ambient. -/
noncomputable def exceptionalFibreFlat :
    Set (ProjectiveSpace k (Option σ × σ)) :=
  (fun R : BlowupPoint (k := k) (σ := σ) => R.1.1) ''
    ExceptionalFibre (k := k) (σ := σ)

/-- The fixed-first-factor Segre product is exactly the fibre over the origin. -/
theorem blowupExceptionalSet_eq_fibre :
    blowupExceptionalSet (k := k) (σ := σ) =
      exceptionalFibreFlat (k := k) (σ := σ) := by
  ext R
  constructor
  · intro hR
    obtain ⟨P, hP, Q, -, hPQ⟩ := mem_segreProduct_iff.mp hR
    have hP0 : P = (blowupOrigin (k := k) (σ := σ)).1 :=
      Set.mem_singleton_iff.mp hP
    subst P
    let S : BlowupPoint (k := k) (σ := σ) := exceptionalPoint Q
    refine ⟨S, blowupAffine_exceptionalPoint Q, ?_⟩
    exact hPQ
  · rintro ⟨S, hS, rfl⟩
    have hEq : S = exceptionalPoint (k := k) (blowupDirection S) := by
      apply blowupPoint_ext
      · simpa [ExceptionalFibre] using hS
      · simp
    rw [hEq]
    exact mem_segreProduct_iff.mpr
      ⟨(blowupOrigin (k := k) (σ := σ)).1, Set.mem_singleton _,
        blowupDirection S, Set.mem_univ _, rfl⟩

variable [IsAlgClosed k] [Finite σ] [Nonempty σ]

/-- The exceptional fibre is a projective variety. -/
theorem isProjVariety_blowupExceptionalSet :
    IsProjVariety (blowupExceptionalSet (k := k) (σ := σ)) := by
  exact isProjVariety_segreProduct
    (isProjVariety_singleton_projectivePoint
      (blowupOrigin (k := k) (σ := σ)).1)
    (isProjVariety_univ (k := k) (σ := σ))

namespace VarietyHom

/-- A constant map between varieties is a morphism. -/
noncomputable def constantHom {X Y : Variety k} (y : Y.carrier) :
    VarietyHom X Y where
  toFun := fun _ => y
  continuous_toFun := continuous_const
  regular_comp V f hf := by
    classical
    let W := Opens.comap
      ⟨(fun _ : X.carrier => y), continuous_const⟩ V
    by_cases hW : Nonempty W
    · let w : W := Classical.choice hW
      have heq : (fun x : W => f ⟨y, x.2⟩) =
          fun _ : W => f ⟨y, w.2⟩ := by
        funext x
        congr 2
      rw [heq]
      exact (X.regular W).algebraMap_mem (f ⟨y, w.2⟩)
    · have heq : (fun x : W => f ⟨y, x.2⟩) = 0 := by
        funext x
        exact (hW ⟨x⟩).elim
      rw [heq]
      exact (X.regular W).zero_mem

end VarietyHom

private noncomputable abbrev hExceptionalOrigin :
    IsQuasiProjVariety
      ({(blowupOrigin (k := k) (σ := σ)).1} :
        Set (ProjectiveSpace k (Option σ))) :=
  (isProjVariety_singleton_projectivePoint
    (blowupOrigin (k := k) (σ := σ)).1).isQuasiProjVariety

private noncomputable abbrev hExceptionalProjectiveSpace :
    IsQuasiProjVariety (Set.univ : Set (ProjectiveSpace k σ)) :=
  (isProjVariety_univ (k := k) (σ := σ)).isQuasiProjVariety

private noncomputable abbrev hExceptionalSet :
    IsQuasiProjVariety (blowupExceptionalSet (k := k) (σ := σ)) :=
  isProjVariety_blowupExceptionalSet.isQuasiProjVariety

/-- Projection of the exceptional fibre to its projective direction. -/
noncomputable def exceptionalDirectionHom :
    VarietyHom
      (Variety.ofQuasiProjective (hExceptionalSet (k := k) (σ := σ)))
      (Variety.ofQuasiProjective
        (hExceptionalProjectiveSpace (k := k) (σ := σ))) :=
  segreProductSndHom
    (hExceptionalProjectiveSpace (k := k) (σ := σ))
    (hExceptionalSet (k := k) (σ := σ))

/-- The constant map to the origin, used with the identity to construct the
inverse inclusion of the exceptional fibre. -/
noncomputable def exceptionalOriginHom :
    VarietyHom
      (Variety.ofQuasiProjective
        (hExceptionalProjectiveSpace (k := k) (σ := σ)))
      (Variety.ofQuasiProjective (hExceptionalOrigin (k := k) (σ := σ))) :=
  VarietyHom.constantHom
    ⟨(blowupOrigin (k := k) (σ := σ)).1, Set.mem_singleton _⟩

/-- The map `Q ↦ (0,Q)` into the exceptional fibre. -/
noncomputable def exceptionalInclusionHom :
    VarietyHom
      (Variety.ofQuasiProjective
        (hExceptionalProjectiveSpace (k := k) (σ := σ)))
      (Variety.ofQuasiProjective (hExceptionalSet (k := k) (σ := σ))) :=
  segreProductLiftHom
    (hExceptionalOrigin (k := k) (σ := σ))
    (hExceptionalProjectiveSpace (k := k) (σ := σ))
    (hExceptionalSet (k := k) (σ := σ))
    (exceptionalOriginHom (k := k) (σ := σ))
    (VarietyHom.id _)

/-- Property (2): the exceptional fibre is isomorphic to `P^(|σ|-1)`. -/
theorem exceptionalDirectionHom_isIso :
    (exceptionalDirectionHom (k := k) (σ := σ)).IsIso := by
  refine ⟨exceptionalInclusionHom (k := k) (σ := σ), ?_, ?_⟩
  · apply VarietyHom.ext
    funext R
    rw [VarietyHom.comp_apply, VarietyHom.id_apply]
    rw [exceptionalInclusionHom, segreProductLiftHom_apply]
    apply Subtype.ext
    have hdir : (exceptionalDirectionHom (k := k) (σ := σ)) R =
        segreProductSnd R := by
      exact segreProductSndHom_apply
        (hExceptionalProjectiveSpace (k := k) (σ := σ))
        (hExceptionalSet (k := k) (σ := σ)) R
    change (segreProductMk
      ((exceptionalOriginHom (k := k) (σ := σ))
        ((exceptionalDirectionHom (k := k) (σ := σ)) R))
      ((VarietyHom.id _) ((exceptionalDirectionHom (k := k) (σ := σ)) R))).1 = R.1
    rw [VarietyHom.id_apply]
    have hfirst : segreProductFst R =
        ((exceptionalOriginHom (k := k) (σ := σ))
          ((exceptionalDirectionHom (k := k) (σ := σ)) R)) := by
      apply Subtype.ext
      exact Set.mem_singleton_iff.mp (segreProductFst R).2
    rw [← hfirst, hdir]
    exact segreMap_fst_snd R
  · exact segreProductSndHom_comp_lift
      (hExceptionalOrigin (k := k) (σ := σ))
      (hExceptionalProjectiveSpace (k := k) (σ := σ))
      (hExceptionalSet (k := k) (σ := σ))
      (exceptionalOriginHom (k := k) (σ := σ))
      (VarietyHom.id _)

end ExceptionalFibre

end Hartshorne
