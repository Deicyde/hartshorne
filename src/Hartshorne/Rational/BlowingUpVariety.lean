/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.BlowingUpGeometry

/-!
# The blow-up as a quasi-projective variety

This file proves that the incidence construction for the blow-up of affine
space at the origin is irreducible and quasi-projective.  The proof uses an
explicit polynomial parametrization: a scalar records distance along a line
through the origin and a nonzero vector records its direction.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k] {σ : Type u}

/-- Parameters consist of a scalar and a nonzero direction vector. -/
def blowupParameterDomain : Set (Option σ → k) :=
  {v | (fun i => v (some i)) ≠ 0}

def blowupBaseVector (v : Option σ → k) : Option σ → k
  | none => 1
  | some i => v none * v (some i)

def blowupDirectionVector (v : Option σ → k) : σ → k :=
  fun i => v (some i)

def blowupParameterVector (v : Option σ → k) : Option σ × σ → k
  | (none, j) => v (some j)
  | (some i, j) => v none * v (some i) * v (some j)

theorem blowupBaseVector_ne_zero (v : Option σ → k) :
    blowupBaseVector v ≠ 0 := by
  intro h
  have := congrFun h none
  simp [blowupBaseVector] at this

theorem blowupParameterVector_ne_zero {v : Option σ → k}
    (hv : v ∈ blowupParameterDomain (k := k) (σ := σ)) :
    blowupParameterVector v ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  intro h
  have := congrFun h (none, i)
  exact hi (by simpa [blowupParameterVector] using this)

theorem blowupDirectionVector_ne_zero {v : Option σ → k}
    (hv : v ∈ blowupParameterDomain (k := k) (σ := σ)) :
    blowupDirectionVector v ≠ 0 := by
  change (fun i => v (some i)) ≠ 0 at hv
  exact hv

/-- The polynomial parametrization of the blow-up. -/
noncomputable def blowupParameterMap
    (v : blowupParameterDomain (k := k) (σ := σ)) :
    ProjectiveSpace k (Option σ × σ) :=
  Projectivization.mk k (blowupParameterVector v.1)
    (blowupParameterVector_ne_zero v.2)

theorem blowupBasePoint_mem (v : Option σ → k) :
    Projectivization.mk k (blowupBaseVector v) (blowupBaseVector_ne_zero v) ∈
      BlowupAffineChart (k := k) (σ := σ) := by
  change ¬ HomogeneousVanish (X none)
    (Projectivization.mk k (blowupBaseVector v) (blowupBaseVector_ne_zero v))
  rw [homogeneousVanish_X_iff (blowupBaseVector_ne_zero v)]
  simp [blowupBaseVector]

theorem blowupParameterMap_eq_segreMap
    (v : blowupParameterDomain (k := k) (σ := σ)) :
    blowupParameterMap v =
      segreMap
        (Projectivization.mk k (blowupBaseVector v.1)
          (blowupBaseVector_ne_zero v.1))
        (Projectivization.mk k (blowupDirectionVector v.1)
          (blowupDirectionVector_ne_zero v.2)) := by
  unfold blowupParameterMap
  rw [segreMap_mk_mk]
  apply (Projectivization.mk_eq_mk_iff k _ _ _ _).2
  refine ⟨1, ?_⟩
  funext ij
  rcases ij with ⟨a, j⟩
  cases a <;> simp [blowupParameterVector, blowupBaseVector,
    blowupDirectionVector, segreVector]

theorem blowupParameterMap_mem
    (v : blowupParameterDomain (k := k) (σ := σ)) :
    blowupParameterMap v ∈ blowupSet (k := k) (σ := σ) := by
  constructor
  · rw [blowupParameterMap_eq_segreMap]
    exact (mem_segreProduct_iff).2
      ⟨Projectivization.mk k (blowupBaseVector v.1)
          (blowupBaseVector_ne_zero v.1),
        blowupBasePoint_mem v.1,
        Projectivization.mk k (blowupDirectionVector v.1)
          (blowupDirectionVector_ne_zero v.2),
        Set.mem_univ _, rfl⟩
  · intro f hf
    obtain ⟨i, j, rfl⟩ := hf
    unfold blowupEquation blowupParameterMap
    rw [homogeneousVanish_iff_of_isHomogeneous
      ((isHomogeneous_X k (some i, j)).sub
        (isHomogeneous_X k (some j, i)))
      (blowupParameterVector_ne_zero v.2)]
    simp [blowupParameterVector]
    ring

noncomputable def blowupParametrization
    (v : blowupParameterDomain (k := k) (σ := σ)) :
    blowupSet (k := k) (σ := σ) :=
  ⟨blowupParameterMap v, blowupParameterMap_mem v⟩

noncomputable def blowupParameterPolynomial (aj : Option σ × σ) :
    MvPolynomial (Option σ) k :=
  match aj.1 with
  | none => X (some aj.2)
  | some i => X none * X (some i) * X (some aj.2)

noncomputable def blowupParameterRingHom :
    MvPolynomial (Option σ × σ) k →ₐ[k] MvPolynomial (Option σ) k :=
  MvPolynomial.aeval (blowupParameterPolynomial (k := k))

theorem eval_blowupParameterPolynomial (v : Option σ → k)
    (aj : Option σ × σ) :
    eval v (blowupParameterPolynomial (k := k) aj) =
      blowupParameterVector v aj := by
  rcases aj with ⟨a, j⟩
  cases a <;> simp [blowupParameterPolynomial, blowupParameterVector]

theorem eval_blowupParameterRingHom (v : Option σ → k)
    (f : MvPolynomial (Option σ × σ) k) :
    eval v (blowupParameterRingHom (k := k) (σ := σ) f) =
      eval (blowupParameterVector v) f := by
  rw [blowupParameterRingHom, aeval_def, eval_eval₂]
  simp only [eval_blowupParameterPolynomial]
  have hc : (eval v).comp (algebraMap k (MvPolynomial (Option σ) k)) =
      RingHom.id k := by
    ext c
    simp
  rw [hc, eval₂_id]

theorem continuous_blowupParameterMap :
    Continuous (blowupParameterMap (k := k) (σ := σ)) := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨T, hT, rfl⟩ := isClosed_iff_isProjAlgebraicSet.mp hC
  have heq :
      blowupParameterMap (k := k) (σ := σ) ⁻¹' projZeroSet T =
        Subtype.val ⁻¹'
          zeroSet (blowupParameterRingHom (k := k) (σ := σ) '' T) := by
    ext v
    simp only [Set.mem_preimage, mem_projZeroSet_iff, mem_zeroSet_iff,
      Set.mem_image]
    constructor
    · intro h g hg
      obtain ⟨f, hf, rfl⟩ := hg
      rw [eval_blowupParameterRingHom]
      obtain ⟨n, hfn⟩ := hT f hf
      exact (homogeneousVanish_iff_of_isHomogeneous hfn
        (blowupParameterVector_ne_zero v.2)).mp (h f hf)
    · intro h f hf
      obtain ⟨n, hfn⟩ := hT f hf
      unfold blowupParameterMap
      rw [homogeneousVanish_iff_of_isHomogeneous hfn
        (blowupParameterVector_ne_zero v.2), ← eval_blowupParameterRingHom]
      exact h (blowupParameterRingHom (k := k) (σ := σ) f) ⟨f, hf, rfl⟩
  rw [heq]
  exact (isClosed_zeroSet _).preimage continuous_subtype_val

theorem isOpen_blowupParameterDomain :
    IsOpen (blowupParameterDomain (k := k) (σ := σ)) := by
  let T : Set (MvPolynomial (Option σ) k) := Set.range fun i : σ => X (some i)
  have heq : blowupParameterDomain (k := k) (σ := σ) = (zeroSet T)ᶜ := by
    ext v
    simp only [blowupParameterDomain, Set.mem_ofPred_eq, Set.mem_compl_iff,
      mem_zeroSet_iff, T, Set.mem_range, not_forall]
    constructor
    · intro hv
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact ⟨X (some i), ⟨i, rfl⟩, by simpa using hi⟩
    · rintro ⟨f, ⟨i, rfl⟩, hi⟩
      exact Function.ne_iff.mpr ⟨i, by simpa using hi⟩
  rw [heq]
  exact (isClosed_zeroSet T).isOpen_compl

theorem blowupParameterDomain_nonempty [Nonempty σ] :
    (blowupParameterDomain (k := k) (σ := σ)).Nonempty := by
  classical
  let i : σ := Classical.choice inferInstance
  let v : Option σ → k := Pi.single (some i) 1
  refine ⟨v, Function.ne_iff.mpr ⟨i, ?_⟩⟩
  simp [v]

theorem isIrreducible_blowupParameterDomain [IsAlgClosed k] [Finite σ]
    [Nonempty σ] :
    IsIrreducible (blowupParameterDomain (k := k) (σ := σ)) := by
  refine ⟨blowupParameterDomain_nonempty, ?_⟩
  exact IsPreirreducible.open_subset
    (isIrreducible_univ (k := k) (σ := Option σ)).2
    isOpen_blowupParameterDomain (Set.subset_univ _)

theorem range_blowupParameterMap :
    Set.range (blowupParameterMap (k := k) (σ := σ)) =
      blowupSet (k := k) (σ := σ) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    exact blowupParameterMap_mem v
  · intro R hR
    obtain ⟨P, hP, Q, -, hPQ⟩ := (mem_segreProduct_iff).mp hR.1
    have hinc : segreMap P Q ∈ blowupIncidence (k := k) (σ := σ) := by
      rw [hPQ]
      exact hR.2
    have hrel := (segreMap_mem_blowupIncidence_iff P Q).mp hinc
    obtain ⟨q, hq⟩ := Function.ne_iff.mp Q.rep_nonzero
    have hp0 : P.rep none ≠ 0 := rep_ne_zero_of_mem_standardChart hP
    let t : k := P.rep (some q) / (P.rep none * Q.rep q)
    let v : Option σ → k
      | none => t
      | some i => Q.rep i
    have hv : v ∈ blowupParameterDomain (k := k) (σ := σ) := by
      change (fun i => v (some i)) ≠ 0
      simpa [v] using Q.rep_nonzero
    have hbase :
        Projectivization.mk k (blowupBaseVector v)
            (blowupBaseVector_ne_zero v) = P := by
      have hmk : Projectivization.mk k (blowupBaseVector v)
            (blowupBaseVector_ne_zero v) =
          Projectivization.mk k P.rep P.rep_nonzero := by
        refine (Projectivization.mk_eq_mk_iff k _ _ _ _).2
          ⟨Units.mk0 (P.rep none)⁻¹ (inv_ne_zero hp0), ?_⟩
        funext a
        cases a with
        | none =>
            simp [blowupBaseVector, hp0]
        | some i =>
            simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul,
              blowupBaseVector, v]
            dsimp [t]
            field_simp [hp0, hq]
            exact (eq_div_iff hq).2 (hrel i q)
      exact hmk.trans P.mk_rep
    let w : blowupParameterDomain (k := k) (σ := σ) := ⟨v, hv⟩
    refine ⟨w, ?_⟩
    rw [blowupParameterMap_eq_segreMap]
    have hdir :
        Projectivization.mk k (blowupDirectionVector v)
            (blowupDirectionVector_ne_zero hv) = Q := by
      have hmk : Projectivization.mk k (blowupDirectionVector v)
              (blowupDirectionVector_ne_zero hv) =
            Projectivization.mk k Q.rep Q.rep_nonzero := by
        refine (Projectivization.mk_eq_mk_iff k _ _ _ _).2 ⟨1, ?_⟩
        funext i
        simp [blowupDirectionVector, v]
      exact hmk.trans Q.mk_rep
    calc
      segreMap
          (Projectivization.mk k (blowupBaseVector v)
            (blowupBaseVector_ne_zero v))
          (Projectivization.mk k (blowupDirectionVector v)
            (blowupDirectionVector_ne_zero hv)) =
          segreMap P Q := by rw [hbase, hdir]
      _ = R := hPQ

/-- Property (4): the blow-up incidence locus is irreducible. -/
theorem isIrreducible_blowupSet [IsAlgClosed k] [Finite σ] [Nonempty σ] :
    IsIrreducible (blowupSet (k := k) (σ := σ)) := by
  rw [← range_blowupParameterMap]
  let _ : IrreducibleSpace (blowupParameterDomain (k := k) (σ := σ)) :=
    isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_blowupParameterDomain (k := k) (σ := σ))
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ
      (blowupParameterDomain (k := k) (σ := σ))).image
        (blowupParameterMap (k := k) (σ := σ))
        (continuous_blowupParameterMap (k := k) (σ := σ)).continuousOn

theorem isQuasiProjVariety_of_isIrreducible_isLocallyClosed
    {S : Set (ProjectiveSpace k σ)} (hirr : IsIrreducible S)
    (hloc : IsLocallyClosed S) : IsQuasiProjVariety S := by
  obtain ⟨U, Z, hU, hZ, hSZ⟩ := hloc
  refine ⟨hirr.nonempty, closure S, U,
    ⟨hirr.closure, isClosed_closure⟩, hU, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hxUZ : x ∈ U ∩ Z := hSZ ▸ hx
    exact ⟨subset_closure hx, hxUZ.1⟩
  · rintro x ⟨hxcl, hxU⟩
    have hsub : S ⊆ Z := by
      intro y hy
      exact (hSZ ▸ hy).2
    have hxZ : x ∈ Z := closure_minimal hsub hZ hxcl
    exact hSZ.symm ▸ ⟨hxU, hxZ⟩

theorem isQuasiProjVariety_blowupAmbient [IsAlgClosed k] [Finite σ]
    [DecidableEq σ] [Nonempty σ] :
    IsQuasiProjVariety (blowupAmbient (k := k) (σ := σ)) :=
  isQuasiProjVariety_segreProduct
    (isQuasiProjVariety_standardChart k none)
    (isProjVariety_univ (k := k) (σ := σ)).isQuasiProjVariety

theorem isLocallyClosed_blowupSet [IsAlgClosed k] [Finite σ]
    [DecidableEq σ] [Nonempty σ] :
    IsLocallyClosed (blowupSet (k := k) (σ := σ)) := by
  have hamb : IsLocallyClosed (blowupAmbient (k := k) (σ := σ)) := by
    obtain ⟨-, V, U, hV, hU, hEq⟩ :=
      isQuasiProjVariety_blowupAmbient (k := k) (σ := σ)
    exact ⟨U, V, hU, hV.2, hEq.trans (Set.inter_comm V U)⟩
  obtain ⟨U, Z, hU, hZ, hEq⟩ := hamb
  refine ⟨U, Z ∩ blowupIncidence (k := k) (σ := σ), hU,
    hZ.inter (isClosed_blowupIncidence (k := k) (σ := σ)), ?_⟩
  rw [blowupSet, hEq]
  ext
  simp only [Set.mem_inter_iff]
  tauto

/-- The incidence construction is a quasi-projective variety. -/
theorem isQuasiProjVariety_blowupSet [IsAlgClosed k] [Finite σ]
    [DecidableEq σ] [Nonempty σ] :
    IsQuasiProjVariety (blowupSet (k := k) (σ := σ)) :=
  isQuasiProjVariety_of_isIrreducible_isLocallyClosed
    (isIrreducible_blowupSet (k := k) (σ := σ))
    (isLocallyClosed_blowupSet (k := k) (σ := σ))

end Hartshorne
