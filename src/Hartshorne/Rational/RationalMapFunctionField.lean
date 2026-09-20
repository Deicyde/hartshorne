/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.RationalMap
import Hartshorne.Rational.AffineOpenBasis
import Hartshorne.Morphism.VarietyFunctionFieldHom
import Hartshorne.Morphism.GlobalLocalIntersection
import Hartshorne.Morphism.HomAffine
import Mathlib.RingTheory.FiniteType

/-!
# Dominant rational maps and function fields

A dominant rational map `X ⇢ Y` pulls rational functions back to give a
`k`-algebra homomorphism `K(Y) → K(X)`.  The construction is independent of the
chosen rational-map representative, preserves identities, and reverses
composition.  For an affine target, every such field homomorphism arises from
a unique dominant rational map; the general theorem is obtained from this case
in `Hartshorne.Rational.RationalMapFunctionFieldEquivalence`.

## Main definitions

* `Hartshorne.DominantRatMap.functionFieldAlgHom`
* `Hartshorne.RatMap.functionFieldAlgHom`
* `Hartshorne.dominantRatMapEquivFunctionFieldAlgHom_affine`
-/

namespace Hartshorne

open TopologicalSpace

universe u v w

variable {k : Type u} [Field k] {X Y : Variety.{u, v} k}

namespace RatMapRep

/-- Pull a rational-function representative back along a dominant rational-map
representative, viewing the resulting domain as an open subset of the ambient
source variety. -/
noncomputable def ratPullback (r : RatMapRep X Y) (hr : r.IsDominant)
    (s : Variety.RationalRep Y) : Variety.RationalRep X where
  U := Variety.preimageOpens r.nonempty_U r.hom s.U
  nonempty_U := by
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hr.exists_mem_open s.U.isOpen s.nonempty_U
    refine ⟨x.1, Variety.mem_preimageOpens.2 ⟨x.2, fun h => ?_⟩⟩
    change (s.U : Set Y.carrier) (r.hom ⟨x.1, h⟩)
    have hxeq : (⟨x.1, h⟩ : r.U) = x := Subtype.ext (by rfl)
    rw [hxeq]
    exact hx
  toFun := fun x => s.toFun
    ⟨r.hom ⟨x.1, x.2.1⟩, x.2.2 x.2.1⟩
  regular := by
    exact r.hom.regular_comp s.U s.toFun s.regular

theorem ratPullback_congr (r : RatMapRep X Y) (hr : r.IsDominant)
    {s t : Variety.RationalRep Y} (h : s.Rel t) :
    (r.ratPullback hr s).Rel (r.ratPullback hr t) := by
  intro x hs ht
  exact h (r.hom ⟨x, hs.1⟩) (hs.2 hs.1) (ht.2 ht.1)

/-- Pullback of rational functions along a dominant rational-map
representative. -/
noncomputable def functionFieldAlgHom (r : RatMapRep X Y) (hr : r.IsDominant) :
    Y.FunctionField →ₐ[k] X.FunctionField where
  toFun := Quotient.map (r.ratPullback hr) fun _ _ h => r.ratPullback_congr hr h
  map_one' := Quotient.sound fun _ _ _ => rfl
  map_zero' := Quotient.sound fun _ _ _ => rfl
  map_mul' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl
  map_add' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl
  commutes' c := Quotient.sound fun _ _ _ => rfl

@[simp]
theorem functionFieldAlgHom_mk (r : RatMapRep X Y) (hr : r.IsDominant)
    (s : Variety.RationalRep Y) :
    r.functionFieldAlgHom hr (Quotient.mk (Variety.rationalSetoid Y) s) =
      Quotient.mk (Variety.rationalSetoid X) (r.ratPullback hr s) :=
  rfl

/-- Equivalent dominant rational-map representatives induce the same pullback
on function fields. -/
theorem functionFieldAlgHom_congr {r t : RatMapRep X Y} (h : r.Rel t)
    (hr : r.IsDominant) (ht : t.IsDominant) :
    r.functionFieldAlgHom hr = t.functionFieldAlgHom ht := by
  ext q
  refine Quotient.inductionOn q ?_
  intro s
  apply Quotient.sound
  intro x hx hx'
  exact congrArg s.toFun (Subtype.ext (h x hx.1 hx'.1))

@[simp]
theorem functionFieldAlgHom_id (X : Variety.{u, v} k) :
    (RatMapRep.id X).functionFieldAlgHom (RatMapRep.id_isDominant X) =
      AlgHom.id k X.FunctionField := by
  ext q
  refine Quotient.inductionOn q ?_
  intro s
  apply Quotient.sound
  intro x hx hs
  rfl

theorem functionFieldAlgHom_comp {Z : Variety.{u, v} k}
    (s : RatMapRep Y Z) (r : RatMapRep X Y)
    (hs : s.IsDominant) (hr : r.IsDominant) :
    (s.comp r hr).functionFieldAlgHom (s.comp_isDominant r hs hr) =
      (r.functionFieldAlgHom hr).comp (s.functionFieldAlgHom hs) := by
  ext q
  refine Quotient.inductionOn q ?_
  intro t
  apply Quotient.sound
  intro x hx hx'
  rfl

end RatMapRep

namespace DominantRatMap

/-- A dominant rational map induces the contravariant `k`-algebra homomorphism
on function fields. -/
noncomputable def functionFieldAlgHom {hY : Y.IsSeparated}
    (f : DominantRatMap X Y hY) : Y.FunctionField →ₐ[k] X.FunctionField :=
  Quotient.liftOn f
    (fun r => r.rep.functionFieldAlgHom r.isDominant)
    (fun r t h => RatMapRep.functionFieldAlgHom_congr h r.isDominant t.isDominant)

@[simp]
theorem functionFieldAlgHom_mk {hY : Y.IsSeparated}
    (r : DominantRatMapRep X Y) :
    functionFieldAlgHom (hY := hY) (⟦r⟧ : DominantRatMap X Y hY) =
      r.rep.functionFieldAlgHom r.isDominant :=
  rfl

@[simp]
theorem functionFieldAlgHom_id (X : Variety.{u, v} k) (hX : X.IsSeparated) :
    functionFieldAlgHom (id X hX) = AlgHom.id k X.FunctionField :=
  RatMapRep.functionFieldAlgHom_id X

theorem functionFieldAlgHom_comp {Z : Variety.{u, v} k}
    {hY : Y.IsSeparated} {hZ : Z.IsSeparated}
    (g : DominantRatMap Y Z hZ) (f : DominantRatMap X Y hY) :
    functionFieldAlgHom (comp g f) =
      (functionFieldAlgHom f).comp (functionFieldAlgHom g) := by
  refine Quotient.inductionOn₂ f g ?_
  intro r s
  exact RatMapRep.functionFieldAlgHom_comp s.rep r.rep s.isDominant r.isDominant

end DominantRatMap

namespace RatMap

/-- The function-field pullback of an unbundled rational map together with a
proof that it is dominant. -/
noncomputable def functionFieldAlgHom {hY : Y.IsSeparated}
    (f : RatMap X Y hY) (hf : f.IsDominant) :
    Y.FunctionField →ₐ[k] X.FunctionField :=
  DominantRatMap.functionFieldAlgHom
    ((DominantRatMap.equivSubtype (X := X) (Y := Y)).symm ⟨f, hf⟩)

end RatMap

namespace Variety

theorem globalToFunctionFieldAlgHom_injective (X : Variety.{u, v} k) :
    Function.Injective X.globalToFunctionFieldAlgHom :=
  X.globalToFunctionField_injective

/-- A global regular function on an open subvariety, regarded directly as a
rational function on the ambient variety. -/
noncomputable def restrictedGlobalRationalRep (X : Variety.{u, v} k)
    (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty)
    (f : (X.restrict U hU).globalRegular) : X.RationalRep where
  U := pushOpens U ⊤
  nonempty_U := by
    obtain ⟨x, hx⟩ := hU
    exact ⟨x, hx, fun _ => trivial⟩
  toFun w := f.1 (ofPush w)
  regular := f.property

/-- Inclusion of regular functions on `U` into `K(X)`. -/
noncomputable def restrictedGlobalToFunctionFieldAlgHom (X : Variety.{u, v} k)
    (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty) :
    (X.restrict U hU).globalRegular →ₐ[k] X.FunctionField where
  toFun f := Quotient.mk _ (X.restrictedGlobalRationalRep U hU f)
  map_one' := Quotient.sound fun _ _ _ => rfl
  map_mul' _ _ := Quotient.sound fun _ _ _ => rfl
  map_zero' := Quotient.sound fun _ _ _ => rfl
  map_add' _ _ := Quotient.sound fun _ _ _ => rfl
  commutes' _ := Quotient.sound fun _ _ _ => rfl

theorem restrictedGlobalToFunctionFieldAlgHom_injective (X : Variety.{u, v} k)
    (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty) :
    Function.Injective (X.restrictedGlobalToFunctionFieldAlgHom U hU) := by
  intro f g hfg
  apply Subtype.ext
  funext z
  change (Quotient.mk _ (X.restrictedGlobalRationalRep U hU f) : X.FunctionField) =
    Quotient.mk _ (X.restrictedGlobalRationalRep U hU g) at hfg
  have hrel := Quotient.exact hfg
  let w := toPush z
  let hwmem : w.1 ∈ pushOpens U ⊤ := w.2
  let w' : pushOpens U ⊤ := ⟨w.1, hwmem⟩
  have h := hrel w.1 hwmem hwmem
  change f.1 (ofPush w') = g.1 (ofPush w') at h
  have hww : w' = w := Subtype.ext (by rfl)
  rw [hww, show ofPush w = z from ofPush_toPush z] at h
  exact h

end Variety

namespace VarietyHom

/-- Algebra-hom version of pullback on function fields. -/
noncomputable def functionFieldAlgHom (f : VarietyHom X Y)
    (hd : Dense (Set.range f.toFun)) :
    Y.FunctionField →ₐ[k] X.FunctionField where
  __ := f.functionFieldHom hd
  commutes' _ := Quotient.sound fun _ _ _ => rfl

end VarietyHom

section CommonDomain

variable {A : Type w} [CommRing A] [Algebra k A]

/-- A common domain for representatives of finitely many rational functions. -/
noncomputable def commonDomain (q : A → X.FunctionField) (s : Finset A) :
    Opens X.carrier :=
  s.inf fun a => (Quotient.out (q a)).U

omit [CommRing A] [Algebra k A] in
theorem commonDomain_le (q : A → X.FunctionField) (s : Finset A)
    {a : A} (ha : a ∈ s) : commonDomain q s ≤ (Quotient.out (q a)).U := by
  exact Finset.inf_le ha

omit [CommRing A] [Algebra k A] in
theorem commonDomain_nonempty (q : A → X.FunctionField) (s : Finset A) :
    ((commonDomain q s : Opens X.carrier) : Set X.carrier).Nonempty := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change ((⊤ : Opens X.carrier) : Set X.carrier).Nonempty
      exact X.nonempty.elim fun x => ⟨x, trivial⟩
  | @insert a s ha ih =>
      simpa [commonDomain, ha] using
        (Variety.opens_inter_nonempty (Quotient.out (q a)).nonempty_U ih)

/-- On the common domain, each chosen representative is globally regular. -/
noncomputable def commonRegular (q : A → X.FunctionField) (s : Finset A)
    (a : A) (ha : a ∈ s) :
    (X.restrict (commonDomain q s) (commonDomain_nonempty q s)).globalRegular where
  val z :=
    (Quotient.out (q a)).toFun
      ⟨z.1.1, commonDomain_le q s ha z.1.2⟩
  property := by
    apply X.regular_restrict
      (show pushOpens (commonDomain q s)
          (⊤ : Opens (X.restrict (commonDomain q s)
            (commonDomain_nonempty q s)).carrier) ≤
          (Quotient.out (q a)).U from fun x hx =>
            commonDomain_le q s ha hx.1)
      (Quotient.out (q a)).regular

/-- The inclusion of a nonempty open subvariety has dense range. -/
theorem Variety.dense_range_inclHom_open (U : Opens X.carrier)
    (hU : (U : Set X.carrier).Nonempty) :
    Dense (Set.range (X.inclHom U hU).toFun) := by
  have hrange : Set.range (X.inclHom U hU).toFun = (U : Set X.carrier) := by
    ext x
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange]
  exact Variety.dense_of_isOpen_of_nonempty U.isOpen hU

omit [CommRing A] [Algebra k A] in
theorem functionFieldAlgHom_commonRegular
    (q : A → X.FunctionField) (s : Finset A) (a : A) (ha : a ∈ s) :
    (X.inclHom (commonDomain q s) (commonDomain_nonempty q s)).functionFieldAlgHom
        (X.dense_range_inclHom_open (commonDomain q s) (commonDomain_nonempty q s))
        (q a) =
      Variety.globalToFunctionFieldAlgHom
        (X.restrict (commonDomain q s) (commonDomain_nonempty q s))
        (commonRegular q s a ha) := by
  rw [← Quotient.out_eq (q a)]
  exact Quotient.sound fun _ _ _ => rfl

omit [CommRing A] [Algebra k A] in
theorem restrictedGlobalToFunctionField_commonRegular
    (q : A → X.FunctionField) (s : Finset A) (a : A) (ha : a ∈ s) :
    X.restrictedGlobalToFunctionFieldAlgHom
        (commonDomain q s) (commonDomain_nonempty q s)
        (commonRegular q s a ha) = q a := by
  rw [← Quotient.out_eq (q a)]
  exact Quotient.sound fun _ _ _ => rfl

theorem exists_finset_adjoin_eq_top [Algebra.FiniteType k A] :
    ∃ s : Finset A, Algebra.adjoin k (↑s : Set A) = ⊤ := by
  obtain ⟨t, ht, htop⟩ := Subalgebra.fg_def.mp (Algebra.FiniteType.out (R := k) (A := A))
  exact ⟨ht.toFinset, by simpa using htop⟩

/-- A homomorphism from a finite type algebra to the function field becomes
regular on one nonempty open set. -/
theorem exists_regular_lift [Algebra.FiniteType k A]
    (θ : A →ₐ[k] X.FunctionField) :
    ∃ (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty)
      (θU : A →ₐ[k] (X.restrict U hU).globalRegular),
      (X.restrict U hU).globalToFunctionFieldAlgHom.comp θU =
        ((X.inclHom U hU).functionFieldAlgHom
          (X.dense_range_inclHom_open U hU)).comp θ := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_adjoin_eq_top (k := k) (A := A)
  let U := commonDomain θ s
  let hU := commonDomain_nonempty θ s
  let j : VarietyHom (X.restrict U hU) X := X.inclHom U hU
  let hj : Dense (Set.range j.toFun) := X.dense_range_inclHom_open U hU
  let Θ : A →ₐ[k] (X.restrict U hU).FunctionField :=
    (j.functionFieldAlgHom hj).comp θ
  let e : (X.restrict U hU).globalRegular →ₐ[k]
      (X.restrict U hU).FunctionField :=
    (X.restrict U hU).globalToFunctionFieldAlgHom
  have hgen : ∀ a : A, Θ a ∈ e.range := by
    have hsub : (↑s : Set A) ⊆ (Subalgebra.comap Θ e.range : Set A) := by
      intro a ha
      change Θ a ∈ e.range
      refine ⟨commonRegular θ s a ha, ?_⟩
      exact (functionFieldAlgHom_commonRegular θ s a ha).symm
    have hadj := Algebra.adjoin_le hsub
    rw [hs] at hadj
    intro a
    exact hadj (Set.mem_univ a)
  let liftFun : A → (X.restrict U hU).globalRegular :=
    fun a => Classical.choose (hgen a)
  have hliftFun (a : A) : e (liftFun a) = Θ a :=
    Classical.choose_spec (hgen a)
  let θU : A →ₐ[k] (X.restrict U hU).globalRegular :=
    { toFun := liftFun
      map_one' := by
        apply (X.restrict U hU).globalToFunctionFieldAlgHom_injective
        rw [hliftFun]
        exact Θ.map_one
      map_mul' := by
        intro a b
        apply (X.restrict U hU).globalToFunctionFieldAlgHom_injective
        rw [map_mul, hliftFun, hliftFun, hliftFun]
        exact Θ.map_mul a b
      map_zero' := by
        apply (X.restrict U hU).globalToFunctionFieldAlgHom_injective
        rw [hliftFun]
        exact Θ.map_zero
      map_add' := by
        intro a b
        apply (X.restrict U hU).globalToFunctionFieldAlgHom_injective
        rw [map_add, hliftFun, hliftFun, hliftFun]
        exact Θ.map_add a b
      commutes' := by
        intro c
        apply (X.restrict U hU).globalToFunctionFieldAlgHom_injective
        rw [hliftFun]
        exact Θ.commutes c }
  refine ⟨U, hU, θU, ?_⟩
  ext a
  exact hliftFun a

/-- Cleaner ambient-field form of `exists_regular_lift`. -/
theorem exists_regular_lift_ambient [Algebra.FiniteType k A]
    (θ : A →ₐ[k] X.FunctionField) :
    ∃ (U : Opens X.carrier) (hU : (U : Set X.carrier).Nonempty)
      (θU : A →ₐ[k] (X.restrict U hU).globalRegular),
      (X.restrictedGlobalToFunctionFieldAlgHom U hU).comp θU = θ := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_adjoin_eq_top (k := k) (A := A)
  let U := commonDomain θ s
  let hU := commonDomain_nonempty θ s
  let e : (X.restrict U hU).globalRegular →ₐ[k] X.FunctionField :=
    X.restrictedGlobalToFunctionFieldAlgHom U hU
  have hgen : ∀ a : A, θ a ∈ e.range := by
    have hsub : (↑s : Set A) ⊆ (Subalgebra.comap θ e.range : Set A) := by
      intro a ha
      change θ a ∈ e.range
      refine ⟨commonRegular θ s a ha, ?_⟩
      exact restrictedGlobalToFunctionField_commonRegular θ s a ha
    have hadj := Algebra.adjoin_le hsub
    rw [hs] at hadj
    intro a
    exact hadj (Set.mem_univ a)
  let liftFun : A → (X.restrict U hU).globalRegular :=
    fun a => Classical.choose (hgen a)
  have hliftFun (a : A) : e (liftFun a) = θ a :=
    Classical.choose_spec (hgen a)
  let θU : A →ₐ[k] (X.restrict U hU).globalRegular :=
    { toFun := liftFun
      map_one' := by
        apply X.restrictedGlobalToFunctionFieldAlgHom_injective U hU
        rw [hliftFun]
        simp
      map_mul' := by
        intro a b
        apply X.restrictedGlobalToFunctionFieldAlgHom_injective U hU
        rw [map_mul, hliftFun, hliftFun, hliftFun]
        exact θ.map_mul a b
      map_zero' := by
        apply X.restrictedGlobalToFunctionFieldAlgHom_injective U hU
        rw [hliftFun]
        simp
      map_add' := by
        intro a b
        apply X.restrictedGlobalToFunctionFieldAlgHom_injective U hU
        rw [map_add, hliftFun, hliftFun, hliftFun]
        exact θ.map_add a b
      commutes' := by
        intro c
        apply X.restrictedGlobalToFunctionFieldAlgHom_injective U hU
        rw [hliftFun]
        simp }
  refine ⟨U, hU, θU, ?_⟩
  ext a
  exact hliftFun a

end CommonDomain

section AffineDominance

open MvPolynomial

variable [IsAlgClosed k] {A : Variety.{u, u} k}
  {σ : Type u} [Finite σ] {Z : Set (σ → k)}

/-- The coordinate ring inside the abstract function field of an affine
variety. -/
noncomputable def affineCoordToFunctionFieldAlgHom (hZ : IsAffineVariety Z) :
    coordinateRing Z →ₐ[k]
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField :=
  (Variety.globalToFunctionFieldAlgHom
    (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)).comp
    (coordinateRingEquivRegularTop hZ).toAlgHom

theorem affineFunctionField_algHom_ext {L : Type u} [Field L] [Algebra k L]
    (hZ : IsAffineVariety Z)
    {f g : (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField →ₐ[k] L}
    (h : f.comp (affineCoordToFunctionFieldAlgHom hZ) =
      g.comp (affineCoordToFunctionFieldAlgHom hZ)) : f = g := by
  let _ : IsDomain (coordinateRing Z) := isDomain_coordinateRing hZ
  let _ : IsFractionRing (coordinateRing Z) (FunctionField hZ.isIrreducible) :=
    isFractionRing_functionField hZ.isIrreducible
  let _ : Field (FunctionField hZ.isIrreducible) :=
    IsFractionRing.toField (coordinateRing Z)
  let e := functionFieldEquivAffine hZ.isQuasiAffineVariety
  let F : FunctionField hZ.isIrreducible →+* L :=
    f.toRingHom.comp e.symm.toRingHom
  let G : FunctionField hZ.isIrreducible →+* L :=
    g.toRingHom.comp e.symm.toRingHom
  have hbase : ∀ a : coordinateRing Z,
      F (algebraMap (coordinateRing Z) (FunctionField hZ.isIrreducible) a) =
        G (algebraMap (coordinateRing Z) (FunctionField hZ.isIrreducible) a) := by
    intro a
    have ha := congrArg
      (fun q : coordinateRing Z →ₐ[k] L => q a) h
    change f (affineCoordToFunctionFieldAlgHom hZ a) =
      g (affineCoordToFunctionFieldAlgHom hZ a) at ha
    have hcoord := coordToRational_eq_globalToFunctionField hZ a
    have hcoord' : e.symm (coordToRational hZ.isIrreducible a) =
        affineCoordToFunctionFieldAlgHom hZ a := by
      rw [hcoord]
      exact e.symm_apply_apply _
    change f (e.symm (coordToRational hZ.isIrreducible a)) =
      g (e.symm (coordToRational hZ.isIrreducible a))
    rw [hcoord']
    exact ha
  have hFG : F = G := IsFractionRing.ringHom_ext
    (A := coordinateRing Z) (K := FunctionField hZ.isIrreducible)
    (L := L) (f1 := F) (f2 := G) hbase
  apply AlgHom.ext
  intro q
  have hq := congrArg (fun m : FunctionField hZ.isIrreducible →+* L => m (e q)) hFG
  simpa [F, G, e] using hq

theorem RatMapRep.functionFieldAlgHom_comp_affineCoord
    (hZ : IsAffineVariety Z)
    (r : RatMapRep A (Variety.ofQuasiAffine hZ.isQuasiAffineVariety))
    (hr : r.IsDominant) :
    (r.functionFieldAlgHom hr).comp (affineCoordToFunctionFieldAlgHom hZ) =
      (A.restrictedGlobalToFunctionFieldAlgHom r.U r.nonempty_U).comp
        (homToAlgHom hZ r.hom) := by
  ext a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Quotient.sound
  intro x hx hx'
  rfl

theorem RatMapRep.rel_of_functionFieldAlgHom_eq_affine
    (hZ : IsAffineVariety Z)
    {r s : DominantRatMapRep A
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)}
    (h : r.rep.functionFieldAlgHom r.isDominant =
      s.rep.functionFieldAlgHom s.isDominant) : r.rep.Rel s.rep := by
  intro x hr hs
  apply Subtype.ext
  funext i
  let a : coordinateRing Z :=
    Ideal.Quotient.mk _ (MvPolynomial.X i)
  have ha := congrArg
    (fun F : (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField →ₐ[k]
        A.FunctionField => F (affineCoordToFunctionFieldAlgHom hZ a)) h
  have hrel := Quotient.exact ha
  have hxr : x ∈ (r.rep.ratPullback r.isDominant
      ((Variety.ofQuasiAffine hZ.isQuasiAffineVariety).globalRationalRep
        (coordinateRingEquivRegularTop hZ a))).U := by
    exact ⟨hr, fun _ => trivial⟩
  have hxs : x ∈ (s.rep.ratPullback s.isDominant
      ((Variety.ofQuasiAffine hZ.isQuasiAffineVariety).globalRationalRep
        (coordinateRingEquivRegularTop hZ a))).U := by
    exact ⟨hs, fun _ => trivial⟩
  have hx := hrel x hxr hxs
  have hcoord (y : (⊤ : Opens
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).carrier)) :
      (coordinateRingEquivRegularTop hZ a).1 y = y.1.1 i := by
    change MvPolynomial.eval y.1.1 (MvPolynomial.X i) = y.1.1 i
    exact MvPolynomial.eval_X i
  change (coordinateRingEquivRegularTop hZ a).1
      ⟨r.rep.eval hr, trivial⟩ =
    (coordinateRingEquivRegularTop hZ a).1
      ⟨s.rep.eval hs, trivial⟩ at hx
  simpa only [hcoord] using hx
  /- Keep this expansion recorded for robustness when inspecting elaboration:
    [a, affineCoordToFunctionFieldAlgHom,
    Variety.globalToFunctionFieldAlgHom,
    Variety.globalRationalRep, RatMapRep.functionFieldAlgHom,
    RatMapRep.ratPullback, coordinateRingEquivRegularTop,
    coordinateToRegular_mk, polynomialToRegular_apply]. -/

omit [IsAlgClosed k] [Finite σ] in
/-- For a morphism into an affine variety, injectivity on coordinate rings is
equivalent to the direction needed here: its range is dense. -/
theorem dense_range_of_injective_homToAlgHom (hZ : IsAffineVariety Z)
    (f : VarietyHom A (Variety.ofQuasiAffine hZ.isQuasiAffineVariety))
    (hf : Function.Injective (homToAlgHom hZ f)) :
    Dense (Set.range f.toFun) := by
  let T : Set (σ → k) := Set.range fun x : A.carrier => (f x).1
  have hTZ : T ⊆ Z := by
    rintro _ ⟨x, rfl⟩
    exact (f x).2
  have hI : vanishingIdeal k T = vanishingIdeal k Z := by
    apply le_antisymm
    · intro p hp
      have hm : homToAlgHom hZ f (Ideal.Quotient.mk _ p) = 0 := by
        apply Subtype.ext
        funext x
        rw [homToAlgHom_val]
        simp only [coordinateToRegular_mk]
        exact hp _ ⟨x.1, rfl⟩
      have hq : (Ideal.Quotient.mk _ p : coordinateRing Z) = 0 := by
        apply hf
        simpa using hm
      exact Ideal.Quotient.eq_zero_iff_mem.mp hq
    · exact vanishingIdeal_anti_mono hTZ
  have hclosure : closure T = Z := by
    rw [← zeroLocus_vanishingIdeal_eq_closure, hI,
      hZ.isAlgebraicSet.zeroLocus_vanishingIdeal]
  rw [dense_iff_inter_open]
  intro W hW hWne
  obtain ⟨w, hwW⟩ := hWne
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  have hwO : w.1 ∈ O := by
    rw [← hOW] at hwW
    exact hwW
  have hwcl : w.1 ∈ closure T := by
    rw [hclosure]
    exact w.2
  rw [mem_closure_iff] at hwcl
  obtain ⟨z, hzO, hzT⟩ := hwcl O hO hwO
  obtain ⟨x, rfl⟩ := hzT
  refine ⟨f x, ?_, ⟨x, rfl⟩⟩
  rw [← hOW]
  exact hzO

omit [IsAlgClosed k] in
/-- An injective map from an affine coordinate ring to `K(X)` is represented
by a dominant morphism on one nonempty open subset of `X`. -/
theorem exists_dominant_open_morphism_to_affine (hZ : IsAffineVariety Z)
    (θ : coordinateRing Z →ₐ[k] A.FunctionField)
    (hθ : Function.Injective θ) :
    ∃ (U : Opens A.carrier) (hU : (U : Set A.carrier).Nonempty)
      (f : VarietyHom (A.restrict U hU)
        (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)),
      Dense (Set.range f.toFun) ∧
      (A.restrictedGlobalToFunctionFieldAlgHom U hU).comp
          (homToAlgHom hZ f) = θ := by
  obtain ⟨U, hU, θU, hθU⟩ :=
    exists_regular_lift_ambient (X := A) θ
  let f : VarietyHom (A.restrict U hU)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) :=
    (homEquivAlgHom hZ).symm θU
  have hf : homToAlgHom hZ f = θU :=
    (homEquivAlgHom hZ).apply_symm_apply θU
  have hθUinj : Function.Injective θU := by
    intro a b hab
    apply hθ
    have ha := congrArg (fun g : coordinateRing Z →ₐ[k] A.FunctionField => g a) hθU
    have hb := congrArg (fun g : coordinateRing Z →ₐ[k] A.FunctionField => g b) hθU
    rw [AlgHom.comp_apply] at ha hb
    exact ha.symm.trans ((congrArg
      (A.restrictedGlobalToFunctionFieldAlgHom U hU) hab).trans hb)
  refine ⟨U, hU, f, ?_, ?_⟩
  · apply dense_range_of_injective_homToAlgHom hZ f
    rwa [hf]
  · rw [hf]
    exact hθU

omit [IsAlgClosed k] in
theorem exists_dominantRatMapRep_to_affine (hZ : IsAffineVariety Z)
    (θ : coordinateRing Z →ₐ[k] A.FunctionField)
    (hθ : Function.Injective θ) :
    ∃ r : DominantRatMapRep A
        (Variety.ofQuasiAffine hZ.isQuasiAffineVariety),
      (A.restrictedGlobalToFunctionFieldAlgHom r.rep.U r.rep.nonempty_U).comp
          (homToAlgHom hZ r.rep.hom) = θ := by
  obtain ⟨U, hU, f, hfdense, hf⟩ :=
    exists_dominant_open_morphism_to_affine hZ θ hθ
  exact ⟨⟨⟨U, hU, f⟩, hfdense⟩, hf⟩

/-- The inverse direction of Theorem 4.4 for an affine target. -/
theorem exists_dominantRatMapRep_functionFieldAlgHom_eq_affine
    (hZ : IsAffineVariety Z)
    (Θ : (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField →ₐ[k]
      A.FunctionField) :
    ∃ r : DominantRatMapRep A
        (Variety.ofQuasiAffine hZ.isQuasiAffineVariety),
      r.rep.functionFieldAlgHom r.isDominant = Θ := by
  let θ := Θ.comp (affineCoordToFunctionFieldAlgHom hZ)
  have hcoord : Function.Injective (affineCoordToFunctionFieldAlgHom hZ) :=
    (Variety.globalToFunctionFieldAlgHom_injective
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)).comp
        (coordinateRingEquivRegularTop hZ).injective
  have hΘ : Function.Injective Θ := Θ.toRingHom.injective
  have hθ : Function.Injective θ := hΘ.comp hcoord
  obtain ⟨r, hr⟩ := exists_dominantRatMapRep_to_affine hZ θ hθ
  refine ⟨r, affineFunctionField_algHom_ext hZ ?_⟩
  rw [r.rep.functionFieldAlgHom_comp_affineCoord, hr]

theorem DominantRatMap.functionFieldAlgHom_injective_affine
    (hZ : IsAffineVariety Z)
    (hsep : (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).IsSeparated) :
    Function.Injective
      (@DominantRatMap.functionFieldAlgHom k _ A
        (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) hsep) := by
  intro f g hfg
  refine Quotient.inductionOn₂ f g ?_ hfg
  intro r s hrs
  apply Quotient.sound
  exact RatMapRep.rel_of_functionFieldAlgHom_eq_affine hZ hrs

theorem DominantRatMap.functionFieldAlgHom_surjective_affine
    (hZ : IsAffineVariety Z)
    (hsep : (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).IsSeparated) :
    Function.Surjective
      (@DominantRatMap.functionFieldAlgHom k _ A
        (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) hsep) := by
  intro Θ
  obtain ⟨r, hr⟩ :=
    exists_dominantRatMapRep_functionFieldAlgHom_eq_affine hZ Θ
  exact ⟨⟦r⟧, hr⟩

/-- Theorem 4.4 for an affine target. -/
noncomputable def dominantRatMapEquivFunctionFieldAlgHom_affine
    (hZ : IsAffineVariety Z)
    (hsep : (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).IsSeparated) :
    DominantRatMap A (Variety.ofQuasiAffine hZ.isQuasiAffineVariety) hsep ≃
      ((Variety.ofQuasiAffine hZ.isQuasiAffineVariety).FunctionField →ₐ[k]
        A.FunctionField) :=
  Equiv.ofBijective DominantRatMap.functionFieldAlgHom
    ⟨DominantRatMap.functionFieldAlgHom_injective_affine hZ hsep,
      DominantRatMap.functionFieldAlgHom_surjective_affine hZ hsep⟩

end AffineDominance

end Hartshorne
