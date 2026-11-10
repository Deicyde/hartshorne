/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.DimFormula
import Hartshorne.Dimension.HeightCoheight
import Hartshorne.Scheme.Codimension
import Hartshorne.Scheme.DimensionAtClosedPoint
import Hartshorne.Topology.Subspace

/-!
# The dimension-codimension formula

Hartshorne, *Algebraic Geometry*, Exercise II.3.20 (p. 94).

Let `X` be an integral scheme of finite type over a field and `Y ⊆ X` a nonempty
closed subset. Then `dim Y + codim (Y, X) = dim X`.

The argument works in the poset of irreducible closed subsets of `X`. For an
irreducible closed `T`, the dimension of `T` is its height and its codimension
is its coheight. On an affine open `Spec B` meeting `T`, the irreducible closed
subsets correspond to primes of `B` (with the order reversed), and the
dimension formula for the finitely generated domain `B` says height plus
coheight equals `dim B`. Every nonempty affine open has dimension `dim X`, by
the dimension at a closed point (closed points of an open subset are closed in
`X` because `X` is a Jacobson space). Coheights are computed on any affine open
meeting `T`, while every chain below `T` lies in an affine open around a point of
its smallest member; together these give `height T + coheight T = dim X`. For a
general closed `Y`, the dimension of `Y` is the largest height of an irreducible
closed subset of `Y`, and the codimension is the smallest coheight, so both are
attained at the same irreducible closed subset.

## Main results

* `Hartshorne.dimension_codimension_formula`
-/

namespace Hartshorne

open CategoryTheory TopologicalSpace Topology Order
open AlgebraicGeometry

universe u

noncomputable section

namespace DimensionCodimension

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- Viewed in the ambient space, the trace on an open subspace of an irreducible
closed subset meeting it has closure the original subset. -/
theorem map_orderIso_symm {f : β → α} (hf : IsOpenEmbedding f) (T : IrreducibleCloseds α)
    (hT : (f ⁻¹' T).Nonempty) :
    IrreducibleCloseds.map f hf.continuous
      ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨T, hT⟩) = T :=
  congrArg Subtype.val
    ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).apply_symm_apply ⟨T, hT⟩)

/-- Coheights of irreducible closed subsets meeting an open subspace are computed
in the subspace. -/
theorem coheight_orderIso_symm {f : β → α} (hf : IsOpenEmbedding f) (T : IrreducibleCloseds α)
    (hT : (f ⁻¹' T).Nonempty) :
    coheight ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨T, hT⟩) =
      coheight T := by
  rw [← hf.coheight_map, map_orderIso_symm]

/-- The height of the trace on an open subspace is at most the height in the
ambient space. -/
theorem height_orderIso_symm_le {f : β → α} (hf : IsOpenEmbedding f) (T : IrreducibleCloseds α)
    (hT : (f ⁻¹' T).Nonempty) :
    height ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨T, hT⟩) ≤ height T := by
  conv_rhs => rw [← map_orderIso_symm hf T hT]
  exact height_le_height_apply_of_strictMono _
    (IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing) _

/-- A chain of irreducible closed subsets whose smallest member meets an open
subspace is bounded by the height of the trace of its largest member. -/
theorem length_le_height_orderIso_symm {f : β → α} (hf : IsOpenEmbedding f)
    (l : LTSeries (IrreducibleCloseds α)) (h0 : (f ⁻¹' (l 0 : Set α)).Nonempty) :
    l.length ≤ height ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm
      ⟨l.last, h0.mono (Set.preimage_mono (l.monotone (Fin.zero_le _)))⟩) := by
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf
  have hmeet : ∀ i, (f ⁻¹' (l i : Set α)).Nonempty := fun i =>
    h0.mono (Set.preimage_mono (l.monotone (Fin.zero_le i)))
  let l' : LTSeries (IrreducibleCloseds β) :=
    ⟨l.length, fun i => e.symm ⟨l i, hmeet i⟩, fun i => e.symm.strictMono (l.step i)⟩
  exact length_le_height_last (p := l')

end Topology

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The sections over an affine open of a scheme of finite type over `k` form a
finitely generated `k`-algebra. -/
theorem exists_algebra_finiteType (hf : FiniteType f) (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ _ : Algebra k Γ(X, U), Algebra.FiniteType k Γ(X, U) := by
  let _ : LocallyOfFiniteType f := hf.1
  have hUle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let φU : k →+* Γ(X, U) :=
    (f.appLE ⊤ U hUle).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hinv : Function.Surjective (Scheme.ΓSpecIso (.of k)).inv := by
    intro z
    exact ⟨(Scheme.ΓSpecIso (.of k)).hom z, by simp⟩
  have hφU : φU.FiniteType :=
    (f.finiteType_appLE (isAffineOpen_top _) hU hUle).comp
      (RingHom.FiniteType.of_surjective _ hinv)
  exact ⟨φU.toAlgebra, hφU⟩

/-- Every nonempty affine open of an integral scheme of finite type over a field
has the dimension of the scheme, and this dimension is finite. -/
theorem exists_ringKrullDim_eq [IsIntegral X] (hf : FiniteType f) (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    ∃ N : ℕ, ringKrullDim Γ(X, U) = N ∧ topologicalKrullDim X = N := by
  obtain ⟨_, _⟩ := exists_algebra_finiteType f hf U hU
  let _ : LocallyOfFiniteType f := hf.1
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxU, hxc⟩ := nonempty_inter_closedPoints (X := X) (Z := (U : Set X))
    (by simpa using (inferInstance : Nonempty U)) U.isOpen.isLocallyClosed
  have : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k _
  obtain ⟨x', hxc⟩ : ∃ x' : U, IsClosed {(x' : X)} := ⟨⟨x, hxU⟩, hxc⟩
  let p := (hU.primeIdealOf x').asIdeal
  have : p.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed x' hxc
  have : IsLocalization.AtPrime (X.presheaf.stalk (x' : X)) p := hU.isLocalization_stalk x'
  obtain ⟨N, hN⟩ : ∃ N : ℕ, p.height = N :=
    ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ e => e.symm
  have hpheight : ((p.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim Γ(X, U) :=
    height_eq_ringKrullDim_of_isMaximal k Γ(X, U) p
  have hlocal : ringKrullDim (X.presheaf.stalk (x' : X)) = ((p.height : ℕ∞) : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p _
  refine ⟨N, ?_, ?_⟩
  · rw [← hpheight, hN]; rfl
  · rw [dimension_at_closed_point f hf x' hxc, hlocal, hN]; rfl

/-- On an affine open, height plus coheight of an irreducible closed subset is the
dimension of the scheme. -/
theorem height_add_coheight_affine [IsIntegral X] (hf : FiniteType f) (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] (Z : IrreducibleCloseds (Spec Γ(X, U))) :
    (((height Z + coheight Z : ℕ∞)) : WithBot ℕ∞) = topologicalKrullDim X := by
  obtain ⟨_, _⟩ := exists_algebra_finiteType f hf U hU
  obtain ⟨N, hNring, hNtop⟩ := exists_ringKrullDim_eq f hf U hU
  let P : PrimeSpectrum Γ(X, U) :=
    (PrimeSpectrum.pointsEquivIrreducibleCloseds Γ(X, U)).symm (OrderDual.toDual Z)
  have hZ : OrderDual.toDual Z = PrimeSpectrum.pointsEquivIrreducibleCloseds Γ(X, U) P :=
    ((PrimeSpectrum.pointsEquivIrreducibleCloseds Γ(X, U)).apply_symm_apply _).symm
  have : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k _
  have hcoh : coheight Z = height P := by
    have h1 := height_orderIso (PrimeSpectrum.pointsEquivIrreducibleCloseds Γ(X, U)) P
    rw [← hZ] at h1
    exact h1
  have hht : height Z = coheight P := by
    have h1 := coheight_orderIso (PrimeSpectrum.pointsEquivIrreducibleCloseds Γ(X, U)) P
    rw [← hZ] at h1
    exact h1
  obtain ⟨h, hh⟩ : ∃ h : ℕ, P.asIdeal.height = h :=
    ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ e => e.symm
  have hform := height_add_ringKrullDim_quotient_eq k Γ(X, U) P.asIdeal h hh
  rw [ringKrullDim_quotient_eq_coheight, hNring] at hform
  have hP : height P = h := (PrimeSpectrum.height_eq_orderHeight P).symm.trans hh
  rw [hNtop, hcoh, hht, add_comm, hP]
  exact_mod_cast hform

/-- **Height plus coheight.** For an integral scheme of finite type over a field,
every irreducible closed subset has height plus coheight equal to the dimension. -/
theorem height_add_coheight [IsIntegral X] (hf : FiniteType f) (T : IrreducibleCloseds X) :
    (((height T + coheight T : ℕ∞)) : WithBot ℕ∞) = topologicalKrullDim X := by
  -- Every nonempty set meets the range of the inclusion of some affine open.
  have cover : ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ Set.range hU.fromSpec := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (⊤ : X.Opens) from trivial) isOpen_univ
    exact ⟨U, hU, by rwa [hU.range_fromSpec]⟩
  obtain ⟨t, ht⟩ := T.isIrreducible.nonempty
  obtain ⟨U, hU, y, hy⟩ := cover t
  have : Nonempty U :=
    ⟨⟨t, show t ∈ (U : Set X) by rw [← hU.range_fromSpec]; exact ⟨y, hy⟩⟩⟩
  obtain ⟨N, -, hN⟩ := exists_ringKrullDim_eq f hf U hU
  rw [hN]
  have hTU : (hU.fromSpec ⁻¹' (T : Set X)).Nonempty := ⟨y, by simpa [hy] using ht⟩
  have hemb := hU.fromSpec.isOpenEmbedding
  -- The coheight of `T` is computed on any affine open meeting it.
  have hcoh : ∀ (V : X.Opens) (hV : IsAffineOpen V) (hTV : (hV.fromSpec ⁻¹' (T : Set X)).Nonempty),
      coheight T = coheight ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _
        hV.fromSpec.isOpenEmbedding).symm ⟨T, hTV⟩) := fun V hV hTV =>
    (coheight_orderIso_symm _ T hTV).symm
  have hlow := height_add_coheight_affine f hf U hU
    ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hemb).symm ⟨T, hTU⟩)
  rw [hN, ← hcoh U hU hTU] at hlow
  have hlow' : height ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hemb).symm
      ⟨T, hTU⟩) + coheight T = N := by exact_mod_cast hlow
  have hcfin : coheight T ≤ N := hlow' ▸ le_add_self
  obtain ⟨c, hc⟩ : ∃ c : ℕ, coheight T = c :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top N) hcfin) |>.imp
      fun _ e => e.symm
  have hcN : c ≤ N := by exact_mod_cast hc ▸ hcfin
  -- Upper bound: every chain below `T` lies in an affine open.
  have hup : height T ≤ ((N - c : ℕ) : ℕ∞) := by
    refine height_le fun l hl => ?_
    subst hl
    obtain ⟨s, hs⟩ := (l 0).isIrreducible.nonempty
    obtain ⟨V, hV, z, hz⟩ := cover s
    have : Nonempty V :=
      ⟨⟨s, show s ∈ (V : Set X) by rw [← hV.range_fromSpec]; exact ⟨z, hz⟩⟩⟩
    have h0 : (hV.fromSpec ⁻¹' (l 0 : Set X)).Nonempty := ⟨z, by simpa [hz] using hs⟩
    have hlen := length_le_height_orderIso_symm hV.fromSpec.isOpenEmbedding l h0
    have hTV : (hV.fromSpec ⁻¹' (l.last : Set X)).Nonempty := by
      exact h0.mono (Set.preimage_mono (l.monotone (Fin.zero_le _)))
    have hV' := height_add_coheight_affine f hf V hV
      ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hV.fromSpec.isOpenEmbedding).symm
        ⟨l.last, hTV⟩)
    obtain ⟨N', -, hN'⟩ := exists_ringKrullDim_eq f hf V hV
    rw [hN'] at hV'
    have hNN : N' = N := by exact_mod_cast hN'.symm.trans hN
    subst hNN
    rw [← hcoh V hV hTV, hc] at hV'
    have hV'' : height ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _
        hV.fromSpec.isOpenEmbedding).symm ⟨l.last, hTV⟩) + c = N' := by exact_mod_cast hV'
    have hlen' : (l.length : ℕ∞) ≤ height ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _
        hV.fromSpec.isOpenEmbedding).symm ⟨l.last, hTV⟩) := hlen
    have hfin : height ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _
        hV.fromSpec.isOpenEmbedding).symm ⟨l.last, hTV⟩) = ((N' - c : ℕ) : ℕ∞) := by
      obtain ⟨m, hm⟩ : ∃ m : ℕ, height ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _
          hV.fromSpec.isOpenEmbedding).symm ⟨l.last, hTV⟩) = m :=
        ENat.ne_top_iff_exists.mp (fun htop => by simp [htop] at hV'') |>.imp fun _ e => e.symm
      rw [hm] at hV'' ⊢
      have : m + c = N' := by exact_mod_cast hV''
      congr 1
      omega
    exact hlen'.trans hfin.le
  have hdown := height_orderIso_symm_le hemb T hTU
  refine congrArg _ (le_antisymm ?_ ?_)
  · calc height T + coheight T ≤ ((N - c : ℕ) : ℕ∞) + c := by rw [hc]; gcongr
      _ = N := by norm_cast; omega
  · calc (N : ℕ∞) = _ := hlow'.symm
      _ ≤ height T + coheight T := by gcongr

end Scheme

end DimensionCodimension

namespace FlatEquidimensional

/-- The dimension of the closure of a point is the height of the point in the specialization
order. -/
theorem topologicalKrullDim_closure_singleton {S : Scheme.{u}} (g : S) :
    topologicalKrullDim (closure ({g} : Set S)) = (height g : WithBot ℕ∞) := by
  rw [topologicalKrullDim_subtype_eq isClosed_closure]
  let e : IrreducibleCloseds S ≃o S := irreducibleSetEquivPoints
  let Z₀ : IrreducibleCloseds S := e.symm g
  change Order.krullDim (Set.Iic Z₀) = _
  rw [← height_eq_krullDim_Iic, ← height_orderIso e.symm g]

end FlatEquidimensional

open DimensionCodimension

/-- **Exercise II.3.20 (dimension-codimension formula).** For an integral scheme `X`
of finite type over a field and a nonempty closed subset `Y ⊆ X`,
`dim Y + codim (Y, X) = dim X`. -/
theorem dimension_codimension_formula
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsIntegral X] (hf : FiniteType f)
    (Y : Set X) (hY : IsClosed Y) (hne : Y.Nonempty) :
    topologicalKrullDim Y + (codim Y : WithBot ℕ∞) = topologicalKrullDim X := by
  -- The irreducible closed subsets contained in `Y`.
  let S : Set (IrreducibleCloseds X) := {Z | (Z : Set X) ⊆ Y}
  obtain ⟨y, hy⟩ := hne
  have hS : S.Nonempty :=
    ⟨⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩,
      closure_minimal (Set.singleton_subset_iff.mpr hy) hY⟩
  let Z₀ := Function.argminOn (fun Z : IrreducibleCloseds X => coheight Z) S hS
  have hZ₀ : Z₀ ∈ S := Function.argminOn_mem _ _ _
  have hcodim : codim Y = coheight Z₀ :=
    le_antisymm (iInf₂_le Z₀ hZ₀) (le_iInf₂ fun Z hZ => Function.argminOn_le _ _ hZ)
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ (⊤ : X.Opens) from trivial) isOpen_univ
  -- The heights of members of `S` are bounded by that of `Z₀`.
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  have hmax : ∀ Z ∈ S, height Z ≤ height Z₀ := by
    intro Z hZ
    obtain ⟨N, -, hN⟩ := exists_ringKrullDim_eq f hf U hU
    have h1 := height_add_coheight f hf Z
    have h2 := height_add_coheight f hf Z₀
    rw [hN] at h1 h2
    have h1' : height Z + coheight Z = N := by exact_mod_cast h1
    have h2' : height Z₀ + coheight Z₀ = N := by exact_mod_cast h2
    have hle : coheight Z₀ ≤ coheight Z := Function.argminOn_le _ _ hZ
    have fin : ∀ a b : ℕ∞, a + b = N → ∃ m n : ℕ, a = m ∧ b = n := by
      intro a b h
      lift a to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top N) (h ▸ le_self_add)
      lift b to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top N) (h ▸ le_add_self)
      exact ⟨a, b, rfl, rfl⟩
    obtain ⟨a, b, ha, hb⟩ := fin _ _ h1'
    obtain ⟨c, d, hc, hd⟩ := fin _ _ h2'
    rw [ha, hb] at h1'
    rw [hc, hd] at h2'
    rw [hb, hd] at hle
    rw [ha, hc]
    have : a + b = N := by exact_mod_cast h1'
    have : c + d = N := by exact_mod_cast h2'
    have : d ≤ b := by exact_mod_cast hle
    exact_mod_cast (by omega : a ≤ c)
  -- The dimension of `Y` is the height of `Z₀`.
  have hdimY : topologicalKrullDim Y = (height Z₀ : WithBot ℕ∞) := by
    apply le_antisymm
    · refine iSup_le fun l => ?_
      let l' := l.map (IrreducibleCloseds.map Subtype.val continuous_subtype_val)
        (IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal)
      have hlast : l'.last ∈ S := by
        change closure (Subtype.val '' (l.last : Set Y)) ⊆ Y
        exact closure_minimal (by simp) hY
      have := (length_le_height_last (p := l')).trans (hmax _ hlast)
      exact_mod_cast this
    · let g : Set.Iic Z₀ → IrreducibleCloseds Y := fun V =>
        ⟨(Subtype.val : Y → X) ⁻¹' (V.1 : Set X),
          isIrreducible_preimage_val hY V.1.isIrreducible (V.2.trans hZ₀),
          V.1.isClosed.preimage continuous_subtype_val⟩
      have hg : StrictMono g := by
        intro a b hab
        refine lt_of_le_of_ne (fun x hx => hab.le hx) fun heq => hab.ne ?_
        apply Subtype.ext
        apply SetLike.coe_injective
        have := congrArg (fun W : IrreducibleCloseds Y => Subtype.val '' (W : Set Y)) heq
        simpa [g, Set.image_preimage_eq_inter_range, Subtype.range_coe,
          Set.inter_eq_left.mpr (a.2.trans hZ₀), Set.inter_eq_left.mpr (b.2.trans hZ₀)] using this
      calc (height Z₀ : WithBot ℕ∞) = krullDim (Set.Iic Z₀) := height_eq_krullDim_Iic Z₀
        _ ≤ topologicalKrullDim Y := krullDim_le_of_strictMono g hg
  rw [hdimY, hcodim]
  exact_mod_cast height_add_coheight f hf Z₀

end

end Hartshorne
