/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeProjPushforwardTwist
import Hartshorne.Scheme.ProjectiveSpaceSectionRing

/-!
# Pushforwards of the twisting sheaves of a projective bundle

Hartshorne, *Algebraic Geometry*, II, Proposition 7.11(a) (p. 162).

Let `X` be a Noetherian scheme, `E` a locally free `𝒪_X`-module of finite rank at least two,
`π : P(E) = Proj_X S(E) ⟶ X` the projective bundle and `𝒪(l)` its twisting sheaves. Then
`S(E) ≅ ⊕_{l ∈ ℤ} π_* 𝒪(l)`, degreewise and compatibly with the products on the affine pieces:
for `l ≥ 0` the natural map
`S^l(E) ⟶ π_* 𝒪(l)`, which over an affine open `U` sends `s ∈ Γ(U, S^l(E)) = Γ(U, S(E))_l` to
the section `s / 1` of `𝒪_{Proj Γ(U, S(E))}(l)` on `π⁻¹(U) = Proj Γ(U, S(E))`, is an
isomorphism, and `π_* 𝒪(l) = 0` for `l < 0`. In particular `π_* 𝒪(0) ≅ 𝒪_X` and
`π_* 𝒪(1) ≅ E`.

## Main definitions and results

* `AlgebraicGeometry.Scheme.Modules.projectiveBundlePushforwardTwistHom`: the natural map
  `S^l(E) ⟶ π_* 𝒪(l)`, and `projectiveBundlePushforwardTwistHom_app_restrict`: over an affine
  open it is `s ↦ s / 1`.
* `AlgebraicGeometry.Scheme.Modules.projectiveBundlePushforwardTwistHom_mul`: compatibility with
  the products `S^a(E) × S^b(E) → S^{a+b}(E)` and `𝒪(a) ⊗ 𝒪(b) → 𝒪(a + b)` over each affine
  piece (from the general `Hartshorne.QuasiCoherentGradedAlgebra.pushforwardTwistHom_mul`).
* `AlgebraicGeometry.Scheme.Modules.isIso_projectiveBundlePushforwardTwistHom`,
  `projectiveBundlePushforwardTwistIso`: it is an isomorphism.
* `AlgebraicGeometry.Scheme.Modules.isZero_pushforward_projectiveBundleTwistingSheaf`:
  `π_* 𝒪(l) = 0` for `l < 0`.
* `AlgebraicGeometry.Scheme.Modules.projectiveBundlePushforwardTwistZeroIso`,
  `projectiveBundlePushforwardTwistOneIso`: `π_* 𝒪(0) ≅ 𝒪_X` and `π_* 𝒪(1) ≅ E`.

## Proof

The map is glued from the sections `s / 1` over the affine pieces
(`Hartshorne.QuasiCoherentGradedAlgebra.pushforwardTwistHom`). Whether it is an isomorphism, and
whether `π_* 𝒪(l)` vanishes, can be checked on the affine opens `U` on which `E` has a frame
`e_0, …, e_n`; these form a basis of the topology of `X`. There `Γ(U, S(E)) ≅ A[x_0, …, x_n]`,
`A = Γ(U, 𝒪_X)`, as graded rings, and the claims are the computation
`Γ_*(𝒪_{ℙⁿ_A}) = A[x_0, …, x_n]` of Proposition II.5.13 for `n ≥ 1`, transported along this
isomorphism.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne.QuasiCoherentGradedAlgebra

open AlgebraicGeometry ProjGradedModuleSheaf Ringed

variable {X : Scheme.{u}} {S : QuasiCoherentGradedAlgebra X}

/-- **Compatibility with multiplication on an affine piece**: if `u|_U = s|_U t|_U` in
`S(U)_{a+b}`, then on `Proj S(U)` the product of the sections attached to `s` and `t` under
`𝒪(a) ⊗ 𝒪(b) → 𝒪(a + b)` is the section attached to `u`, as checked on values at points. -/
theorem pushforwardTwistHom_mul {a b : ℕ} (Ma Mb Mc : S.relProj.Modules)
    (αa : ∀ U, Ma.restrict (S.projι U) ≅ S.twistingSheaf (a : ℤ) U)
    (αb : ∀ U, Mb.restrict (S.projι U) ≅ S.twistingSheaf (b : ℤ) U)
    (αc : ∀ U, Mc.restrict (S.projι U) ≅ S.twistingSheaf ((a + b : ℕ) : ℤ) U)
    {Fa Fb Fc : X.Modules} (τa : S.GradedSectionsMap a Fa) (τb : S.GradedSectionsMap b Fb)
    (τc : S.GradedSectionsMap (a + b) Fc) (hαa : TwistCompatible Ma αa)
    (hαb : TwistCompatible Mb αb) (hαc : TwistCompatible Mc αc) {V : X.Opens}
    (U : X.AffineZariskiSite) (hUV : U.1 ≤ V) (s : Γ(Fa, V)) (t : Γ(Fb, V)) (u : Γ(Fc, V))
    (hmul : (τc.toFun U (Fc.presheaf.map (homOfLE hUV).op u) : S.obj.obj (op U)) =
      τa.toFun U (Fa.presheaf.map (homOfLE hUV).op s) *
        τb.toFun U (Fb.presheaf.map (homOfLE hUV).op t))
    (x : Proj (S.grading U)) :
    (globalValue _ _ ((twistMulHom _ (a : ℤ) (b : ℤ)).val.app (op ⊤)
        (tmulSection _ _
          ((αa U).hom.app ⊤ (Ma.presheaf.map (homOfLE (S.projι_image_top_le ⟨U, hUV⟩)).op
            ((pushforwardTwistHom Ma αa τa hαa).app V s)))
          ((αb U).hom.app ⊤ (Mb.presheaf.map (homOfLE (S.projι_image_top_le ⟨U, hUV⟩)).op
            ((pushforwardTwistHom Mb αb τb hαb).app V t))))) x).val =
      (globalValue _ _ ((αc U).hom.app ⊤ (Mc.presheaf.map
        (homOfLE (S.projι_image_top_le ⟨U, hUV⟩)).op
          ((pushforwardTwistHom Mc αc τc hαc).app V u))) x).val := by
  rw [pushforwardTwistHom_app_restrict, pushforwardTwistHom_app_restrict,
    pushforwardTwistHom_app_restrict]
  refine (GradedGlobalSections.twistMulHom_tmul_twistSection_apply (a : ℤ) b _ (U := op ⊤) _
    ⟨x, trivial⟩).trans ?_
  change _ • LocalizedModule.mk _ 1 = LocalizedModule.mk _ 1
  rw [LocalizedModule.smul'_mk, smul_eq_mul, hmul, mul_comm]

end Hartshorne.QuasiCoherentGradedAlgebra

namespace AlgebraicGeometry.Scheme.Modules

open Hartshorne Hartshorne.SheafAlgebraOperations Hartshorne.ModuleSheafAlgebra
  Hartshorne.QuasiCoherentGradedAlgebra

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {E : X.Modules} (hE : E.IsLocallyFree)
  (hfin : ∀ x, E.rankAt x < Cardinal.aleph0)

/-- The degree-`l` sections `Γ(U, S^l(E)) → Γ(U, S(E))_l` over the affine opens `U`. -/
def symmetricPowerGradedSectionsMap (l : ℕ) :
    (symmetricGradedAlgebra hE hfin).GradedSectionsMap l (E.symmetricPower l) where
  toFun U :=
    { toFun a := ⟨(show E.symSections U.1 from
        (moduleSheafSymmetricAlgebraι (R := X.sheaf) l E).val.app (op U.1) a),
        E.mem_symmetricGrading.2 ⟨a, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' a b := Subtype.ext (map_add _ a b) }
  map_smul U r a := by
    change toSectionsRing E.symmetricAlgebraStructure_isCommutative
      ((moduleSheafSymmetricAlgebraι (R := X.sheaf) l E).val.app (op U.1) (r • a)) =
      unitRingHom E.symmetricAlgebraStructure_isCommutative U.1 r *
        toSectionsRing E.symmetricAlgebraStructure_isCommutative
          ((moduleSheafSymmetricAlgebraι (R := X.sheaf) l E).val.app (op U.1) a)
    rw [unitRingHom_mul, _root_.map_smul]
  map_restrict f a :=
    PresheafOfModules.naturality_apply (moduleSheafSymmetricAlgebraι (R := X.sheaf) l E).val
      ((Scheme.AffineZariskiSite.toOpensFunctor X).map f).op a

/-- Over an affine open `U`, `Γ(U, S^l(E)) → Γ(U, S(E))_l` is bijective. -/
theorem symmetricPowerGradedSectionsMap_bijective (l : ℕ) (U : X.AffineZariskiSite) :
    Function.Bijective ((symmetricPowerGradedSectionsMap hE hfin l).toFun U) := by
  have hG := moduleSheafSymmetricAlgebraPresheaf_isGraded (R := X.sheaf) E
  refine ⟨fun a b hab => ?_, fun ⟨y, hy⟩ => ?_⟩
  · have h := congrArg (fun z : (symmetricGradedAlgebra hE hfin).grading U l =>
      (hG.sheafProj l).val.app (op U.1)
        (ofSectionsRing E.symmetricAlgebraStructure_isCommutative
          (show E.symSections U.1 from z.1))) hab
    have ha := hG.sheafProj_ι_self l (op U.1) a
    have hb := hG.sheafProj_ι_self l (op U.1) b
    change (hG.sheafProj l).val.app (op U.1) ((moduleSheafSymmetricAlgebraι (R := X.sheaf) l
      E).val.app (op U.1) a) = a at ha
    change (hG.sheafProj l).val.app (op U.1) ((moduleSheafSymmetricAlgebraι (R := X.sheaf) l
      E).val.app (op U.1) b) = b at hb
    rw [← ha, ← hb]
    exact h
  · obtain ⟨a, ha⟩ := E.mem_symmetricGrading.1 hy
    exact ⟨a, Subtype.ext ha⟩

/-- On an affine open with a frame of rank at least two, `s ↦ s / 1` is a bijection
`Γ(U, S(E))_l → Γ(Proj Γ(U, S(E)), 𝒪(l))`. -/
theorem twistSection_top_bijective_of_isLocalFrame {U : X.AffineZariskiSite} {n : ℕ} (hn : 0 < n)
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, U.1)} (he : Ringed.IsLocalFrame (R := X.sheaf) E U.1 e)
    (l : ℕ) :
    Function.Bijective fun a : (symmetricGradedAlgebra hE hfin).grading U l =>
      GradedGlobalSections.twistSection l a (op ⊤) :=
  ProjTwistMap.twistSection_top_bijective_of_bijective (frameGradedHom hE hfin U.2 e)
    (frameGradedHom_bijective hE hfin U.2 he) l
    (ProjectiveSpaceSectionRing.twistSection_top_bijective hn l)

/-- On an affine open with a frame of rank at least two, `𝒪(l)`, `l < 0`, has no nonzero global
sections on `Proj Γ(U, S(E))`. -/
theorem twist_global_eq_zero_of_isLocalFrame {U : X.AffineZariskiSite} {n : ℕ} (hn : 0 < n)
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, U.1)} (he : Ringed.IsLocalFrame (R := X.sheaf) E U.1 e)
    {l : ℤ} (hl : l < 0) (g : Γ((symmetricGradedAlgebra hE hfin).twistingSheaf l U, ⊤)) :
    g = 0 :=
  ProjTwistMap.eq_zero_of_bijective (frameGradedHom hE hfin U.2 e)
    (frameGradedHom_bijective hE hfin U.2 he) l
    (fun g => ProjectiveSpaceSectionRing.projTwistingSheaf_global_eq_zero hn hl g) g

include hE hfin in
/-- If `E` has rank at least two everywhere, the affine opens on which `E` has a frame form a
basis of the topology of `X`. -/
theorem exists_affine_isLocalFrame_of_two_le_rankAt (hrank : ∀ x, 2 ≤ E.rankAt x) (x : X)
    (W : X.Opens) (hx : x ∈ W) :
    ∃ U : X.AffineZariskiSite, x ∈ U.1 ∧ U.1 ≤ W ∧ ∃ (n : ℕ) (_ : 0 < n)
      (e : ULift.{u} (Fin (n + 1)) → Γ(E, U.1)), Ringed.IsLocalFrame (R := X.sheaf) E U.1 e := by
  have hfl := (isFiniteLocallyFree_iff E).2 ⟨hE, hfin⟩
  obtain ⟨W', hxW', r, ⟨α⟩⟩ := hfl x
  have hr : E.rankAt x = r := by
    rw [rankAt_eq_ringed, Ringed.rankAt_eq E α hxW']
    simp
  have h2 : 2 ≤ r := by
    have := hrank x
    rw [hr] at this
    exact_mod_cast this
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have he := Ringed.isLocalFrame_of_over_iso (R := X.sheaf) α
  obtain ⟨V, hV, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ W ⊓ W' from ⟨hx, hxW'⟩)
  exact ⟨⟨V, hV⟩, hxV, hVle.trans inf_le_left, n, by omega, _,
    he.restrictLE (hVle.trans inf_le_right)⟩

variable [IsNoetherian X]

/-- **The natural map `S^l(E) ⟶ π_* 𝒪_{P(E)}(l)`**: a section `s` of `S^l(E)` over an open
`V ⊆ X` goes to the section of `𝒪(l)` over `π⁻¹(V)` which on `π⁻¹(U) = Proj Γ(U, S(E))`, for
every affine open `U ⊆ V`, is `s|_U / 1`. -/
def projectiveBundlePushforwardTwistHom (l : ℕ) :
    E.symmetricPower l ⟶ (Scheme.Modules.pushforward (projectiveBundleProj hE hfin)).obj
      (projectiveBundleTwistingSheaf hE hfin l) :=
  pushforwardTwistHom ((symmetricGradedAlgebra hE hfin).relTwistingSheaf (l : ℤ))
    ((symmetricGradedAlgebra hE hfin).relTwistingSheafRestrictIso (l : ℤ))
    (symmetricPowerGradedSectionsMap hE hfin l)
    (twistCompatible_relTwistingSheaf (symmetricGradedAlgebra hE hfin) l)

/-- **The natural map is induced by the degree-`l` sections**: for an affine open `U ⊆ V` and a
section `s` of `S^l(E)` over `V`, the section of `𝒪(l)` attached to `s`, restricted to
`π⁻¹(U) = Proj Γ(U, S(E))`, is `s|_U / 1`, where `s|_U ∈ Γ(U, S^l(E)) = Γ(U, S(E))_l`. -/
theorem projectiveBundlePushforwardTwistHom_app_restrict (l : ℕ) {V : X.Opens}
    (U : X.AffineZariskiSite) (hUV : U.1 ≤ V) (s : Γ(E.symmetricPower l, V)) :
    ((symmetricGradedAlgebra hE hfin).relTwistingSheafRestrictIso (l : ℤ) U).hom.app ⊤
        ((projectiveBundleTwistingSheaf hE hfin l).presheaf.map
          (homOfLE ((symmetricGradedAlgebra hE hfin).projι_image_top_le ⟨U, hUV⟩)).op
          ((projectiveBundlePushforwardTwistHom hE hfin l).app V s)) =
      GradedGlobalSections.twistSection l
        ((symmetricPowerGradedSectionsMap hE hfin l).toFun U
          ((E.symmetricPower l).presheaf.map (homOfLE hUV).op s)) (op ⊤) :=
  pushforwardTwistHom_app_restrict _ _ (symmetricPowerGradedSectionsMap hE hfin l)
    (twistCompatible_relTwistingSheaf (symmetricGradedAlgebra hE hfin) l) U hUV s

-- The kernel check of the instantiation of `pushforwardTwistHom_mul` unfolds the projective
-- bundle to the relative `Proj` of `S(E)` and exceeds the default limit.
set_option maxHeartbeats 1000000 in
open ProjGradedModuleSheaf Ringed in
/-- **Compatibility with multiplication**: over an affine open `U ⊆ V`, the natural maps are
compatible with the products `S^a(E) × S^b(E) → S^{a+b}(E)` (here `u = s t`, as sections of the
sheaf of algebras `S(E)`) and `𝒪(a) ⊗ 𝒪(b) → 𝒪(a + b)` on `π⁻¹(U) = Proj Γ(U, S(E))`. Equality
is checked on the values at every point, which lie in the same localization of `Γ(U, S(E))` for
all twists. -/
theorem projectiveBundlePushforwardTwistHom_mul (a b : ℕ) {V : X.Opens} (U : X.AffineZariskiSite)
    (hUV : U.1 ≤ V) (s : Γ(E.symmetricPower a, V)) (t : Γ(E.symmetricPower b, V))
    (u : Γ(E.symmetricPower (a + b), V))
    (hu : (show E.symSections V from
        (moduleSheafSymmetricAlgebraι (R := X.sheaf) (a + b) E).val.app (op V) u) =
      (show E.symSections V from
        (moduleSheafSymmetricAlgebraι (R := X.sheaf) a E).val.app (op V) s) *
        (show E.symSections V from
          (moduleSheafSymmetricAlgebraι (R := X.sheaf) b E).val.app (op V) t))
    (x : Proj ((symmetricGradedAlgebra hE hfin).grading U)) :
    (globalValue _ _ ((twistMulHom _ (a : ℤ) (b : ℤ)).val.app (op ⊤)
        (tmulSection _ _
          (((symmetricGradedAlgebra hE hfin).relTwistingSheafRestrictIso (a : ℤ) U).hom.app ⊤
            ((projectiveBundleTwistingSheaf hE hfin a).presheaf.map
              (homOfLE ((symmetricGradedAlgebra hE hfin).projι_image_top_le ⟨U, hUV⟩)).op
              ((projectiveBundlePushforwardTwistHom hE hfin a).app V s)))
          (((symmetricGradedAlgebra hE hfin).relTwistingSheafRestrictIso (b : ℤ) U).hom.app ⊤
            ((projectiveBundleTwistingSheaf hE hfin b).presheaf.map
              (homOfLE ((symmetricGradedAlgebra hE hfin).projι_image_top_le ⟨U, hUV⟩)).op
              ((projectiveBundlePushforwardTwistHom hE hfin b).app V t))))) x).val =
      (globalValue _ _
        (((symmetricGradedAlgebra hE hfin).relTwistingSheafRestrictIso ((a + b : ℕ) : ℤ) U).hom.app
          ⊤ ((projectiveBundleTwistingSheaf hE hfin ((a + b : ℕ) : ℤ)).presheaf.map
            (homOfLE ((symmetricGradedAlgebra hE hfin).projι_image_top_le ⟨U, hUV⟩)).op
            ((projectiveBundlePushforwardTwistHom hE hfin (a + b)).app V u))) x).val := by
  have key : ∀ (l : ℕ) (y : Γ(E.symmetricPower l, V)),
      (show E.symSections U.1 from ((symmetricPowerGradedSectionsMap hE hfin l).toFun U
        ((E.symmetricPower l).presheaf.map (homOfLE hUV).op y)).1) =
      sectionsRestrict E.symmetricAlgebraStructure_isCommutative (homOfLE hUV)
        (show E.symSections V from (moduleSheafSymmetricAlgebraι (R := X.sheaf) l E).val.app
          (op V) y) := fun l y =>
    PresheafOfModules.naturality_apply (moduleSheafSymmetricAlgebraι (R := X.sheaf) l E).val
      (homOfLE hUV).op y
  refine pushforwardTwistHom_mul _ _ _ _ _ _ (symmetricPowerGradedSectionsMap hE hfin a)
    (symmetricPowerGradedSectionsMap hE hfin b) (symmetricPowerGradedSectionsMap hE hfin (a + b))
    (twistCompatible_relTwistingSheaf (symmetricGradedAlgebra hE hfin) a)
    (twistCompatible_relTwistingSheaf (symmetricGradedAlgebra hE hfin) b)
    (twistCompatible_relTwistingSheaf (symmetricGradedAlgebra hE hfin) (a + b)) U hUV s t u ?_ x
  change (show E.symSections U.1 from
      ((symmetricPowerGradedSectionsMap hE hfin (a + b)).toFun U _).1) =
    (show E.symSections U.1 from ((symmetricPowerGradedSectionsMap hE hfin a).toFun U _).1) *
    (show E.symSections U.1 from ((symmetricPowerGradedSectionsMap hE hfin b).toFun U _).1)
  rw [key, key, key, hu, map_mul]

/-- **Hartshorne II, Proposition 7.11(a), in nonnegative degrees**: if `E` has rank at least two,
the natural map `S^l(E) ⟶ π_* 𝒪_{P(E)}(l)` is an isomorphism for every `l ≥ 0`. -/
theorem isIso_projectiveBundlePushforwardTwistHom (hrank : ∀ x, 2 ≤ E.rankAt x) (l : ℕ) :
    IsIso (projectiveBundlePushforwardTwistHom hE hfin l) := by
  refine isIso_of_forall_exists_bijective _ fun x W hx => ?_
  obtain ⟨U, hxU, hUW, n, hn, e, he⟩ :=
    exists_affine_isLocalFrame_of_two_le_rankAt hE hfin hrank x W hx
  exact ⟨U.1, hxU, hUW, pushforwardTwistHom_app_bijective _ _
    (symmetricPowerGradedSectionsMap hE hfin l)
    (twistCompatible_relTwistingSheaf (symmetricGradedAlgebra hE hfin) l) U
    (symmetricPowerGradedSectionsMap_bijective hE hfin l U)
    (twistSection_top_bijective_of_isLocalFrame hE hfin hn he l)⟩

/-- **Hartshorne II, Proposition 7.11(a), in nonnegative degrees**:
`S^l(E) ≅ π_* 𝒪_{P(E)}(l)` for `l ≥ 0`, by the natural map. -/
def projectiveBundlePushforwardTwistIso (hrank : ∀ x, 2 ≤ E.rankAt x) (l : ℕ) :
    E.symmetricPower l ≅ (Scheme.Modules.pushforward (projectiveBundleProj hE hfin)).obj
      (projectiveBundleTwistingSheaf hE hfin l) :=
  haveI := isIso_projectiveBundlePushforwardTwistHom hE hfin hrank l
  asIso (projectiveBundlePushforwardTwistHom hE hfin l)

/-- **Hartshorne II, Proposition 7.11(a), in negative degrees**: if `E` has rank at least two,
`π_* 𝒪_{P(E)}(l) = 0` for `l < 0`. -/
theorem isZero_pushforward_projectiveBundleTwistingSheaf (hrank : ∀ x, 2 ≤ E.rankAt x) {l : ℤ}
    (hl : l < 0) :
    IsZero ((Scheme.Modules.pushforward (projectiveBundleProj hE hfin)).obj
      (projectiveBundleTwistingSheaf hE hfin l)) :=
  isZero_pushforward_of_twist_eq_zero _
    ((symmetricGradedAlgebra hE hfin).relTwistingSheafRestrictIso l)
    fun x W hx => by
      obtain ⟨U, hxU, hUW, n, hn, e, he⟩ :=
        exists_affine_isLocalFrame_of_two_le_rankAt hE hfin hrank x W hx
      exact ⟨U, hxU, hUW, ⟨fun a b =>
        (twist_global_eq_zero_of_isLocalFrame hE hfin hn he hl a).trans
        (twist_global_eq_zero_of_isLocalFrame hE hfin hn he hl b).symm⟩⟩

/-- **`π_* 𝒪_{P(E)} = 𝒪_X`** (Hartshorne II, Proposition 7.11(a)): `π_* 𝒪(0) ≅ 𝒪_X` if `E` has
rank at least two. -/
def projectiveBundlePushforwardTwistZeroIso (hrank : ∀ x, 2 ≤ E.rankAt x) :
    (Scheme.Modules.pushforward (projectiveBundleProj hE hfin)).obj
      (projectiveBundleTwistingSheaf hE hfin 0) ≅ SheafOfModules.unit X.ringCatSheaf :=
  (projectiveBundlePushforwardTwistIso hE hfin hrank 0).symm ≪≫ E.symmetricPowerZeroIso

/-- **`π_* 𝒪_{P(E)}(1) = E`** (Hartshorne II, Proposition 7.11(a)): `π_* 𝒪(1) ≅ E` if `E` has
rank at least two. -/
def projectiveBundlePushforwardTwistOneIso (hrank : ∀ x, 2 ≤ E.rankAt x) :
    (Scheme.Modules.pushforward (projectiveBundleProj hE hfin)).obj
      (projectiveBundleTwistingSheaf hE hfin 1) ≅ E :=
  (projectiveBundlePushforwardTwistIso hE hfin hrank 1).symm ≪≫ E.symmetricPowerOneIso

end AlgebraicGeometry.Scheme.Modules
